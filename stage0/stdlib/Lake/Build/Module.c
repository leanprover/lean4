// Lean compiler output
// Module: Lake.Build.Module
// Imports: Lake.Util.OrdHashSet Lake.Util.List Lean.Elab.ParseImportsFast Lake.Build.Common Lake.Build.Target
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
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_MTime_instOrd;
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Module_transImportsFacetConfig___closed__1;
static lean_object* l_Lake_Module_coFacetConfig___closed__4;
lean_object* l_Lake_Module_bcFile_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recParseImports___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__5(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__4;
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__2;
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_cFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fetchExternLibs___closed__1;
static lean_object* l_Lake_initModuleFacetConfigs___closed__2;
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__2;
extern lean_object* l_Lake_instOrdBuildType;
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__13;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__2;
uint64_t l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(lean_object*, size_t, size_t, uint64_t);
static uint8_t l_Lake_Module_clearOutputHashes___closed__3;
lean_object* l_Lake_instBEqModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__5;
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recParseImports___spec__5___at_Lake_Module_recParseImports___spec__6(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recParseImports___lambda__4___closed__2;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_oExportFacetConfig___closed__4;
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__4;
static lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcoFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig___elambda__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_bcFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_clearOutputHashes___closed__2;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
static lean_object* l_Lake_Module_depsFacetConfig___closed__5;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig;
static lean_object* l_Lake_Module_ileanFacetConfig___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_initModuleFacetConfigs___closed__10;
static lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Ord_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__2;
lean_object* l_Lake_buildUnlessUpToDate_x3f_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig___elambda__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recParseImports___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_fetchExternLibs___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_dynlibFacetConfig___elambda__1___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2___closed__3___boxed__const__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Module_recParseImports___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Module_recParseImports___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_fetchFileTrace(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recComputeTransImports___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_BuildType_leanArgs___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_bcFacetConfig___closed__3;
static lean_object* l_Lake_collectImportsAux___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__7;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Module_bcoFacetConfig___closed__4;
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_Lake_Module_oFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__5;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_Lake_TargetArray_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_ileanFacetConfig___closed__1;
static lean_object* l_Lake_Module_recBuildDeps___lambda__2___closed__2;
static lean_object* l_Lake_Module_coExportFacetConfig___closed__5;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2(lean_object*);
static lean_object* l_Lake_collectImportsAux___closed__4;
extern lean_object* l_Lake_sharedLibExt;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_clearOutputHashes(lean_object*, lean_object*);
lean_object* l_Lake_nullFormat___rarg(uint8_t, lean_object*);
lean_object* l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint64_t l_Lake_platformTrace;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__8(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectImportsAux___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchExternLibs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashableModule___boxed(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lake_Module_getMTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__3;
static lean_object* l_Lake_collectImportsAux___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___boxed(lean_object**);
static lean_object* l_Lake_collectImportsAux___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Module_checkExists(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__7(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oleanFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cacheOutputHashes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__12;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mixArray___rarg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lake_Module_coExportFacetConfig;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig;
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_initModuleFacetConfigs;
static lean_object* l_Lake_Module_coExportFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_Module_bcoFacetConfig___closed__3;
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig;
static lean_object* l_Lake_Module_bcFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1___boxed(lean_object*);
lean_object* l_Lake_withRegisterJob___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__1;
static lean_object* l_Lake_Module_oExportFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_coExportFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__16;
static lean_object* l_Lake_Module_precompileImportsFacetConfig___closed__3;
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig___elambda__1(uint8_t, lean_object*);
lean_object* l_Lake_EquipT_map___at_Lake_instMonadStateOfLogJobM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recParseImports___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recBuildDeps___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recParseImports___lambda__2___closed__1;
static lean_object* l_Lake_Module_ileanFacetConfig___closed__3;
static lean_object* l_Lake_Module_ileanFacetConfig___closed__4;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcoFacetConfig___elambda__1(uint8_t, lean_object*);
lean_object* l_Lake_Job_mapM___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLean___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_dynlibFacetConfig___elambda__1___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig;
static lean_object* l_Lake_Module_bcFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__3(lean_object*, lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recBuildDeps___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_computePrecompileImportsAux___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanBcToO___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recBuildDeps___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_cacheFileHash(lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_oFacetConfig___closed__1;
extern lean_object* l_Task_Priority_default;
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_cFacetConfig___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__1;
static lean_object* l_Lake_Module_oleanFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFacetConfig;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Ord_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coExportFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__17;
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2___boxed(lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__5;
static lean_object* l_Lake_Module_cFacetConfig___closed__1;
extern lean_object* l_Lake_BuildTrace_nil;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate_x27___spec__5(lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_fetchExternLibs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__2;
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__2;
static lean_object* l_Lake_Module_recBuildDeps___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oFacetConfig___closed__2;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_bcoFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_fetchExternLibs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___lambda__4___closed__2;
lean_object* l_Lake_Job_collectArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recComputeTransImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__2;
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Module_recParseImports___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recParseImports___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_collectImportsAux___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recBuildDeps___spec__8___at_Lake_Module_recBuildDeps___spec__9(lean_object*, lean_object*);
static lean_object* l_Lake_Module_transImportsFacetConfig___closed__3;
static lean_object* l_Lake_Module_coExportFacetConfig___closed__1;
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recComputePrecompileImports___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recParseImports___closed__1;
static lean_object* l_Lake_Module_depsFacetConfig___closed__4;
static lean_object* l_Lake_Module_recBuildDynlib___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lake_recBuildExternDynlibs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFacetConfig___elambda__1(uint8_t, lean_object*);
lean_object* l_Lake_Job_bindM___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recBuildExternDynlibs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__6;
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig___elambda__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___boxed__const__1;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
lean_object* l_Lake_BuildType_leanArgs(uint8_t);
static lean_object* l_Lake_Module_cFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(lean_object*);
static lean_object* l_Lake_Module_clearOutputHashes___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4___closed__2;
static lean_object* l_Lake_initModuleFacetConfigs___closed__14;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__1;
static lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__1;
static lean_object* l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__4;
static lean_object* l_Lake_Module_recBuildDynlib___lambda__4___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_Module_coExportFacetConfig___closed__6;
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___closed__1;
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
static lean_object* l_Lake_Module_oleanFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToONoExport___closed__1;
uint8_t l_Lake_Backend_orPreferLeft(uint8_t, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_recBuildExternDynlibs___closed__1;
static lean_object* l_Lake_initModuleFacetConfigs___closed__11;
static lean_object* l_Lake_Module_bcoFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig___elambda__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___lambda__7___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coExportFacetConfig___elambda__1(uint8_t, lean_object*);
lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computePrecompileImportsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__3;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coFacetConfig___closed__2;
lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashablePackage___boxed(lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___lambda__7___closed__2;
static lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___lambda__1___boxed(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__6(lean_object*, lean_object*, lean_object*, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
static lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__1;
static lean_object* l_Lake_Module_recParseImports___lambda__4___closed__1;
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_importsFacetConfig___elambda__1___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanPath___boxed(lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
static lean_object* l_Lake_collectImportsAux___closed__5;
static lean_object* l_Lake_Module_transImportsFacetConfig___closed__2;
static lean_object* l_Lake_Module_precompileImportsFacetConfig___closed__1;
static lean_object* l_Lake_Module_coFacetConfig___closed__1;
lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_importsFacetConfig___elambda__1___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___lambda__7___closed__3;
static lean_object* l_Lake_Module_clearOutputHashes___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__3;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig;
uint8_t lean_internal_has_llvm_backend(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_collectImportsAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__4;
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_fetchExternLibs___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3(lean_object*, size_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instBEqPackage___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Module_coFacetConfig___closed__3;
static lean_object* l_Lake_Module_precompileImportsFacetConfig___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l_Lake_Module_oExportFacetConfig___closed__3;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recComputePrecompileImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__1;
lean_object* lean_name_mangle(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig___elambda__1(uint8_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_Module_depsFacetConfig___closed__2;
static lean_object* l_Lake_initModuleFacetConfigs___closed__9;
static lean_object* l_Lake_Module_recBuildDeps___lambda__2___closed__3;
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_BuildType_leancArgs(uint8_t);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchExternLibs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1___boxed(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_computePrecompileImportsAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__3;
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__3;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__4;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__15;
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_clearFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectImportsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___lambda__7___closed__4;
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig___elambda__1(uint8_t, lean_object*);
static lean_object* l_Lake_Module_coExportFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig;
static lean_object* l_Lake_Module_bcoFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1(x_1, x_2, x_4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
x_10 = lean_array_push(x_8, x_9);
x_2 = x_10;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_16, 0, x_13);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = lean_apply_6(x_4, x_16, x_5, x_6, x_7, x_8, x_9);
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
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_15, x_2, x_20);
x_2 = x_23;
x_3 = x_24;
x_8 = x_21;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; 
x_16 = lean_array_uget(x_3, x_5);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 8);
lean_inc(x_21);
x_22 = l_System_FilePath_join(x_19, x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 10);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_System_FilePath_join(x_22, x_23);
lean_dec(x_23);
x_25 = lean_array_push(x_18, x_24);
x_26 = lean_ctor_get(x_16, 10);
lean_inc(x_26);
x_27 = 0;
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_29 = l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1(x_16, x_28, x_26);
lean_dec(x_26);
x_30 = lean_array_size(x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2(x_30, x_27, x_29, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Array_append___rarg(x_17, x_34);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
x_38 = 1;
x_39 = lean_usize_add(x_5, x_38);
x_5 = x_39;
x_6 = x_37;
x_11 = x_35;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_31, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_31, 0, x_46);
return x_31;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_dec(x_31);
x_48 = lean_ctor_get(x_32, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_50 = x_32;
} else {
 lean_dec_ref(x_32);
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
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
return x_31;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_31);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
static lean_object* _init_l_Lake_recBuildExternDynlibs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recBuildExternDynlibs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Lake_recBuildExternDynlibs___closed__1;
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3(x_1, x_8, x_1, x_9, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_13, 0, x_22);
return x_12;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_26 = x_14;
} else {
 lean_dec_ref(x_14);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
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
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_34 = x_14;
} else {
 lean_dec_ref(x_14);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
if (lean_is_scalar(x_31)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_31;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_12, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_12, 0, x_43);
return x_12;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_dec(x_12);
x_45 = lean_ctor_get(x_13, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_47 = x_13;
} else {
 lean_dec_ref(x_13);
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
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
return x_12;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_12, 0);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_12);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_recBuildExternDynlibs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recBuildExternDynlibs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recParseImports___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recParseImports___spec__5___at_Lake_Module_recParseImports___spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recParseImports___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recParseImports___spec__5___at_Lake_Module_recParseImports___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recParseImports___spec__3(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recParseImports___spec__4(x_7, x_1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashableModule___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqModule___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__2(x_2, x_21);
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
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recParseImports___spec__3(x_29);
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
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__2(x_2, x_55);
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
x_70 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recParseImports___spec__3(x_63);
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
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_apply_1(x_2, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_apply_1(x_2, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_23 = x_10;
} else {
 lean_dec_ref(x_10);
 x_23 = lean_box(0);
}
x_24 = lean_apply_1(x_2, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_9, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_9, 0, x_32);
return x_9;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_dec(x_9);
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_36 = x_10;
} else {
 lean_dec_ref(x_10);
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
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Functor_mapRev___at_Lake_Module_recParseImports___spec__7___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_11);
lean_dec(x_5);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_12);
lean_inc(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1(x_1, x_3);
return x_4;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_instMonadStateOfLogJobM___spec__1___rarg), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_Workspace_findModule_x3f___boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__3;
x_16 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_instMonadStateOfLogJobM___spec__1___rarg), 8, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__3), 2, 1);
lean_closure_set(x_17, 0, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Functor_mapRev___at_Lake_Module_recParseImports___spec__7___rarg(x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_21;
x_9 = x_22;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_18, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_35 = x_19;
} else {
 lean_dec_ref(x_19);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_9);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Module_recParseImports___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
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
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdout(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdout(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
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
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Module_recParseImports___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
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
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdin(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdin(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
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
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Module_recParseImports___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
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
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stderr(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stderr(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__1() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__3;
x_3 = lean_unsigned_to_nat(100u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__1;
x_13 = lean_st_mk_ref(x_12, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_12, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_IO_FS_Stream_ofBuffer(x_14);
lean_inc(x_17);
x_20 = l_IO_FS_Stream_ofBuffer(x_17);
if (x_2 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Module_recParseImports___spec__10), 8, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_1);
x_22 = l_IO_withStdin___at_Lake_Module_recParseImports___spec__11(x_19, x_21, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_string_validate_utf8(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
x_37 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
x_38 = l_panic___at_String_fromUTF8_x21___spec__1(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_23, 0, x_39);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_string_from_utf8_unchecked(x_35);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_27);
lean_ctor_set(x_23, 0, x_41);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_string_validate_utf8(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_44);
x_46 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
x_47 = l_panic___at_String_fromUTF8_x21___spec__1(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_27);
lean_ctor_set(x_23, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_string_from_utf8_unchecked(x_44);
lean_dec(x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_27);
lean_ctor_set(x_23, 0, x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_free_object(x_24);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_23);
lean_dec(x_27);
x_53 = !lean_is_exclusive(x_32);
if (x_53 == 0)
{
return x_32;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_32, 0);
x_55 = lean_ctor_get(x_32, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_32);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_24, 0);
x_58 = lean_ctor_get_uint8(x_24, sizeof(void*)*2);
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
lean_inc(x_57);
lean_dec(x_24);
x_60 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
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
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_58);
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_string_validate_utf8(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_67 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
x_68 = l_panic___at_String_fromUTF8_x21___spec__1(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_27);
lean_ctor_set(x_23, 1, x_64);
lean_ctor_set(x_23, 0, x_69);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_23);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_string_from_utf8_unchecked(x_65);
lean_dec(x_65);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_27);
lean_ctor_set(x_23, 1, x_64);
lean_ctor_set(x_23, 0, x_72);
if (lean_is_scalar(x_63)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_63;
}
lean_ctor_set(x_73, 0, x_23);
lean_ctor_set(x_73, 1, x_62);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_59);
lean_dec(x_57);
lean_free_object(x_23);
lean_dec(x_27);
x_74 = lean_ctor_get(x_60, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_76 = x_60;
} else {
 lean_dec_ref(x_60);
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
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_23, 0);
lean_inc(x_78);
lean_dec(x_23);
x_79 = lean_ctor_get(x_24, 0);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_24, sizeof(void*)*2);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_82 = x_24;
} else {
 lean_dec_ref(x_24);
 x_82 = lean_box(0);
}
x_83 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 1);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_80);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_string_validate_utf8(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_88);
x_90 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
x_91 = l_panic___at_String_fromUTF8_x21___spec__1(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_78);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_87);
if (lean_is_scalar(x_86)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_86;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_85);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_string_from_utf8_unchecked(x_88);
lean_dec(x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_78);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_87);
if (lean_is_scalar(x_86)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_86;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_85);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
x_99 = lean_ctor_get(x_83, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_83, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_101 = x_83;
} else {
 lean_dec_ref(x_83);
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
}
else
{
uint8_t x_103; 
lean_dec(x_17);
x_103 = !lean_is_exclusive(x_22);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_22, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_23);
if (x_105 == 0)
{
return x_22;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_23, 0);
x_107 = lean_ctor_get(x_23, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_23);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_22, 0, x_108);
return x_22;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_22, 1);
lean_inc(x_109);
lean_dec(x_22);
x_110 = lean_ctor_get(x_23, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_23, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_112 = x_23;
} else {
 lean_dec_ref(x_23);
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
uint8_t x_115; 
lean_dec(x_17);
x_115 = !lean_is_exclusive(x_22);
if (x_115 == 0)
{
return x_22;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_22, 0);
x_117 = lean_ctor_get(x_22, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_22);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_inc(x_20);
x_119 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Module_recParseImports___spec__12), 8, 2);
lean_closure_set(x_119, 0, x_20);
lean_closure_set(x_119, 1, x_1);
x_120 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Module_recParseImports___spec__10), 8, 2);
lean_closure_set(x_120, 0, x_20);
lean_closure_set(x_120, 1, x_119);
x_121 = l_IO_withStdin___at_Lake_Module_recParseImports___spec__11(x_19, x_120, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = !lean_is_exclusive(x_122);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_dec(x_127);
x_128 = !lean_is_exclusive(x_123);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_123, 0);
x_130 = lean_ctor_get(x_123, 1);
x_131 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_string_validate_utf8(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_134);
x_136 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
x_137 = l_panic___at_String_fromUTF8_x21___spec__1(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_126);
lean_ctor_set(x_122, 0, x_138);
lean_ctor_set(x_131, 0, x_122);
return x_131;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_string_from_utf8_unchecked(x_134);
lean_dec(x_134);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_126);
lean_ctor_set(x_122, 0, x_140);
lean_ctor_set(x_131, 0, x_122);
return x_131;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_131, 0);
x_142 = lean_ctor_get(x_131, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_131);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_string_validate_utf8(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_143);
x_145 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
x_146 = l_panic___at_String_fromUTF8_x21___spec__1(x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_126);
lean_ctor_set(x_122, 0, x_147);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_122);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_string_from_utf8_unchecked(x_143);
lean_dec(x_143);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_126);
lean_ctor_set(x_122, 0, x_150);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_122);
lean_ctor_set(x_151, 1, x_142);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_free_object(x_123);
lean_dec(x_130);
lean_dec(x_129);
lean_free_object(x_122);
lean_dec(x_126);
x_152 = !lean_is_exclusive(x_131);
if (x_152 == 0)
{
return x_131;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_131, 0);
x_154 = lean_ctor_get(x_131, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_131);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_123, 0);
x_157 = lean_ctor_get_uint8(x_123, sizeof(void*)*2);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
lean_inc(x_156);
lean_dec(x_123);
x_159 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
x_163 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_158);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_157);
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_string_validate_utf8(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_164);
x_166 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
x_167 = l_panic___at_String_fromUTF8_x21___spec__1(x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_126);
lean_ctor_set(x_122, 1, x_163);
lean_ctor_set(x_122, 0, x_168);
if (lean_is_scalar(x_162)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_162;
}
lean_ctor_set(x_169, 0, x_122);
lean_ctor_set(x_169, 1, x_161);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_string_from_utf8_unchecked(x_164);
lean_dec(x_164);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_126);
lean_ctor_set(x_122, 1, x_163);
lean_ctor_set(x_122, 0, x_171);
if (lean_is_scalar(x_162)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_162;
}
lean_ctor_set(x_172, 0, x_122);
lean_ctor_set(x_172, 1, x_161);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_158);
lean_dec(x_156);
lean_free_object(x_122);
lean_dec(x_126);
x_173 = lean_ctor_get(x_159, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_159, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_175 = x_159;
} else {
 lean_dec_ref(x_159);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_122, 0);
lean_inc(x_177);
lean_dec(x_122);
x_178 = lean_ctor_get(x_123, 0);
lean_inc(x_178);
x_179 = lean_ctor_get_uint8(x_123, sizeof(void*)*2);
x_180 = lean_ctor_get(x_123, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_181 = x_123;
} else {
 lean_dec_ref(x_123);
 x_181 = lean_box(0);
}
x_182 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 2, 1);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_178);
lean_ctor_set(x_186, 1, x_180);
lean_ctor_set_uint8(x_186, sizeof(void*)*2, x_179);
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_string_validate_utf8(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_187);
x_189 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
x_190 = l_panic___at_String_fromUTF8_x21___spec__1(x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_177);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_186);
if (lean_is_scalar(x_185)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_185;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_184);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_string_from_utf8_unchecked(x_187);
lean_dec(x_187);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_177);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_186);
if (lean_is_scalar(x_185)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_185;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_184);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_177);
x_198 = lean_ctor_get(x_182, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_182, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_200 = x_182;
} else {
 lean_dec_ref(x_182);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_17);
x_202 = !lean_is_exclusive(x_121);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_121, 0);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_122);
if (x_204 == 0)
{
return x_121;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_122, 0);
x_206 = lean_ctor_get(x_122, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_122);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_121, 0, x_207);
return x_121;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_121, 1);
lean_inc(x_208);
lean_dec(x_121);
x_209 = lean_ctor_get(x_122, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_122, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_211 = x_122;
} else {
 lean_dec_ref(x_122);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_208);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_17);
x_214 = !lean_is_exclusive(x_121);
if (x_214 == 0)
{
return x_121;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_121, 0);
x_216 = lean_ctor_get(x_121, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_121);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_14);
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_16);
if (x_218 == 0)
{
return x_16;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_16, 0);
x_220 = lean_ctor_get(x_16, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_16);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_13);
if (x_222 == 0)
{
return x_13;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_13, 0);
x_224 = lean_ctor_get(x_13, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_13);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_7, 0);
x_227 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_228 = lean_ctor_get(x_7, 1);
lean_inc(x_228);
lean_inc(x_226);
lean_dec(x_7);
x_229 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__1;
x_230 = lean_st_mk_ref(x_229, x_8);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_st_mk_ref(x_229, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_236, 0, x_226);
lean_ctor_set(x_236, 1, x_228);
lean_ctor_set_uint8(x_236, sizeof(void*)*2, x_227);
x_237 = l_IO_FS_Stream_ofBuffer(x_231);
lean_inc(x_234);
x_238 = l_IO_FS_Stream_ofBuffer(x_234);
if (x_2 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Module_recParseImports___spec__10), 8, 2);
lean_closure_set(x_239, 0, x_238);
lean_closure_set(x_239, 1, x_1);
x_240 = l_IO_withStdin___at_Lake_Module_recParseImports___spec__11(x_237, x_239, x_3, x_4, x_5, x_6, x_236, x_235);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_dec(x_240);
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_245 = x_241;
} else {
 lean_dec_ref(x_241);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_242, 0);
lean_inc(x_246);
x_247 = lean_ctor_get_uint8(x_242, sizeof(void*)*2);
x_248 = lean_ctor_get(x_242, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_249 = x_242;
} else {
 lean_dec_ref(x_242);
 x_249 = lean_box(0);
}
x_250 = lean_st_ref_get(x_234, x_243);
lean_dec(x_234);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_254 = lean_alloc_ctor(0, 2, 1);
} else {
 x_254 = x_249;
}
lean_ctor_set(x_254, 0, x_246);
lean_ctor_set(x_254, 1, x_248);
lean_ctor_set_uint8(x_254, sizeof(void*)*2, x_247);
x_255 = lean_ctor_get(x_251, 0);
lean_inc(x_255);
lean_dec(x_251);
x_256 = lean_string_validate_utf8(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_255);
x_257 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
x_258 = l_panic___at_String_fromUTF8_x21___spec__1(x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_244);
if (lean_is_scalar(x_245)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_245;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_254);
if (lean_is_scalar(x_253)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_253;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_252);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_string_from_utf8_unchecked(x_255);
lean_dec(x_255);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_244);
if (lean_is_scalar(x_245)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_245;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_254);
if (lean_is_scalar(x_253)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_253;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_252);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
x_266 = lean_ctor_get(x_250, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_250, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_268 = x_250;
} else {
 lean_dec_ref(x_250);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_234);
x_270 = lean_ctor_get(x_240, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_271 = x_240;
} else {
 lean_dec_ref(x_240);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_241, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_241, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_274 = x_241;
} else {
 lean_dec_ref(x_241);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
if (lean_is_scalar(x_271)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_271;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_270);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_234);
x_277 = lean_ctor_get(x_240, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_240, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_279 = x_240;
} else {
 lean_dec_ref(x_240);
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
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_inc(x_238);
x_281 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Module_recParseImports___spec__12), 8, 2);
lean_closure_set(x_281, 0, x_238);
lean_closure_set(x_281, 1, x_1);
x_282 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Module_recParseImports___spec__10), 8, 2);
lean_closure_set(x_282, 0, x_238);
lean_closure_set(x_282, 1, x_281);
x_283 = l_IO_withStdin___at_Lake_Module_recParseImports___spec__11(x_237, x_282, x_3, x_4, x_5, x_6, x_236, x_235);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_ctor_get(x_284, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_288 = x_284;
} else {
 lean_dec_ref(x_284);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
x_290 = lean_ctor_get_uint8(x_285, sizeof(void*)*2);
x_291 = lean_ctor_get(x_285, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_292 = x_285;
} else {
 lean_dec_ref(x_285);
 x_292 = lean_box(0);
}
x_293 = lean_st_ref_get(x_234, x_286);
lean_dec(x_234);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_297 = lean_alloc_ctor(0, 2, 1);
} else {
 x_297 = x_292;
}
lean_ctor_set(x_297, 0, x_289);
lean_ctor_set(x_297, 1, x_291);
lean_ctor_set_uint8(x_297, sizeof(void*)*2, x_290);
x_298 = lean_ctor_get(x_294, 0);
lean_inc(x_298);
lean_dec(x_294);
x_299 = lean_string_validate_utf8(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_298);
x_300 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5;
x_301 = l_panic___at_String_fromUTF8_x21___spec__1(x_300);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_287);
if (lean_is_scalar(x_288)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_288;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_297);
if (lean_is_scalar(x_296)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_296;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_295);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_string_from_utf8_unchecked(x_298);
lean_dec(x_298);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_287);
if (lean_is_scalar(x_288)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_288;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_297);
if (lean_is_scalar(x_296)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_296;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_295);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
x_309 = lean_ctor_get(x_293, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_293, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_311 = x_293;
} else {
 lean_dec_ref(x_293);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_234);
x_313 = lean_ctor_get(x_283, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_314 = x_283;
} else {
 lean_dec_ref(x_283);
 x_314 = lean_box(0);
}
x_315 = lean_ctor_get(x_284, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_284, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_317 = x_284;
} else {
 lean_dec_ref(x_284);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
if (lean_is_scalar(x_314)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_314;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_313);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_234);
x_320 = lean_ctor_get(x_283, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_283, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_322 = x_283;
} else {
 lean_dec_ref(x_283);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_231);
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_324 = lean_ctor_get(x_233, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_233, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_326 = x_233;
} else {
 lean_dec_ref(x_233);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_328 = lean_ctor_get(x_230, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_230, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_330 = x_230;
} else {
 lean_dec_ref(x_230);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_IO_FS_readFile(x_1, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_io_error_to_string(x_19);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_9);
x_24 = lean_array_push(x_9, x_22);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_io_error_to_string(x_26);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_array_get_size(x_9);
x_32 = lean_array_push(x_9, x_30);
lean_ctor_set(x_6, 0, x_32);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
}
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_35);
lean_dec(x_6);
x_38 = l_IO_FS_readFile(x_1, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_36);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_47 = x_38;
} else {
 lean_dec_ref(x_38);
 x_47 = lean_box(0);
}
x_48 = lean_io_error_to_string(x_45);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_get_size(x_35);
x_52 = lean_array_push(x_35, x_50);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_37);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_36);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
if (lean_is_scalar(x_47)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_47;
 lean_ctor_set_tag(x_55, 0);
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_46);
return x_55;
}
}
}
}
static lean_object* _init_l_Lake_Module_recParseImports___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_102; 
x_102 = !lean_is_exclusive(x_7);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_7, 0);
x_104 = l_Lean_parseImports_x27(x_2, x_1, x_8);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_104, 1);
lean_ctor_set(x_104, 1, x_7);
x_9 = x_104;
x_10 = x_106;
goto block_101;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_104, 0);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_104);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_7);
x_9 = x_109;
x_10 = x_108;
goto block_101;
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_104);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_104, 0);
x_112 = lean_ctor_get(x_104, 1);
x_113 = lean_io_error_to_string(x_111);
x_114 = 3;
x_115 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_114);
x_116 = lean_array_get_size(x_103);
x_117 = lean_array_push(x_103, x_115);
lean_ctor_set(x_7, 0, x_117);
lean_ctor_set(x_104, 1, x_7);
lean_ctor_set(x_104, 0, x_116);
x_9 = x_104;
x_10 = x_112;
goto block_101;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_104, 0);
x_119 = lean_ctor_get(x_104, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_104);
x_120 = lean_io_error_to_string(x_118);
x_121 = 3;
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_121);
x_123 = lean_array_get_size(x_103);
x_124 = lean_array_push(x_103, x_122);
lean_ctor_set(x_7, 0, x_124);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_7);
x_9 = x_125;
x_10 = x_119;
goto block_101;
}
}
}
else
{
lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_7, 0);
x_127 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_128 = lean_ctor_get(x_7, 1);
lean_inc(x_128);
lean_inc(x_126);
lean_dec(x_7);
x_129 = l_Lean_parseImports_x27(x_2, x_1, x_8);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_126);
lean_ctor_set(x_133, 1, x_128);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_127);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_133);
x_9 = x_134;
x_10 = x_131;
goto block_101;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
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
x_143 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_128);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_127);
if (lean_is_scalar(x_137)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_137;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
x_9 = x_144;
x_10 = x_136;
goto block_101;
}
}
block_101:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_array_get_size(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = l_Lake_Module_recParseImports___lambda__2___closed__1;
lean_ctor_set(x_9, 0, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_14, x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = l_Lake_Module_recParseImports___lambda__2___closed__1;
lean_ctor_set(x_9, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_9);
x_22 = 0;
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_25 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8(x_12, x_22, x_23, x_24, x_3, x_4, x_5, x_6, x_13, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_ctor_set(x_26, 0, x_31);
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_39 = x_26;
} else {
 lean_dec_ref(x_26);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_25, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_26);
if (x_45 == 0)
{
return x_25;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_26, 0);
x_47 = lean_ctor_get(x_26, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_26);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_25, 0, x_48);
return x_25;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
lean_dec(x_25);
x_50 = lean_ctor_get(x_26, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_26, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_52 = x_26;
} else {
 lean_dec_ref(x_26);
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
x_55 = !lean_is_exclusive(x_25);
if (x_55 == 0)
{
return x_25;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_25, 0);
x_57 = lean_ctor_get(x_25, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_25);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_9, 0);
x_60 = lean_ctor_get(x_9, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_9);
x_61 = lean_array_get_size(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_lt(x_62, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = l_Lake_Module_recParseImports___lambda__2___closed__1;
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_10);
return x_66;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_61, x_61);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = l_Lake_Module_recParseImports___lambda__2___closed__1;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_60);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_10);
return x_70;
}
else
{
size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_71 = 0;
x_72 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_73 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_74 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8(x_59, x_71, x_72, x_73, x_3, x_4, x_5, x_6, x_60, x_10);
lean_dec(x_59);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
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
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
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
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
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
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_74, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_74, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_93 = x_74;
} else {
 lean_dec_ref(x_74);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_9);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_9);
lean_ctor_set(x_96, 1, x_10);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_9, 0);
x_98 = lean_ctor_get(x_9, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_9);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_10);
return x_100;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Lake_Module_recParseImports___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recParseImports___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
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
x_16 = lean_string_utf8_byte_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_19 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_14, x_16, x_17);
x_20 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_14, x_19, x_16);
x_21 = lean_string_utf8_extract(x_14, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
x_22 = l_Lake_Module_recParseImports___lambda__4___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_array_push(x_29, x_27);
lean_ctor_set(x_13, 0, x_30);
x_31 = lean_box(0);
x_32 = l_Lake_Module_recParseImports___lambda__3(x_15, x_31, x_2, x_3, x_4, x_5, x_13, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_33);
lean_dec(x_13);
x_36 = lean_array_push(x_33, x_27);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_34);
x_38 = lean_box(0);
x_39 = l_Lake_Module_recParseImports___lambda__3(x_15, x_38, x_2, x_3, x_4, x_5, x_37, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_16);
lean_dec(x_14);
x_40 = lean_box(0);
x_41 = l_Lake_Module_recParseImports___lambda__3(x_15, x_40, x_2, x_3, x_4, x_5, x_13, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_9, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_9, 0, x_47);
return x_9;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_dec(x_9);
x_49 = lean_ctor_get(x_10, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_51 = x_10;
} else {
 lean_dec_ref(x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_9);
if (x_54 == 0)
{
return x_9;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_9, 0);
x_56 = lean_ctor_get(x_9, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_9);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l_Lake_Module_recParseImports___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recParseImports___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_2 = 0;
x_3 = l_Lake_BuildTrace_nil;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 7);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_System_FilePath_join(x_10, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_System_FilePath_join(x_13, x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lake_Module_recParseImports___closed__1;
x_19 = l_Lean_modToFilePath(x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lake_Module_recParseImports___lambda__1___boxed), 7, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lake_Module_recParseImports___lambda__2___boxed), 8, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 8, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = l_Lake_Module_recParseImports___closed__2;
x_24 = lean_alloc_closure((void*)(l_Lake_Module_recParseImports___lambda__4), 7, 6);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_23);
x_25 = l_Task_Priority_default;
x_26 = lean_io_as_task(x_24, x_25, x_7);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_30 = 0;
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_36 = 0;
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Module_recParseImports___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Module_recParseImports___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Module_recParseImports___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
x_9 = lean_string_append(x_8, x_7);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = 1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1;
x_13 = l_Lean_Name_toString(x_10, x_11, x_12);
x_14 = lean_string_append(x_9, x_13);
lean_dec(x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__2;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_importsFacetConfig___elambda__1___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1;
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
static lean_object* _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__3;
x_4 = l_Substring_prevn(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__4;
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__5;
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_6 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__6;
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
x_8 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__6;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2(x_2, x_9, x_10, x_11);
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
x_22 = l_Array_mapMUnsafe_map___at_Lake_Module_importsFacetConfig___elambda__1___spec__3(x_20, x_21, x_2);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Json_compress(x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_importsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imports", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_importsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_importsFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_importsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recParseImports), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_importsFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_importsFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_importsFacetConfig___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_importsFacetConfig___closed__3;
x_2 = 0;
x_3 = l_Lake_Module_importsFacetConfig___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_importsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_importsFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_importsFacetConfig___elambda__1___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Module_importsFacetConfig___elambda__1___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_importsFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_collectImportsAux___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_17 = lean_apply_7(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; size_t x_26; size_t x_27; lean_object* x_28; 
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
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_unbox(x_22);
lean_dec(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_25);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_28 = lean_array_uset(x_16, x_3, x_24);
x_3 = x_27;
x_4 = x_28;
x_9 = x_21;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_17, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_17, 0, x_35);
return x_17;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_dec(x_17);
x_37 = lean_ctor_get(x_18, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_39 = x_18;
} else {
 lean_dec_ref(x_18);
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
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_17, 0);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_17);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__3(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": bad import '", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__2(x_7, x_6);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_9 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1(x_8, x_10);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__2(x_13, x_12);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1(x_15, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_25 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_26 = lean_string_append(x_25, x_3);
x_27 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = 1;
x_32 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1;
x_33 = l_Lean_Name_toString(x_30, x_31, x_32);
x_34 = lean_string_append(x_28, x_33);
lean_dec(x_33);
x_35 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_array_push(x_43, x_38);
lean_ctor_set(x_40, 0, x_44);
x_45 = lean_unsigned_to_nat(0u);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get_uint8(x_40, sizeof(void*)*2);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_46);
lean_dec(x_40);
x_49 = lean_array_push(x_46, x_38);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_47);
x_51 = lean_unsigned_to_nat(0u);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_50);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_dec(x_1);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_52, sizeof(void*)*2);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = lean_array_push(x_53, x_38);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 1);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_54);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_1);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_1, 1);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_array_push(x_64, x_38);
lean_ctor_set(x_62, 0, x_65);
return x_1;
}
else
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get_uint8(x_62, sizeof(void*)*2);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_inc(x_66);
lean_dec(x_62);
x_69 = lean_array_push(x_66, x_38);
x_70 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_67);
lean_ctor_set(x_1, 1, x_70);
return x_1;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_1, 1);
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
lean_inc(x_72);
lean_dec(x_1);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_71, sizeof(void*)*2);
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
x_77 = lean_array_push(x_73, x_38);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_74);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___boxed), 4, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Task_Priority_default;
x_8 = 1;
x_9 = lean_task_map(x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__2), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Task_Priority_default;
x_10 = 1;
x_11 = lean_task_bind(x_5, x_8, x_9, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectImportsAux___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lake_collectImportsAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_2 = l_Lake_Module_recParseImports___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_collectImportsAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_collectImportsAux___closed__1;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_collectImportsAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_collectImportsAux___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_collectImportsAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lake_collectImportsAux___closed__3;
x_2 = l_Lake_collectImportsAux___closed__2;
x_3 = l_Task_Priority_default;
x_4 = 1;
x_5 = lean_task_map(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_collectImportsAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lake_collectImportsAux___closed__4;
x_2 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_collectImportsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lake_collectImportsAux___spec__1(x_3, x_10, x_11, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_21 = l_Lake_collectImportsAux___closed__5;
lean_ctor_set(x_13, 0, x_21);
return x_12;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_23 = l_Lake_collectImportsAux___closed__5;
lean_ctor_set(x_13, 0, x_23);
return x_12;
}
else
{
size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_24 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_25 = l_Lake_collectImportsAux___closed__2;
x_26 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4(x_1, x_17, x_11, x_24, x_25);
lean_dec(x_17);
x_27 = l_Lake_collectImportsAux___closed__3;
x_28 = l_Task_Priority_default;
x_29 = 1;
x_30 = lean_task_map(x_27, x_26, x_28, x_29);
x_31 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
lean_ctor_set(x_13, 0, x_33);
return x_12;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_array_get_size(x_34);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_1);
x_39 = l_Lake_collectImportsAux___closed__5;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_12, 0, x_40);
return x_12;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_36, x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_1);
x_42 = l_Lake_collectImportsAux___closed__5;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_12, 0, x_43);
return x_12;
}
else
{
size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_45 = l_Lake_collectImportsAux___closed__2;
x_46 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4(x_1, x_34, x_11, x_44, x_45);
lean_dec(x_34);
x_47 = l_Lake_collectImportsAux___closed__3;
x_48 = l_Task_Priority_default;
x_49 = 1;
x_50 = lean_task_map(x_47, x_46, x_48, x_49);
x_51 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_52 = 0;
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_35);
lean_ctor_set(x_12, 0, x_54);
return x_12;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_12, 1);
lean_inc(x_55);
lean_dec(x_12);
x_56 = lean_ctor_get(x_13, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_58 = x_13;
} else {
 lean_dec_ref(x_13);
 x_58 = lean_box(0);
}
x_59 = lean_array_get_size(x_56);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_lt(x_60, x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_1);
x_62 = l_Lake_collectImportsAux___closed__5;
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_59, x_59);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_1);
x_66 = l_Lake_collectImportsAux___closed__5;
if (lean_is_scalar(x_58)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_58;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_57);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_55);
return x_68;
}
else
{
size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_70 = l_Lake_collectImportsAux___closed__2;
x_71 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4(x_1, x_56, x_11, x_69, x_70);
lean_dec(x_56);
x_72 = l_Lake_collectImportsAux___closed__3;
x_73 = l_Task_Priority_default;
x_74 = 1;
x_75 = lean_task_map(x_72, x_71, x_73, x_74);
x_76 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_77 = 0;
x_78 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_77);
if (lean_is_scalar(x_58)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_58;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_57);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_55);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_12);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_12, 0);
lean_dec(x_82);
x_83 = !lean_is_exclusive(x_13);
if (x_83 == 0)
{
return x_12;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_13, 0);
x_85 = lean_ctor_get(x_13, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_13);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_12, 0, x_86);
return x_12;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_12, 1);
lean_inc(x_87);
lean_dec(x_12);
x_88 = lean_ctor_get(x_13, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_13, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_90 = x_13;
} else {
 lean_dec_ref(x_13);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_12);
if (x_93 == 0)
{
return x_12;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_12, 0);
x_95 = lean_ctor_get(x_12, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_12);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_collectImportsAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_collectImportsAux___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("transImports", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = lean_apply_6(x_4, x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_27 = lean_array_uset(x_15, x_2, x_24);
x_2 = x_26;
x_3 = x_27;
x_8 = x_22;
x_9 = x_20;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_18, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_18, 0, x_34);
return x_18;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_38 = x_19;
} else {
 lean_dec_ref(x_19);
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
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_18);
if (x_41 == 0)
{
return x_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__2), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Task_Priority_default;
x_10 = 1;
x_11 = lean_task_bind(x_5, x_8, x_9, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recComputeTransImports___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_119; lean_object* x_120; lean_object* x_136; lean_object* x_137; lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_2, 0);
lean_inc(x_161);
lean_dec(x_2);
x_162 = lean_io_wait(x_161, x_8);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = !lean_is_exclusive(x_163);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_167 = lean_ctor_get(x_163, 0);
x_168 = lean_ctor_get(x_163, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
lean_dec(x_164);
x_170 = lean_array_get_size(x_169);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_nat_dec_lt(x_171, x_170);
if (x_172 == 0)
{
lean_dec(x_170);
lean_dec(x_169);
lean_ctor_set(x_163, 1, x_7);
x_136 = x_163;
x_137 = x_165;
goto block_160;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_170, x_170);
if (x_173 == 0)
{
lean_dec(x_170);
lean_dec(x_169);
lean_ctor_set(x_163, 1, x_7);
x_136 = x_163;
x_137 = x_165;
goto block_160;
}
else
{
size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_free_object(x_163);
x_174 = 0;
x_175 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_176 = lean_box(0);
x_177 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_169, x_174, x_175, x_176, x_7, x_165);
lean_dec(x_169);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = !lean_is_exclusive(x_178);
if (x_180 == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_178, 0);
lean_dec(x_181);
lean_ctor_set(x_178, 0, x_167);
x_136 = x_178;
x_137 = x_179;
goto block_160;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
lean_dec(x_178);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_167);
lean_ctor_set(x_183, 1, x_182);
x_136 = x_183;
x_137 = x_179;
goto block_160;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_163, 0);
lean_inc(x_184);
lean_dec(x_163);
x_185 = lean_ctor_get(x_164, 0);
lean_inc(x_185);
lean_dec(x_164);
x_186 = lean_array_get_size(x_185);
x_187 = lean_unsigned_to_nat(0u);
x_188 = lean_nat_dec_lt(x_187, x_186);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_186);
lean_dec(x_185);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_184);
lean_ctor_set(x_189, 1, x_7);
x_136 = x_189;
x_137 = x_165;
goto block_160;
}
else
{
uint8_t x_190; 
x_190 = lean_nat_dec_le(x_186, x_186);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_186);
lean_dec(x_185);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_184);
lean_ctor_set(x_191, 1, x_7);
x_136 = x_191;
x_137 = x_165;
goto block_160;
}
else
{
size_t x_192; size_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_192 = 0;
x_193 = lean_usize_of_nat(x_186);
lean_dec(x_186);
x_194 = lean_box(0);
x_195 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_185, x_192, x_193, x_194, x_7, x_165);
lean_dec(x_185);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_184);
lean_ctor_set(x_200, 1, x_198);
x_136 = x_200;
x_137 = x_197;
goto block_160;
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_201 = lean_ctor_get(x_163, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_162, 1);
lean_inc(x_202);
lean_dec(x_162);
x_203 = !lean_is_exclusive(x_163);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_204 = lean_ctor_get(x_163, 0);
x_205 = lean_ctor_get(x_163, 1);
lean_dec(x_205);
x_206 = lean_ctor_get(x_201, 0);
lean_inc(x_206);
lean_dec(x_201);
x_207 = lean_array_get_size(x_206);
x_208 = lean_unsigned_to_nat(0u);
x_209 = lean_nat_dec_lt(x_208, x_207);
if (x_209 == 0)
{
lean_dec(x_207);
lean_dec(x_206);
lean_ctor_set(x_163, 1, x_7);
x_136 = x_163;
x_137 = x_202;
goto block_160;
}
else
{
uint8_t x_210; 
x_210 = lean_nat_dec_le(x_207, x_207);
if (x_210 == 0)
{
lean_dec(x_207);
lean_dec(x_206);
lean_ctor_set(x_163, 1, x_7);
x_136 = x_163;
x_137 = x_202;
goto block_160;
}
else
{
size_t x_211; size_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
lean_free_object(x_163);
x_211 = 0;
x_212 = lean_usize_of_nat(x_207);
lean_dec(x_207);
x_213 = lean_box(0);
x_214 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_206, x_211, x_212, x_213, x_7, x_202);
lean_dec(x_206);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = !lean_is_exclusive(x_215);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_215, 0);
lean_dec(x_218);
lean_ctor_set_tag(x_215, 1);
lean_ctor_set(x_215, 0, x_204);
x_136 = x_215;
x_137 = x_216;
goto block_160;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
lean_dec(x_215);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_204);
lean_ctor_set(x_220, 1, x_219);
x_136 = x_220;
x_137 = x_216;
goto block_160;
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_163, 0);
lean_inc(x_221);
lean_dec(x_163);
x_222 = lean_ctor_get(x_201, 0);
lean_inc(x_222);
lean_dec(x_201);
x_223 = lean_array_get_size(x_222);
x_224 = lean_unsigned_to_nat(0u);
x_225 = lean_nat_dec_lt(x_224, x_223);
if (x_225 == 0)
{
lean_object* x_226; 
lean_dec(x_223);
lean_dec(x_222);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_221);
lean_ctor_set(x_226, 1, x_7);
x_136 = x_226;
x_137 = x_202;
goto block_160;
}
else
{
uint8_t x_227; 
x_227 = lean_nat_dec_le(x_223, x_223);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_223);
lean_dec(x_222);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_7);
x_136 = x_228;
x_137 = x_202;
goto block_160;
}
else
{
size_t x_229; size_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_229 = 0;
x_230 = lean_usize_of_nat(x_223);
lean_dec(x_223);
x_231 = lean_box(0);
x_232 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_222, x_229, x_230, x_231, x_7, x_202);
lean_dec(x_222);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_236 = x_233;
} else {
 lean_dec_ref(x_233);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
 lean_ctor_set_tag(x_237, 1);
}
lean_ctor_set(x_237, 0, x_221);
lean_ctor_set(x_237, 1, x_235);
x_136 = x_237;
x_137 = x_234;
goto block_160;
}
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_162);
if (x_238 == 0)
{
return x_162;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_162, 0);
x_240 = lean_ctor_get(x_162, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_162);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
block_118:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 7);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_System_FilePath_join(x_15, x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_System_FilePath_join(x_18, x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_Lake_Module_recParseImports___closed__1;
x_24 = l_Lean_modToFilePath(x_21, x_22, x_23);
lean_dec(x_22);
lean_dec(x_21);
x_25 = lean_array_size(x_11);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1(x_25, x_26, x_11, x_3, x_4, x_5, x_6, x_12, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_array_get_size(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_24);
x_36 = l_Lake_collectImportsAux___closed__5;
lean_ctor_set(x_28, 0, x_36);
return x_27;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_33, x_33);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_24);
x_38 = l_Lake_collectImportsAux___closed__5;
lean_ctor_set(x_28, 0, x_38);
return x_27;
}
else
{
size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_39 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_40 = l_Lake_collectImportsAux___closed__2;
x_41 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2(x_24, x_32, x_26, x_39, x_40);
lean_dec(x_32);
x_42 = l_Lake_collectImportsAux___closed__3;
x_43 = l_Task_Priority_default;
x_44 = 1;
x_45 = lean_task_map(x_42, x_41, x_43, x_44);
x_46 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_47 = 0;
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_47);
lean_ctor_set(x_28, 0, x_48);
return x_27;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_51 = lean_array_get_size(x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_lt(x_52, x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_24);
x_54 = l_Lake_collectImportsAux___closed__5;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_27, 0, x_55);
return x_27;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_51, x_51);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_24);
x_57 = l_Lake_collectImportsAux___closed__5;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_27, 0, x_58);
return x_27;
}
else
{
size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_59 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_60 = l_Lake_collectImportsAux___closed__2;
x_61 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2(x_24, x_49, x_26, x_59, x_60);
lean_dec(x_49);
x_62 = l_Lake_collectImportsAux___closed__3;
x_63 = l_Task_Priority_default;
x_64 = 1;
x_65 = lean_task_map(x_62, x_61, x_63, x_64);
x_66 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_67 = 0;
x_68 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_50);
lean_ctor_set(x_27, 0, x_69);
return x_27;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_27, 1);
lean_inc(x_70);
lean_dec(x_27);
x_71 = lean_ctor_get(x_28, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_28, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_73 = x_28;
} else {
 lean_dec_ref(x_28);
 x_73 = lean_box(0);
}
x_74 = lean_array_get_size(x_71);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_lt(x_75, x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_24);
x_77 = l_Lake_collectImportsAux___closed__5;
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_70);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_74, x_74);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_24);
x_81 = l_Lake_collectImportsAux___closed__5;
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_72);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_70);
return x_83;
}
else
{
size_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_84 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_85 = l_Lake_collectImportsAux___closed__2;
x_86 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2(x_24, x_71, x_26, x_84, x_85);
lean_dec(x_71);
x_87 = l_Lake_collectImportsAux___closed__3;
x_88 = l_Task_Priority_default;
x_89 = 1;
x_90 = lean_task_map(x_87, x_86, x_88, x_89);
x_91 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_92 = 0;
x_93 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*2, x_92);
if (lean_is_scalar(x_73)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_73;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_72);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_70);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_24);
x_96 = !lean_is_exclusive(x_27);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_27, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_28);
if (x_98 == 0)
{
return x_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_28, 0);
x_100 = lean_ctor_get(x_28, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_28);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_27, 0, x_101);
return x_27;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_27, 1);
lean_inc(x_102);
lean_dec(x_27);
x_103 = lean_ctor_get(x_28, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_28, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_105 = x_28;
} else {
 lean_dec_ref(x_28);
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
lean_dec(x_24);
x_108 = !lean_is_exclusive(x_27);
if (x_108 == 0)
{
return x_27;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_27, 0);
x_110 = lean_ctor_get(x_27, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_27);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_9);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_9);
lean_ctor_set(x_113, 1, x_10);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_9, 0);
x_115 = lean_ctor_get(x_9, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_9);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_10);
return x_117;
}
}
}
block_135:
{
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_119, 1);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec(x_122);
lean_ctor_set(x_119, 1, x_123);
x_9 = x_119;
x_10 = x_120;
goto block_118;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_119, 0);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_119);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_9 = x_127;
x_10 = x_120;
goto block_118;
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_119);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_119, 1);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec(x_129);
lean_ctor_set(x_119, 1, x_130);
x_9 = x_119;
x_10 = x_120;
goto block_118;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_119, 0);
x_132 = lean_ctor_get(x_119, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_119);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
x_9 = x_134;
x_10 = x_120;
goto block_118;
}
}
}
block_160:
{
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_136);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_136, 1);
x_140 = 0;
x_141 = l_Lake_BuildTrace_nil;
x_142 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_140);
lean_ctor_set(x_136, 1, x_142);
x_119 = x_136;
x_120 = x_137;
goto block_135;
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_136, 0);
x_144 = lean_ctor_get(x_136, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_136);
x_145 = 0;
x_146 = l_Lake_BuildTrace_nil;
x_147 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*2, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
x_119 = x_148;
x_120 = x_137;
goto block_135;
}
}
else
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_136);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_136, 1);
x_151 = 0;
x_152 = l_Lake_BuildTrace_nil;
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_151);
lean_ctor_set(x_136, 1, x_153);
x_119 = x_136;
x_120 = x_137;
goto block_135;
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_136, 0);
x_155 = lean_ctor_get(x_136, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_136);
x_156 = 0;
x_157 = l_Lake_BuildTrace_nil;
x_158 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set_uint8(x_158, sizeof(void*)*2, x_156);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_154);
lean_ctor_set(x_159, 1, x_158);
x_119 = x_159;
x_120 = x_137;
goto block_135;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recComputeTransImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lake_Module_importsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, lean_box(0));
x_11 = lean_alloc_closure((void*)(l_Lake_Module_recComputeTransImports___lambda__1), 8, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg), 8, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lake_ensureJob___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_transImportsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recComputeTransImports), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_transImportsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_transImportsFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_transImportsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_transImportsFacetConfig___closed__1;
x_2 = 0;
x_3 = l_Lake_Module_transImportsFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_transImportsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_transImportsFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_transImportsFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precompileImports", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_31; lean_object* x_32; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_51 = lean_ctor_get(x_13, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*29);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_ctor_get_uint8(x_55, sizeof(void*)*9);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
lean_inc(x_13);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_13);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = lean_apply_6(x_4, x_58, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = 0;
x_65 = lean_box(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_60, 0, x_66);
x_31 = x_60;
x_32 = x_61;
goto block_50;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_60);
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
x_31 = x_72;
x_32 = x_61;
goto block_50;
}
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
lean_dec(x_59);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
x_31 = x_60;
x_32 = x_73;
goto block_50;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_31 = x_77;
x_32 = x_73;
goto block_50;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_59);
if (x_78 == 0)
{
return x_59;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_59, 0);
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_59);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_13);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_13);
lean_ctor_set(x_83, 1, x_82);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_84 = lean_apply_6(x_4, x_83, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_85, 0);
x_89 = 1;
x_90 = lean_box(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
lean_ctor_set(x_85, 0, x_91);
x_31 = x_85;
x_32 = x_86;
goto block_50;
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_85, 0);
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_85);
x_94 = 1;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
x_31 = x_97;
x_32 = x_86;
goto block_50;
}
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_84, 1);
lean_inc(x_98);
lean_dec(x_84);
x_99 = !lean_is_exclusive(x_85);
if (x_99 == 0)
{
x_31 = x_85;
x_32 = x_98;
goto block_50;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_85, 0);
x_101 = lean_ctor_get(x_85, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_85);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_31 = x_102;
x_32 = x_98;
goto block_50;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_103 = !lean_is_exclusive(x_84);
if (x_103 == 0)
{
return x_84;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_84, 0);
x_105 = lean_ctor_get(x_84, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_84);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_51);
x_107 = l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_13);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_13);
lean_ctor_set(x_108, 1, x_107);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_109 = lean_apply_6(x_4, x_108, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = !lean_is_exclusive(x_110);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_110, 0);
x_114 = 1;
x_115 = lean_box(x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
lean_ctor_set(x_110, 0, x_116);
x_31 = x_110;
x_32 = x_111;
goto block_50;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_110, 0);
x_118 = lean_ctor_get(x_110, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_110);
x_119 = 1;
x_120 = lean_box(x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_117);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_118);
x_31 = x_122;
x_32 = x_111;
goto block_50;
}
}
else
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_109, 1);
lean_inc(x_123);
lean_dec(x_109);
x_124 = !lean_is_exclusive(x_110);
if (x_124 == 0)
{
x_31 = x_110;
x_32 = x_123;
goto block_50;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_110, 0);
x_126 = lean_ctor_get(x_110, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_110);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_31 = x_127;
x_32 = x_123;
goto block_50;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_128 = !lean_is_exclusive(x_109);
if (x_128 == 0)
{
return x_109;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_109, 0);
x_130 = lean_ctor_get(x_109, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_109);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
block_30:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_15, x_2, x_18);
x_2 = x_21;
x_3 = x_22;
x_8 = x_19;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_17);
return x_29;
}
}
}
block_50:
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_13);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_38);
lean_ctor_set(x_31, 0, x_37);
x_16 = x_31;
x_17 = x_32;
goto block_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_40);
x_16 = x_45;
x_17 = x_32;
goto block_30;
}
}
else
{
uint8_t x_46; 
lean_dec(x_13);
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
x_16 = x_31;
x_17 = x_32;
goto block_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_16 = x_49;
x_17 = x_32;
goto block_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_computePrecompileImportsAux___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__2), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Task_Priority_default;
x_10 = 1;
x_11 = lean_task_bind(x_5, x_8, x_9, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computePrecompileImportsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_array_size(x_2);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1(x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_20 = l_Lake_collectImportsAux___closed__5;
lean_ctor_set(x_12, 0, x_20);
return x_11;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_17, x_17);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_22 = l_Lake_collectImportsAux___closed__5;
lean_ctor_set(x_12, 0, x_22);
return x_11;
}
else
{
size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_23 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_24 = l_Lake_collectImportsAux___closed__2;
x_25 = l_Array_foldlMUnsafe_fold___at_Lake_computePrecompileImportsAux___spec__2(x_1, x_16, x_10, x_23, x_24);
lean_dec(x_16);
x_26 = l_Lake_collectImportsAux___closed__3;
x_27 = l_Task_Priority_default;
x_28 = 1;
x_29 = lean_task_map(x_26, x_25, x_27, x_28);
x_30 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_31 = 0;
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_31);
lean_ctor_set(x_12, 0, x_32);
return x_11;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = lean_array_get_size(x_33);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_lt(x_36, x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_1);
x_38 = l_Lake_collectImportsAux___closed__5;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_11, 0, x_39);
return x_11;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_35, x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_1);
x_41 = l_Lake_collectImportsAux___closed__5;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_11, 0, x_42);
return x_11;
}
else
{
size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_44 = l_Lake_collectImportsAux___closed__2;
x_45 = l_Array_foldlMUnsafe_fold___at_Lake_computePrecompileImportsAux___spec__2(x_1, x_33, x_10, x_43, x_44);
lean_dec(x_33);
x_46 = l_Lake_collectImportsAux___closed__3;
x_47 = l_Task_Priority_default;
x_48 = 1;
x_49 = lean_task_map(x_46, x_45, x_47, x_48);
x_50 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_51 = 0;
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_34);
lean_ctor_set(x_11, 0, x_53);
return x_11;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
lean_dec(x_11);
x_55 = lean_ctor_get(x_12, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_57 = x_12;
} else {
 lean_dec_ref(x_12);
 x_57 = lean_box(0);
}
x_58 = lean_array_get_size(x_55);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_lt(x_59, x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_1);
x_61 = l_Lake_collectImportsAux___closed__5;
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
return x_63;
}
else
{
uint8_t x_64; 
x_64 = lean_nat_dec_le(x_58, x_58);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_1);
x_65 = l_Lake_collectImportsAux___closed__5;
if (lean_is_scalar(x_57)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_57;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_54);
return x_67;
}
else
{
size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_68 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_69 = l_Lake_collectImportsAux___closed__2;
x_70 = l_Array_foldlMUnsafe_fold___at_Lake_computePrecompileImportsAux___spec__2(x_1, x_55, x_10, x_68, x_69);
lean_dec(x_55);
x_71 = l_Lake_collectImportsAux___closed__3;
x_72 = l_Task_Priority_default;
x_73 = 1;
x_74 = lean_task_map(x_71, x_70, x_72, x_73);
x_75 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_76 = 0;
x_77 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*2, x_76);
if (lean_is_scalar(x_57)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_57;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_56);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_54);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_11);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_11, 0);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_12);
if (x_82 == 0)
{
return x_11;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_12, 0);
x_84 = lean_ctor_get(x_12, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_12);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_11, 0, x_85);
return x_11;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_11, 1);
lean_inc(x_86);
lean_dec(x_11);
x_87 = lean_ctor_get(x_12, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_12, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_89 = x_12;
} else {
 lean_dec_ref(x_12);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_86);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_11);
if (x_92 == 0)
{
return x_11;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_11, 0);
x_94 = lean_ctor_get(x_11, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_11);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_computePrecompileImportsAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_computePrecompileImportsAux___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__2), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Task_Priority_default;
x_10 = 1;
x_11 = lean_task_bind(x_5, x_8, x_9, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recComputePrecompileImports___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_119; lean_object* x_120; lean_object* x_136; lean_object* x_137; lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_2, 0);
lean_inc(x_161);
lean_dec(x_2);
x_162 = lean_io_wait(x_161, x_8);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = !lean_is_exclusive(x_163);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_167 = lean_ctor_get(x_163, 0);
x_168 = lean_ctor_get(x_163, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
lean_dec(x_164);
x_170 = lean_array_get_size(x_169);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_nat_dec_lt(x_171, x_170);
if (x_172 == 0)
{
lean_dec(x_170);
lean_dec(x_169);
lean_ctor_set(x_163, 1, x_7);
x_136 = x_163;
x_137 = x_165;
goto block_160;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_170, x_170);
if (x_173 == 0)
{
lean_dec(x_170);
lean_dec(x_169);
lean_ctor_set(x_163, 1, x_7);
x_136 = x_163;
x_137 = x_165;
goto block_160;
}
else
{
size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_free_object(x_163);
x_174 = 0;
x_175 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_176 = lean_box(0);
x_177 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_169, x_174, x_175, x_176, x_7, x_165);
lean_dec(x_169);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = !lean_is_exclusive(x_178);
if (x_180 == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_178, 0);
lean_dec(x_181);
lean_ctor_set(x_178, 0, x_167);
x_136 = x_178;
x_137 = x_179;
goto block_160;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
lean_dec(x_178);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_167);
lean_ctor_set(x_183, 1, x_182);
x_136 = x_183;
x_137 = x_179;
goto block_160;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_163, 0);
lean_inc(x_184);
lean_dec(x_163);
x_185 = lean_ctor_get(x_164, 0);
lean_inc(x_185);
lean_dec(x_164);
x_186 = lean_array_get_size(x_185);
x_187 = lean_unsigned_to_nat(0u);
x_188 = lean_nat_dec_lt(x_187, x_186);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_186);
lean_dec(x_185);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_184);
lean_ctor_set(x_189, 1, x_7);
x_136 = x_189;
x_137 = x_165;
goto block_160;
}
else
{
uint8_t x_190; 
x_190 = lean_nat_dec_le(x_186, x_186);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_186);
lean_dec(x_185);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_184);
lean_ctor_set(x_191, 1, x_7);
x_136 = x_191;
x_137 = x_165;
goto block_160;
}
else
{
size_t x_192; size_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_192 = 0;
x_193 = lean_usize_of_nat(x_186);
lean_dec(x_186);
x_194 = lean_box(0);
x_195 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_185, x_192, x_193, x_194, x_7, x_165);
lean_dec(x_185);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_184);
lean_ctor_set(x_200, 1, x_198);
x_136 = x_200;
x_137 = x_197;
goto block_160;
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_201 = lean_ctor_get(x_163, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_162, 1);
lean_inc(x_202);
lean_dec(x_162);
x_203 = !lean_is_exclusive(x_163);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_204 = lean_ctor_get(x_163, 0);
x_205 = lean_ctor_get(x_163, 1);
lean_dec(x_205);
x_206 = lean_ctor_get(x_201, 0);
lean_inc(x_206);
lean_dec(x_201);
x_207 = lean_array_get_size(x_206);
x_208 = lean_unsigned_to_nat(0u);
x_209 = lean_nat_dec_lt(x_208, x_207);
if (x_209 == 0)
{
lean_dec(x_207);
lean_dec(x_206);
lean_ctor_set(x_163, 1, x_7);
x_136 = x_163;
x_137 = x_202;
goto block_160;
}
else
{
uint8_t x_210; 
x_210 = lean_nat_dec_le(x_207, x_207);
if (x_210 == 0)
{
lean_dec(x_207);
lean_dec(x_206);
lean_ctor_set(x_163, 1, x_7);
x_136 = x_163;
x_137 = x_202;
goto block_160;
}
else
{
size_t x_211; size_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
lean_free_object(x_163);
x_211 = 0;
x_212 = lean_usize_of_nat(x_207);
lean_dec(x_207);
x_213 = lean_box(0);
x_214 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_206, x_211, x_212, x_213, x_7, x_202);
lean_dec(x_206);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = !lean_is_exclusive(x_215);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_215, 0);
lean_dec(x_218);
lean_ctor_set_tag(x_215, 1);
lean_ctor_set(x_215, 0, x_204);
x_136 = x_215;
x_137 = x_216;
goto block_160;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
lean_dec(x_215);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_204);
lean_ctor_set(x_220, 1, x_219);
x_136 = x_220;
x_137 = x_216;
goto block_160;
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_163, 0);
lean_inc(x_221);
lean_dec(x_163);
x_222 = lean_ctor_get(x_201, 0);
lean_inc(x_222);
lean_dec(x_201);
x_223 = lean_array_get_size(x_222);
x_224 = lean_unsigned_to_nat(0u);
x_225 = lean_nat_dec_lt(x_224, x_223);
if (x_225 == 0)
{
lean_object* x_226; 
lean_dec(x_223);
lean_dec(x_222);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_221);
lean_ctor_set(x_226, 1, x_7);
x_136 = x_226;
x_137 = x_202;
goto block_160;
}
else
{
uint8_t x_227; 
x_227 = lean_nat_dec_le(x_223, x_223);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_223);
lean_dec(x_222);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_7);
x_136 = x_228;
x_137 = x_202;
goto block_160;
}
else
{
size_t x_229; size_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_229 = 0;
x_230 = lean_usize_of_nat(x_223);
lean_dec(x_223);
x_231 = lean_box(0);
x_232 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_222, x_229, x_230, x_231, x_7, x_202);
lean_dec(x_222);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_236 = x_233;
} else {
 lean_dec_ref(x_233);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
 lean_ctor_set_tag(x_237, 1);
}
lean_ctor_set(x_237, 0, x_221);
lean_ctor_set(x_237, 1, x_235);
x_136 = x_237;
x_137 = x_234;
goto block_160;
}
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_162);
if (x_238 == 0)
{
return x_162;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_162, 0);
x_240 = lean_ctor_get(x_162, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_162);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
block_118:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 7);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_System_FilePath_join(x_15, x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_System_FilePath_join(x_18, x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_Lake_Module_recParseImports___closed__1;
x_24 = l_Lean_modToFilePath(x_21, x_22, x_23);
lean_dec(x_22);
lean_dec(x_21);
x_25 = lean_array_size(x_11);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1(x_25, x_26, x_11, x_3, x_4, x_5, x_6, x_12, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_array_get_size(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_24);
x_36 = l_Lake_collectImportsAux___closed__5;
lean_ctor_set(x_28, 0, x_36);
return x_27;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_33, x_33);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_24);
x_38 = l_Lake_collectImportsAux___closed__5;
lean_ctor_set(x_28, 0, x_38);
return x_27;
}
else
{
size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_39 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_40 = l_Lake_collectImportsAux___closed__2;
x_41 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(x_24, x_32, x_26, x_39, x_40);
lean_dec(x_32);
x_42 = l_Lake_collectImportsAux___closed__3;
x_43 = l_Task_Priority_default;
x_44 = 1;
x_45 = lean_task_map(x_42, x_41, x_43, x_44);
x_46 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_47 = 0;
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_47);
lean_ctor_set(x_28, 0, x_48);
return x_27;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_51 = lean_array_get_size(x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_lt(x_52, x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_24);
x_54 = l_Lake_collectImportsAux___closed__5;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_27, 0, x_55);
return x_27;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_51, x_51);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_24);
x_57 = l_Lake_collectImportsAux___closed__5;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_27, 0, x_58);
return x_27;
}
else
{
size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_59 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_60 = l_Lake_collectImportsAux___closed__2;
x_61 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(x_24, x_49, x_26, x_59, x_60);
lean_dec(x_49);
x_62 = l_Lake_collectImportsAux___closed__3;
x_63 = l_Task_Priority_default;
x_64 = 1;
x_65 = lean_task_map(x_62, x_61, x_63, x_64);
x_66 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_67 = 0;
x_68 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_50);
lean_ctor_set(x_27, 0, x_69);
return x_27;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_27, 1);
lean_inc(x_70);
lean_dec(x_27);
x_71 = lean_ctor_get(x_28, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_28, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_73 = x_28;
} else {
 lean_dec_ref(x_28);
 x_73 = lean_box(0);
}
x_74 = lean_array_get_size(x_71);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_lt(x_75, x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_24);
x_77 = l_Lake_collectImportsAux___closed__5;
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_70);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_74, x_74);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_24);
x_81 = l_Lake_collectImportsAux___closed__5;
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_72);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_70);
return x_83;
}
else
{
size_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_84 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_85 = l_Lake_collectImportsAux___closed__2;
x_86 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(x_24, x_71, x_26, x_84, x_85);
lean_dec(x_71);
x_87 = l_Lake_collectImportsAux___closed__3;
x_88 = l_Task_Priority_default;
x_89 = 1;
x_90 = lean_task_map(x_87, x_86, x_88, x_89);
x_91 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_92 = 0;
x_93 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*2, x_92);
if (lean_is_scalar(x_73)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_73;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_72);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_70);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_24);
x_96 = !lean_is_exclusive(x_27);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_27, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_28);
if (x_98 == 0)
{
return x_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_28, 0);
x_100 = lean_ctor_get(x_28, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_28);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_27, 0, x_101);
return x_27;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_27, 1);
lean_inc(x_102);
lean_dec(x_27);
x_103 = lean_ctor_get(x_28, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_28, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_105 = x_28;
} else {
 lean_dec_ref(x_28);
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
lean_dec(x_24);
x_108 = !lean_is_exclusive(x_27);
if (x_108 == 0)
{
return x_27;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_27, 0);
x_110 = lean_ctor_get(x_27, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_27);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_9);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_9);
lean_ctor_set(x_113, 1, x_10);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_9, 0);
x_115 = lean_ctor_get(x_9, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_9);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_10);
return x_117;
}
}
}
block_135:
{
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_119, 1);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec(x_122);
lean_ctor_set(x_119, 1, x_123);
x_9 = x_119;
x_10 = x_120;
goto block_118;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_119, 0);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_119);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_9 = x_127;
x_10 = x_120;
goto block_118;
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_119);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_119, 1);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec(x_129);
lean_ctor_set(x_119, 1, x_130);
x_9 = x_119;
x_10 = x_120;
goto block_118;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_119, 0);
x_132 = lean_ctor_get(x_119, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_119);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
x_9 = x_134;
x_10 = x_120;
goto block_118;
}
}
}
block_160:
{
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_136);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_136, 1);
x_140 = 0;
x_141 = l_Lake_BuildTrace_nil;
x_142 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_140);
lean_ctor_set(x_136, 1, x_142);
x_119 = x_136;
x_120 = x_137;
goto block_135;
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_136, 0);
x_144 = lean_ctor_get(x_136, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_136);
x_145 = 0;
x_146 = l_Lake_BuildTrace_nil;
x_147 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*2, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
x_119 = x_148;
x_120 = x_137;
goto block_135;
}
}
else
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_136);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_136, 1);
x_151 = 0;
x_152 = l_Lake_BuildTrace_nil;
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_151);
lean_ctor_set(x_136, 1, x_153);
x_119 = x_136;
x_120 = x_137;
goto block_135;
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_136, 0);
x_155 = lean_ctor_get(x_136, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_136);
x_156 = 0;
x_157 = l_Lake_BuildTrace_nil;
x_158 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set_uint8(x_158, sizeof(void*)*2, x_156);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_154);
lean_ctor_set(x_159, 1, x_158);
x_119 = x_159;
x_120 = x_137;
goto block_135;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recComputePrecompileImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lake_Module_importsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, lean_box(0));
x_11 = lean_alloc_closure((void*)(l_Lake_Module_recComputePrecompileImports___lambda__1), 8, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg), 8, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lake_ensureJob___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_precompileImportsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recComputePrecompileImports), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_precompileImportsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_precompileImportsFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_precompileImportsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_precompileImportsFacetConfig___closed__1;
x_2 = 0;
x_3 = l_Lake_Module_precompileImportsFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_precompileImportsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_precompileImportsFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_precompileImportsFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_fetchExternLibs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_fold___at_Lake_fetchExternLibs___spec__1(x_1, x_2, x_4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
x_10 = lean_array_push(x_8, x_9);
x_2 = x_10;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_fetchExternLibs___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 10);
lean_inc(x_13);
x_14 = 0;
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_16 = l_Lean_RBNode_fold___at_Lake_fetchExternLibs___spec__1(x_12, x_15, x_13);
lean_dec(x_13);
x_17 = lean_array_size(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2(x_17, x_14, x_16, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_23 = l_Array_append___rarg(x_4, x_21);
lean_dec(x_21);
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
static lean_object* _init_l_Lake_fetchExternLibs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Module_recParseImports___lambda__2___closed__1;
x_2 = l_Lake_Job_collectArray___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchExternLibs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = l_Lake_fetchExternLibs___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_8, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Lake_fetchExternLibs___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = l_Lake_Module_recParseImports___lambda__2___closed__1;
x_21 = l_Array_foldlMUnsafe_fold___at_Lake_fetchExternLibs___spec__2(x_1, x_18, x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = l_Lake_Job_collectArray___rarg(x_26);
lean_dec(x_26);
lean_ctor_set(x_22, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = l_Lake_Job_collectArray___rarg(x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_35 = x_22;
} else {
 lean_dec_ref(x_22);
 x_35 = lean_box(0);
}
x_36 = l_Lake_Job_collectArray___rarg(x_33);
lean_dec(x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_21, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_22);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_22, 0);
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_22);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_21, 0, x_44);
return x_21;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_dec(x_21);
x_46 = lean_ctor_get(x_22, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_48 = x_22;
} else {
 lean_dec_ref(x_22);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
return x_21;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_21, 0);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_21);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_fetchExternLibs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_fold___at_Lake_fetchExternLibs___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_fetchExternLibs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_fetchExternLibs___spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchExternLibs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_fetchExternLibs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("olean", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__2;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_6(x_3, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": module imports itself", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_array_uget(x_5, x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_5, x_4, x_16);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1(x_15, x_21, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = 1;
x_28 = lean_usize_add(x_4, x_27);
x_29 = lean_array_uset(x_17, x_4, x_25);
x_4 = x_28;
x_5 = x_29;
x_10 = x_26;
x_11 = x_24;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_22, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_22, 0, x_36);
return x_22;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_dec(x_22);
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_40 = x_23;
} else {
 lean_dec_ref(x_23);
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
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_22);
if (x_43 == 0)
{
return x_22;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_ctor_get(x_22, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_22);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_49, 7);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_System_FilePath_join(x_48, x_50);
lean_dec(x_50);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_System_FilePath_join(x_51, x_53);
lean_dec(x_53);
x_55 = l_Lake_Module_recParseImports___closed__1;
x_56 = l_Lean_modToFilePath(x_54, x_19, x_55);
lean_dec(x_54);
x_57 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_58 = lean_string_append(x_57, x_56);
lean_dec(x_56);
x_59 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___closed__1;
x_60 = lean_string_append(x_58, x_59);
x_61 = 3;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_array_push(x_10, x_62);
x_64 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_65 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1(x_15, x_64, x_6, x_7, x_8, x_9, x_63, x_11);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = 1;
x_71 = lean_usize_add(x_4, x_70);
x_72 = lean_array_uset(x_17, x_4, x_68);
x_4 = x_71;
x_5 = x_72;
x_10 = x_69;
x_11 = x_67;
goto _start;
}
else
{
uint8_t x_74; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_65);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_65, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
return x_65;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_66, 0);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_66);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_65, 0, x_79);
return x_65;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
lean_dec(x_65);
x_81 = lean_ctor_get(x_66, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_66, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_83 = x_66;
} else {
 lean_dec_ref(x_66);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_65);
if (x_86 == 0)
{
return x_65;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_65, 0);
x_88 = lean_ctor_get(x_65, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_65);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dynlib", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = lean_apply_6(x_4, x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_25 = lean_array_uset(x_15, x_2, x_21);
x_2 = x_24;
x_3 = x_25;
x_8 = x_22;
x_9 = x_20;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_15);
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
lean_dec(x_15);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recBuildDeps___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recBuildDeps___spec__8___at_Lake_Module_recBuildDeps___spec__9(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_1, x_20);
lean_ctor_set(x_2, 2, x_21);
x_22 = lean_array_uset(x_1, x_20, x_2);
x_1 = x_22;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_27 = lean_array_get_size(x_1);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Name_hash___override(x_29);
lean_dec(x_29);
x_31 = 32;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = 16;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_39 = 1;
x_40 = lean_usize_sub(x_38, x_39);
x_41 = lean_usize_land(x_37, x_40);
x_42 = lean_array_uget(x_1, x_41);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_array_uset(x_1, x_41, x_43);
x_1 = x_44;
x_2 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recBuildDeps___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recBuildDeps___spec__8___at_Lake_Module_recBuildDeps___spec__9(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recBuildDeps___spec__6(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recBuildDeps___spec__7(x_7, x_1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashablePackage___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqPackage___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Name_hash___override(x_9);
lean_dec(x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_6, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__5(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_2);
x_25 = lean_array_push(x_24, x_2);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_22);
x_30 = lean_array_uset(x_6, x_21, x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_mul(x_27, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recBuildDeps___spec__6(x_30);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_3, 0, x_27);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_25);
return x_38;
}
else
{
lean_object* x_39; 
lean_ctor_set(x_3, 1, x_30);
lean_ctor_set(x_3, 0, x_27);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_25);
return x_39;
}
}
else
{
lean_dec(x_22);
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; size_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; uint8_t x_58; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_42 = lean_array_get_size(x_41);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Name_hash___override(x_44);
lean_dec(x_44);
x_46 = 32;
x_47 = lean_uint64_shift_right(x_45, x_46);
x_48 = lean_uint64_xor(x_45, x_47);
x_49 = 16;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = lean_uint64_to_usize(x_51);
x_53 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_54 = 1;
x_55 = lean_usize_sub(x_53, x_54);
x_56 = lean_usize_land(x_52, x_55);
x_57 = lean_array_uget(x_41, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__5(x_2, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_dec(x_1);
lean_inc(x_2);
x_60 = lean_array_push(x_59, x_2);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_40, x_61);
lean_dec(x_40);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_57);
x_65 = lean_array_uset(x_41, x_56, x_64);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_nat_mul(x_62, x_66);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_nat_div(x_67, x_68);
lean_dec(x_67);
x_70 = lean_array_get_size(x_65);
x_71 = lean_nat_dec_le(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recBuildDeps___spec__6(x_65);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_62);
lean_ctor_set(x_75, 1, x_65);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_60);
return x_76;
}
}
else
{
lean_dec(x_57);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4(x_4, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_array_size(x_1);
x_14 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__3(x_13, x_2, x_1);
x_15 = lean_array_size(x_3);
x_16 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__3(x_15, x_2, x_3);
x_17 = l_Array_append___rarg(x_14, x_16);
lean_dec(x_16);
x_18 = lean_array_size(x_4);
x_19 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__3(x_18, x_2, x_4);
x_20 = lean_array_size(x_5);
x_21 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__3(x_20, x_2, x_5);
x_22 = l_Array_append___rarg(x_19, x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___lambda__2___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Module_recBuildDeps___lambda__2___closed__1;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___lambda__2___closed__3___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lake_platformTrace;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_recBuildDeps___lambda__2___closed__2;
x_2 = l_Lake_Module_recBuildDeps___lambda__2___closed__3___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_5, 8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_6, 8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 1);
x_19 = l_Lake_BuildTrace_mix(x_18, x_7);
lean_ctor_set(x_13, 1, x_19);
x_20 = lean_box(0);
x_21 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_8, x_20, x_9, x_10, x_11, x_12, x_13, x_14);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_22);
lean_dec(x_13);
x_25 = l_Lake_BuildTrace_mix(x_24, x_7);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_23);
x_27 = lean_box(0);
x_28 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_8, x_27, x_9, x_10, x_11, x_12, x_26, x_14);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_unbox(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_13, 1);
x_33 = l_Lake_BuildTrace_mix(x_32, x_7);
x_34 = l_Lake_Module_recBuildDeps___lambda__2___closed__3;
x_35 = l_Lake_BuildTrace_mix(x_33, x_34);
lean_ctor_set(x_13, 1, x_35);
x_36 = lean_box(0);
x_37 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_8, x_36, x_9, x_10, x_11, x_12, x_13, x_14);
return x_37;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_38);
lean_dec(x_13);
x_41 = l_Lake_BuildTrace_mix(x_40, x_7);
x_42 = l_Lake_Module_recBuildDeps___lambda__2___closed__3;
x_43 = l_Lake_BuildTrace_mix(x_41, x_42);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_39);
x_45 = lean_box(0);
x_46 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_8, x_45, x_9, x_10, x_11, x_12, x_44, x_14);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_13);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_13, 1);
lean_dec(x_48);
lean_ctor_set(x_13, 1, x_7);
x_49 = lean_box(0);
x_50 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_8, x_49, x_9, x_10, x_11, x_12, x_13, x_14);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_7);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_52);
x_54 = lean_box(0);
x_55 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_8, x_54, x_9, x_10, x_11, x_12, x_53, x_14);
return x_55;
}
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_13, 1);
x_60 = l_Lake_BuildTrace_mix(x_59, x_7);
x_61 = l_Lake_Module_recBuildDeps___lambda__2___closed__3;
x_62 = l_Lake_BuildTrace_mix(x_60, x_61);
lean_ctor_set(x_13, 1, x_62);
x_63 = lean_box(0);
x_64 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_8, x_63, x_9, x_10, x_11, x_12, x_13, x_14);
return x_64;
}
else
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_13, 0);
x_66 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_65);
lean_dec(x_13);
x_68 = l_Lake_BuildTrace_mix(x_67, x_7);
x_69 = l_Lake_Module_recBuildDeps___lambda__2___closed__3;
x_70 = l_Lake_BuildTrace_mix(x_68, x_69);
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_box(0);
x_73 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_8, x_72, x_9, x_10, x_11, x_12, x_71, x_14);
return x_73;
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_13);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_13, 1);
lean_dec(x_75);
lean_ctor_set(x_13, 1, x_7);
x_76 = lean_box(0);
x_77 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_8, x_76, x_9, x_10, x_11, x_12, x_13, x_14);
return x_77;
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_13, 0);
x_79 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_inc(x_78);
lean_dec(x_13);
x_80 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_7);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_79);
x_81 = lean_box(0);
x_82 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_8, x_81, x_9, x_10, x_11, x_12, x_80, x_14);
return x_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_box_usize(x_2);
x_16 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2___boxed), 14, 7);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_8);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = l_Task_Priority_default;
x_19 = 0;
x_20 = l_Lake_Job_mapM___rarg(x_7, x_16, x_18, x_19, x_9, x_10, x_11, x_12, x_17, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
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
lean_ctor_set(x_26, 1, x_13);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_13);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_box_usize(x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__3___boxed), 14, 7);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = l_Task_Priority_default;
x_19 = 0;
x_20 = l_Lake_Job_bindM___rarg(x_7, x_16, x_18, x_19, x_9, x_10, x_11, x_12, x_17, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
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
lean_ctor_set(x_26, 1, x_13);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_13);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_box_usize(x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__4___boxed), 14, 7);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_8);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = l_Task_Priority_default;
x_19 = 0;
x_20 = l_Lake_Job_bindM___rarg(x_7, x_16, x_18, x_19, x_9, x_10, x_11, x_12, x_17, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
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
lean_ctor_set(x_26, 1, x_13);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_13);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lake_BuildTrace_nil;
lean_ctor_set(x_13, 1, x_17);
x_18 = lean_box_usize(x_1);
x_19 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 14, 7);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_16);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_6);
x_20 = l_Task_Priority_default;
x_21 = 0;
x_22 = l_Lake_Job_bindM___rarg(x_7, x_19, x_20, x_21, x_9, x_10, x_11, x_12, x_17, x_14);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
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
lean_ctor_set(x_28, 1, x_13);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
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
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_34);
lean_dec(x_13);
x_37 = l_Lake_BuildTrace_nil;
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_35);
x_39 = lean_box_usize(x_1);
x_40 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 14, 7);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_2);
lean_closure_set(x_40, 2, x_3);
lean_closure_set(x_40, 3, x_36);
lean_closure_set(x_40, 4, x_4);
lean_closure_set(x_40, 5, x_5);
lean_closure_set(x_40, 6, x_6);
x_41 = l_Task_Priority_default;
x_42 = 0;
x_43 = l_Lake_Job_bindM___rarg(x_7, x_40, x_41, x_42, x_9, x_10, x_11, x_12, x_37, x_14);
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
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_38);
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
lean_dec(x_38);
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
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_box_usize(x_1);
x_17 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__6___boxed), 14, 7);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_5);
lean_closure_set(x_17, 5, x_6);
lean_closure_set(x_17, 6, x_7);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = l_Task_Priority_default;
x_20 = 0;
x_21 = l_Lake_Job_bindM___rarg(x_8, x_17, x_19, x_20, x_10, x_11, x_12, x_13, x_18, x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
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
lean_ctor_set(x_27, 1, x_14);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__8(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_187; lean_object* x_188; lean_object* x_204; lean_object* x_205; lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_5, 0);
lean_inc(x_229);
lean_dec(x_5);
x_230 = lean_io_wait(x_229, x_11);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_234 = !lean_is_exclusive(x_231);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_235 = lean_ctor_get(x_231, 0);
x_236 = lean_ctor_get(x_231, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_232, 0);
lean_inc(x_237);
lean_dec(x_232);
x_238 = lean_array_get_size(x_237);
x_239 = lean_unsigned_to_nat(0u);
x_240 = lean_nat_dec_lt(x_239, x_238);
if (x_240 == 0)
{
lean_dec(x_238);
lean_dec(x_237);
lean_ctor_set(x_231, 1, x_10);
x_204 = x_231;
x_205 = x_233;
goto block_228;
}
else
{
uint8_t x_241; 
x_241 = lean_nat_dec_le(x_238, x_238);
if (x_241 == 0)
{
lean_dec(x_238);
lean_dec(x_237);
lean_ctor_set(x_231, 1, x_10);
x_204 = x_231;
x_205 = x_233;
goto block_228;
}
else
{
size_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
lean_free_object(x_231);
x_242 = lean_usize_of_nat(x_238);
lean_dec(x_238);
x_243 = lean_box(0);
x_244 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_237, x_1, x_242, x_243, x_10, x_233);
lean_dec(x_237);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = !lean_is_exclusive(x_245);
if (x_247 == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_245, 0);
lean_dec(x_248);
lean_ctor_set(x_245, 0, x_235);
x_204 = x_245;
x_205 = x_246;
goto block_228;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
lean_dec(x_245);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_235);
lean_ctor_set(x_250, 1, x_249);
x_204 = x_250;
x_205 = x_246;
goto block_228;
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_251 = lean_ctor_get(x_231, 0);
lean_inc(x_251);
lean_dec(x_231);
x_252 = lean_ctor_get(x_232, 0);
lean_inc(x_252);
lean_dec(x_232);
x_253 = lean_array_get_size(x_252);
x_254 = lean_unsigned_to_nat(0u);
x_255 = lean_nat_dec_lt(x_254, x_253);
if (x_255 == 0)
{
lean_object* x_256; 
lean_dec(x_253);
lean_dec(x_252);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_251);
lean_ctor_set(x_256, 1, x_10);
x_204 = x_256;
x_205 = x_233;
goto block_228;
}
else
{
uint8_t x_257; 
x_257 = lean_nat_dec_le(x_253, x_253);
if (x_257 == 0)
{
lean_object* x_258; 
lean_dec(x_253);
lean_dec(x_252);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_251);
lean_ctor_set(x_258, 1, x_10);
x_204 = x_258;
x_205 = x_233;
goto block_228;
}
else
{
size_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_259 = lean_usize_of_nat(x_253);
lean_dec(x_253);
x_260 = lean_box(0);
x_261 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_252, x_1, x_259, x_260, x_10, x_233);
lean_dec(x_252);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_251);
lean_ctor_set(x_266, 1, x_264);
x_204 = x_266;
x_205 = x_263;
goto block_228;
}
}
}
}
else
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_267 = lean_ctor_get(x_231, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_230, 1);
lean_inc(x_268);
lean_dec(x_230);
x_269 = !lean_is_exclusive(x_231);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_270 = lean_ctor_get(x_231, 0);
x_271 = lean_ctor_get(x_231, 1);
lean_dec(x_271);
x_272 = lean_ctor_get(x_267, 0);
lean_inc(x_272);
lean_dec(x_267);
x_273 = lean_array_get_size(x_272);
x_274 = lean_unsigned_to_nat(0u);
x_275 = lean_nat_dec_lt(x_274, x_273);
if (x_275 == 0)
{
lean_dec(x_273);
lean_dec(x_272);
lean_ctor_set(x_231, 1, x_10);
x_204 = x_231;
x_205 = x_268;
goto block_228;
}
else
{
uint8_t x_276; 
x_276 = lean_nat_dec_le(x_273, x_273);
if (x_276 == 0)
{
lean_dec(x_273);
lean_dec(x_272);
lean_ctor_set(x_231, 1, x_10);
x_204 = x_231;
x_205 = x_268;
goto block_228;
}
else
{
size_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_free_object(x_231);
x_277 = lean_usize_of_nat(x_273);
lean_dec(x_273);
x_278 = lean_box(0);
x_279 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_272, x_1, x_277, x_278, x_10, x_268);
lean_dec(x_272);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = !lean_is_exclusive(x_280);
if (x_282 == 0)
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_280, 0);
lean_dec(x_283);
lean_ctor_set_tag(x_280, 1);
lean_ctor_set(x_280, 0, x_270);
x_204 = x_280;
x_205 = x_281;
goto block_228;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_280, 1);
lean_inc(x_284);
lean_dec(x_280);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_270);
lean_ctor_set(x_285, 1, x_284);
x_204 = x_285;
x_205 = x_281;
goto block_228;
}
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_286 = lean_ctor_get(x_231, 0);
lean_inc(x_286);
lean_dec(x_231);
x_287 = lean_ctor_get(x_267, 0);
lean_inc(x_287);
lean_dec(x_267);
x_288 = lean_array_get_size(x_287);
x_289 = lean_unsigned_to_nat(0u);
x_290 = lean_nat_dec_lt(x_289, x_288);
if (x_290 == 0)
{
lean_object* x_291; 
lean_dec(x_288);
lean_dec(x_287);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_286);
lean_ctor_set(x_291, 1, x_10);
x_204 = x_291;
x_205 = x_268;
goto block_228;
}
else
{
uint8_t x_292; 
x_292 = lean_nat_dec_le(x_288, x_288);
if (x_292 == 0)
{
lean_object* x_293; 
lean_dec(x_288);
lean_dec(x_287);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_286);
lean_ctor_set(x_293, 1, x_10);
x_204 = x_293;
x_205 = x_268;
goto block_228;
}
else
{
size_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_294 = lean_usize_of_nat(x_288);
lean_dec(x_288);
x_295 = lean_box(0);
x_296 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_287, x_1, x_294, x_295, x_10, x_268);
lean_dec(x_287);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_300 = x_297;
} else {
 lean_dec_ref(x_297);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
 lean_ctor_set_tag(x_301, 1);
}
lean_ctor_set(x_301, 0, x_286);
lean_ctor_set(x_301, 1, x_299);
x_204 = x_301;
x_205 = x_298;
goto block_228;
}
}
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_302 = !lean_is_exclusive(x_230);
if (x_302 == 0)
{
return x_230;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_230, 0);
x_304 = lean_ctor_get(x_230, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_230);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
block_186:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_array_size(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_17 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(x_16, x_1, x_14, x_6, x_7, x_8, x_9, x_15, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lake_Job_collectArray___rarg(x_20);
lean_dec(x_20);
x_133 = lean_array_get_size(x_14);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_nat_dec_lt(x_134, x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_133);
lean_dec(x_14);
x_136 = lean_ctor_get(x_2, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 2);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_137, sizeof(void*)*29);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_2, 1);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_139, sizeof(void*)*9);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_136);
x_141 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_23 = x_141;
goto block_132;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_143 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4(x_142, x_136);
x_23 = x_143;
goto block_132;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_145 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4(x_144, x_136);
x_23 = x_145;
goto block_132;
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_2, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_146, 2);
lean_inc(x_147);
x_148 = lean_ctor_get_uint8(x_147, sizeof(void*)*29);
lean_dec(x_147);
x_149 = lean_nat_dec_le(x_133, x_133);
if (x_149 == 0)
{
lean_dec(x_133);
lean_dec(x_14);
if (x_148 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_2, 1);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_150, sizeof(void*)*9);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_146);
x_152 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_23 = x_152;
goto block_132;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_154 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4(x_153, x_146);
x_23 = x_154;
goto block_132;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_156 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4(x_155, x_146);
x_23 = x_156;
goto block_132;
}
}
else
{
size_t x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_usize_of_nat(x_133);
lean_dec(x_133);
x_158 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_159 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__10(x_14, x_1, x_157, x_158);
lean_dec(x_14);
if (x_148 == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_2, 1);
lean_inc(x_160);
x_161 = lean_ctor_get_uint8(x_160, sizeof(void*)*9);
lean_dec(x_160);
if (x_161 == 0)
{
lean_dec(x_146);
x_23 = x_159;
goto block_132;
}
else
{
lean_object* x_162; 
x_162 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4(x_159, x_146);
x_23 = x_162;
goto block_132;
}
}
else
{
lean_object* x_163; 
x_163 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4(x_159, x_146);
x_23 = x_163;
goto block_132;
}
}
}
block_132:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lake_fetchExternLibs(x_24, x_6, x_7, x_8, x_9, x_21, x_19);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 9);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 9);
lean_inc(x_36);
x_37 = l_Array_append___rarg(x_33, x_36);
lean_dec(x_36);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_38 = l_Lake_TargetArray_fetch___rarg(x_37, x_6, x_7, x_8, x_9, x_29, x_27);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_32, 10);
lean_inc(x_43);
x_44 = lean_ctor_get(x_35, 10);
lean_inc(x_44);
x_45 = l_Array_append___rarg(x_43, x_44);
lean_dec(x_44);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lake_TargetArray_fetch___rarg(x_45, x_6, x_7, x_8, x_9, x_42, x_40);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 1);
x_52 = lean_box_usize(x_1);
x_53 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__7___boxed), 15, 8);
lean_closure_set(x_53, 0, x_52);
lean_closure_set(x_53, 1, x_35);
lean_closure_set(x_53, 2, x_32);
lean_closure_set(x_53, 3, x_50);
lean_closure_set(x_53, 4, x_41);
lean_closure_set(x_53, 5, x_28);
lean_closure_set(x_53, 6, x_22);
lean_closure_set(x_53, 7, x_3);
x_54 = l_Task_Priority_default;
x_55 = 0;
x_56 = l_Lake_BuildTrace_nil;
x_57 = l_Lake_Job_bindM___rarg(x_4, x_53, x_54, x_55, x_6, x_7, x_8, x_9, x_56, x_48);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_ctor_set(x_47, 0, x_59);
lean_ctor_set(x_57, 0, x_47);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_57);
lean_ctor_set(x_47, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_47);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_free_object(x_47);
lean_dec(x_51);
x_63 = !lean_is_exclusive(x_57);
if (x_63 == 0)
{
return x_57;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_57, 0);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_57);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_47, 0);
x_68 = lean_ctor_get(x_47, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_47);
x_69 = lean_box_usize(x_1);
x_70 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__7___boxed), 15, 8);
lean_closure_set(x_70, 0, x_69);
lean_closure_set(x_70, 1, x_35);
lean_closure_set(x_70, 2, x_32);
lean_closure_set(x_70, 3, x_67);
lean_closure_set(x_70, 4, x_41);
lean_closure_set(x_70, 5, x_28);
lean_closure_set(x_70, 6, x_22);
lean_closure_set(x_70, 7, x_3);
x_71 = l_Task_Priority_default;
x_72 = 0;
x_73 = l_Lake_BuildTrace_nil;
x_74 = l_Lake_Job_bindM___rarg(x_4, x_70, x_71, x_72, x_6, x_7, x_8, x_9, x_73, x_48);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
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
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_68);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_68);
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
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_46);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_46, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_47);
if (x_86 == 0)
{
return x_46;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_47, 0);
x_88 = lean_ctor_get(x_47, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_47);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_46, 0, x_89);
return x_46;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_46, 1);
lean_inc(x_90);
lean_dec(x_46);
x_91 = lean_ctor_get(x_47, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_47, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_93 = x_47;
} else {
 lean_dec_ref(x_47);
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
else
{
uint8_t x_96; 
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
return x_46;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_46, 0);
x_98 = lean_ctor_get(x_46, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_46);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_38);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_38, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_39);
if (x_102 == 0)
{
return x_38;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_39, 0);
x_104 = lean_ctor_get(x_39, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_39);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_38, 0, x_105);
return x_38;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 1);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_39, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_39, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_109 = x_39;
} else {
 lean_dec_ref(x_39);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_38);
if (x_112 == 0)
{
return x_38;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_38, 0);
x_114 = lean_ctor_get(x_38, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_38);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = !lean_is_exclusive(x_25);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_25, 0);
lean_dec(x_117);
x_118 = !lean_is_exclusive(x_26);
if (x_118 == 0)
{
return x_25;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_26, 0);
x_120 = lean_ctor_get(x_26, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_26);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_25, 0, x_121);
return x_25;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_122 = lean_ctor_get(x_25, 1);
lean_inc(x_122);
lean_dec(x_25);
x_123 = lean_ctor_get(x_26, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_26, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_125 = x_26;
} else {
 lean_dec_ref(x_26);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_122);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_25);
if (x_128 == 0)
{
return x_25;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_25, 0);
x_130 = lean_ctor_get(x_25, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_25);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_17);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_17, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_18);
if (x_166 == 0)
{
return x_17;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_18, 0);
x_168 = lean_ctor_get(x_18, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_18);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_17, 0, x_169);
return x_17;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_170 = lean_ctor_get(x_17, 1);
lean_inc(x_170);
lean_dec(x_17);
x_171 = lean_ctor_get(x_18, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_18, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_173 = x_18;
} else {
 lean_dec_ref(x_18);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_176 = !lean_is_exclusive(x_17);
if (x_176 == 0)
{
return x_17;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_17, 0);
x_178 = lean_ctor_get(x_17, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_17);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_12);
if (x_180 == 0)
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_12);
lean_ctor_set(x_181, 1, x_13);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_12, 0);
x_183 = lean_ctor_get(x_12, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_12);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_13);
return x_185;
}
}
}
block_203:
{
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_187);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_187, 1);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec(x_190);
lean_ctor_set(x_187, 1, x_191);
x_12 = x_187;
x_13 = x_188;
goto block_186;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_187, 0);
x_193 = lean_ctor_get(x_187, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_187);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_194);
x_12 = x_195;
x_13 = x_188;
goto block_186;
}
}
else
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_187);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_187, 1);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec(x_197);
lean_ctor_set(x_187, 1, x_198);
x_12 = x_187;
x_13 = x_188;
goto block_186;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_187, 0);
x_200 = lean_ctor_get(x_187, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_187);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_201);
x_12 = x_202;
x_13 = x_188;
goto block_186;
}
}
}
block_228:
{
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_204);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_204, 1);
x_208 = 0;
x_209 = l_Lake_BuildTrace_nil;
x_210 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*2, x_208);
lean_ctor_set(x_204, 1, x_210);
x_187 = x_204;
x_188 = x_205;
goto block_203;
}
else
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_204, 0);
x_212 = lean_ctor_get(x_204, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_204);
x_213 = 0;
x_214 = l_Lake_BuildTrace_nil;
x_215 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*2, x_213);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_211);
lean_ctor_set(x_216, 1, x_215);
x_187 = x_216;
x_188 = x_205;
goto block_203;
}
}
else
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_204);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_204, 1);
x_219 = 0;
x_220 = l_Lake_BuildTrace_nil;
x_221 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set_uint8(x_221, sizeof(void*)*2, x_219);
lean_ctor_set(x_204, 1, x_221);
x_187 = x_204;
x_188 = x_205;
goto block_203;
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_204, 0);
x_223 = lean_ctor_get(x_204, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_204);
x_224 = 0;
x_225 = l_Lake_BuildTrace_nil;
x_226 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*2, x_224);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_222);
lean_ctor_set(x_227, 1, x_226);
x_187 = x_227;
x_188 = x_205;
goto block_203;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_122; lean_object* x_123; lean_object* x_139; lean_object* x_140; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = l_Lake_Module_importsFacetConfig___closed__2;
lean_inc(x_1);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_164);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_166 = lean_apply_6(x_4, x_165, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_io_wait(x_171, x_168);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = !lean_is_exclusive(x_173);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_177 = lean_ctor_get(x_173, 0);
x_178 = lean_ctor_get(x_173, 1);
lean_dec(x_178);
x_179 = lean_ctor_get(x_174, 0);
lean_inc(x_179);
lean_dec(x_174);
x_180 = lean_array_get_size(x_179);
x_181 = lean_unsigned_to_nat(0u);
x_182 = lean_nat_dec_lt(x_181, x_180);
if (x_182 == 0)
{
lean_dec(x_180);
lean_dec(x_179);
lean_ctor_set(x_173, 1, x_170);
x_139 = x_173;
x_140 = x_175;
goto block_163;
}
else
{
uint8_t x_183; 
x_183 = lean_nat_dec_le(x_180, x_180);
if (x_183 == 0)
{
lean_dec(x_180);
lean_dec(x_179);
lean_ctor_set(x_173, 1, x_170);
x_139 = x_173;
x_140 = x_175;
goto block_163;
}
else
{
size_t x_184; size_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
lean_free_object(x_173);
x_184 = 0;
x_185 = lean_usize_of_nat(x_180);
lean_dec(x_180);
x_186 = lean_box(0);
x_187 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_179, x_184, x_185, x_186, x_170, x_175);
lean_dec(x_179);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = !lean_is_exclusive(x_188);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_188, 0);
lean_dec(x_191);
lean_ctor_set(x_188, 0, x_177);
x_139 = x_188;
x_140 = x_189;
goto block_163;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
lean_dec(x_188);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_177);
lean_ctor_set(x_193, 1, x_192);
x_139 = x_193;
x_140 = x_189;
goto block_163;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_194 = lean_ctor_get(x_173, 0);
lean_inc(x_194);
lean_dec(x_173);
x_195 = lean_ctor_get(x_174, 0);
lean_inc(x_195);
lean_dec(x_174);
x_196 = lean_array_get_size(x_195);
x_197 = lean_unsigned_to_nat(0u);
x_198 = lean_nat_dec_lt(x_197, x_196);
if (x_198 == 0)
{
lean_object* x_199; 
lean_dec(x_196);
lean_dec(x_195);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_170);
x_139 = x_199;
x_140 = x_175;
goto block_163;
}
else
{
uint8_t x_200; 
x_200 = lean_nat_dec_le(x_196, x_196);
if (x_200 == 0)
{
lean_object* x_201; 
lean_dec(x_196);
lean_dec(x_195);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_170);
x_139 = x_201;
x_140 = x_175;
goto block_163;
}
else
{
size_t x_202; size_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_202 = 0;
x_203 = lean_usize_of_nat(x_196);
lean_dec(x_196);
x_204 = lean_box(0);
x_205 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_195, x_202, x_203, x_204, x_170, x_175);
lean_dec(x_195);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_194);
lean_ctor_set(x_210, 1, x_208);
x_139 = x_210;
x_140 = x_207;
goto block_163;
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_211 = lean_ctor_get(x_173, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_172, 1);
lean_inc(x_212);
lean_dec(x_172);
x_213 = !lean_is_exclusive(x_173);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_214 = lean_ctor_get(x_173, 0);
x_215 = lean_ctor_get(x_173, 1);
lean_dec(x_215);
x_216 = lean_ctor_get(x_211, 0);
lean_inc(x_216);
lean_dec(x_211);
x_217 = lean_array_get_size(x_216);
x_218 = lean_unsigned_to_nat(0u);
x_219 = lean_nat_dec_lt(x_218, x_217);
if (x_219 == 0)
{
lean_dec(x_217);
lean_dec(x_216);
lean_ctor_set(x_173, 1, x_170);
x_139 = x_173;
x_140 = x_212;
goto block_163;
}
else
{
uint8_t x_220; 
x_220 = lean_nat_dec_le(x_217, x_217);
if (x_220 == 0)
{
lean_dec(x_217);
lean_dec(x_216);
lean_ctor_set(x_173, 1, x_170);
x_139 = x_173;
x_140 = x_212;
goto block_163;
}
else
{
size_t x_221; size_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_free_object(x_173);
x_221 = 0;
x_222 = lean_usize_of_nat(x_217);
lean_dec(x_217);
x_223 = lean_box(0);
x_224 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_216, x_221, x_222, x_223, x_170, x_212);
lean_dec(x_216);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = !lean_is_exclusive(x_225);
if (x_227 == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_225, 0);
lean_dec(x_228);
lean_ctor_set_tag(x_225, 1);
lean_ctor_set(x_225, 0, x_214);
x_139 = x_225;
x_140 = x_226;
goto block_163;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_225, 1);
lean_inc(x_229);
lean_dec(x_225);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_214);
lean_ctor_set(x_230, 1, x_229);
x_139 = x_230;
x_140 = x_226;
goto block_163;
}
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_231 = lean_ctor_get(x_173, 0);
lean_inc(x_231);
lean_dec(x_173);
x_232 = lean_ctor_get(x_211, 0);
lean_inc(x_232);
lean_dec(x_211);
x_233 = lean_array_get_size(x_232);
x_234 = lean_unsigned_to_nat(0u);
x_235 = lean_nat_dec_lt(x_234, x_233);
if (x_235 == 0)
{
lean_object* x_236; 
lean_dec(x_233);
lean_dec(x_232);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_231);
lean_ctor_set(x_236, 1, x_170);
x_139 = x_236;
x_140 = x_212;
goto block_163;
}
else
{
uint8_t x_237; 
x_237 = lean_nat_dec_le(x_233, x_233);
if (x_237 == 0)
{
lean_object* x_238; 
lean_dec(x_233);
lean_dec(x_232);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_231);
lean_ctor_set(x_238, 1, x_170);
x_139 = x_238;
x_140 = x_212;
goto block_163;
}
else
{
size_t x_239; size_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_239 = 0;
x_240 = lean_usize_of_nat(x_233);
lean_dec(x_233);
x_241 = lean_box(0);
x_242 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_232, x_239, x_240, x_241, x_170, x_212);
lean_dec(x_232);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
 lean_ctor_set_tag(x_247, 1);
}
lean_ctor_set(x_247, 0, x_231);
lean_ctor_set(x_247, 1, x_245);
x_139 = x_247;
x_140 = x_244;
goto block_163;
}
}
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_170);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_248 = !lean_is_exclusive(x_172);
if (x_248 == 0)
{
return x_172;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_172, 0);
x_250 = lean_ctor_get(x_172, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_172);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_166);
if (x_252 == 0)
{
lean_object* x_253; uint8_t x_254; 
x_253 = lean_ctor_get(x_166, 0);
lean_dec(x_253);
x_254 = !lean_is_exclusive(x_167);
if (x_254 == 0)
{
return x_166;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_167, 0);
x_256 = lean_ctor_get(x_167, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_167);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set(x_166, 0, x_257);
return x_166;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_258 = lean_ctor_get(x_166, 1);
lean_inc(x_258);
lean_dec(x_166);
x_259 = lean_ctor_get(x_167, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_167, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_261 = x_167;
} else {
 lean_dec_ref(x_167);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_258);
return x_263;
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_264 = !lean_is_exclusive(x_166);
if (x_264 == 0)
{
return x_166;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_166, 0);
x_266 = lean_ctor_get(x_166, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_166);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
block_121:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_array_size(x_12);
x_15 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_16 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(x_1, x_2, x_14, x_15, x_12, x_4, x_5, x_6, x_7, x_13, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lake_Job_mixArray___rarg(x_19);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*29);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*9);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = lean_apply_6(x_4, x_28, x_5, x_6, x_7, x_20, x_18);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Lake_Module_recBuildDeps___lambda__8(x_15, x_2, x_21, x_3, x_32, x_4, x_5, x_6, x_7, x_33, x_31);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_30, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_44 = x_30;
} else {
 lean_dec_ref(x_30);
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
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
return x_29;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_29, 0);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_29);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_53 = lean_apply_6(x_4, x_52, x_5, x_6, x_7, x_20, x_18);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l_Lake_Module_recBuildDeps___lambda__8(x_15, x_2, x_21, x_3, x_56, x_4, x_5, x_6, x_7, x_57, x_55);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_53, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_54);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_53, 0, x_64);
return x_53;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_ctor_get(x_54, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_54, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_68 = x_54;
} else {
 lean_dec_ref(x_54);
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
uint8_t x_71; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_53);
if (x_71 == 0)
{
return x_53;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_53, 0);
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_53);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_77 = lean_apply_6(x_4, x_76, x_5, x_6, x_7, x_20, x_18);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l_Lake_Module_recBuildDeps___lambda__8(x_15, x_2, x_21, x_3, x_80, x_4, x_5, x_6, x_7, x_81, x_79);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_77);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_77, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_78);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_78, 0);
x_87 = lean_ctor_get(x_78, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_78);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_77, 0, x_88);
return x_77;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_77, 1);
lean_inc(x_89);
lean_dec(x_77);
x_90 = lean_ctor_get(x_78, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_78, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_92 = x_78;
} else {
 lean_dec_ref(x_78);
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
else
{
uint8_t x_95; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_77);
if (x_95 == 0)
{
return x_77;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_77, 0);
x_97 = lean_ctor_get(x_77, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_77);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_16);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_16, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_17);
if (x_101 == 0)
{
return x_16;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_17, 0);
x_103 = lean_ctor_get(x_17, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_17);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_16, 0, x_104);
return x_16;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_16, 1);
lean_inc(x_105);
lean_dec(x_16);
x_106 = lean_ctor_get(x_17, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_17, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_108 = x_17;
} else {
 lean_dec_ref(x_17);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_105);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_16);
if (x_111 == 0)
{
return x_16;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_16, 0);
x_113 = lean_ctor_get(x_16, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_16);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_10);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_10);
lean_ctor_set(x_116, 1, x_11);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_10, 0);
x_118 = lean_ctor_get(x_10, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_10);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_11);
return x_120;
}
}
}
block_138:
{
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_122, 1);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
lean_ctor_set(x_122, 1, x_126);
x_10 = x_122;
x_11 = x_123;
goto block_121;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_122, 0);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_122);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
x_10 = x_130;
x_11 = x_123;
goto block_121;
}
}
else
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_122);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_122, 1);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
lean_ctor_set(x_122, 1, x_133);
x_10 = x_122;
x_11 = x_123;
goto block_121;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_122, 0);
x_135 = lean_ctor_get(x_122, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_122);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_136);
x_10 = x_137;
x_11 = x_123;
goto block_121;
}
}
}
block_163:
{
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_139);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_139, 1);
x_143 = 0;
x_144 = l_Lake_BuildTrace_nil;
x_145 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_143);
lean_ctor_set(x_139, 1, x_145);
x_122 = x_139;
x_123 = x_140;
goto block_138;
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_139, 0);
x_147 = lean_ctor_get(x_139, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_139);
x_148 = 0;
x_149 = l_Lake_BuildTrace_nil;
x_150 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set_uint8(x_150, sizeof(void*)*2, x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set(x_151, 1, x_150);
x_122 = x_151;
x_123 = x_140;
goto block_138;
}
}
else
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_139);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_139, 1);
x_154 = 0;
x_155 = l_Lake_BuildTrace_nil;
x_156 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*2, x_154);
lean_ctor_set(x_139, 1, x_156);
x_122 = x_139;
x_123 = x_140;
goto block_138;
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_139, 0);
x_158 = lean_ctor_get(x_139, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_139);
x_159 = 0;
x_160 = l_Lake_BuildTrace_nil;
x_161 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_159);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_157);
lean_ctor_set(x_162, 1, x_161);
x_122 = x_162;
x_123 = x_140;
goto block_138;
}
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extraDep", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_recBuildDeps___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lake_Module_recBuildDeps___closed__2;
lean_inc(x_8);
x_10 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, lean_box(0));
x_12 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__9), 9, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_8);
x_13 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg), 8, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lake_ensureJob___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = l_Lake_Module_recBuildDeps___lambda__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = l_Lake_Module_recBuildDeps___lambda__3(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_16 = l_Lake_Module_recBuildDeps___lambda__4(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_16 = l_Lake_Module_recBuildDeps___lambda__5(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_16 = l_Lake_Module_recBuildDeps___lambda__6(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; lean_object* x_17; 
x_16 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_17 = l_Lake_Module_recBuildDeps___lambda__7(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; lean_object* x_13; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = l_Lake_Module_recBuildDeps___lambda__8(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_nullFormat___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("deps", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_depsFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_depsFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_depsFacetConfig___closed__3;
x_2 = 1;
x_3 = l_Lake_Module_depsFacetConfig___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_depsFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_depsFacetConfig___elambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_clearOutputHashes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ilean", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_clearOutputHashes___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c", 1, 1);
return x_1;
}
}
static uint8_t _init_l_Lake_Module_clearOutputHashes___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_has_llvm_backend(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_clearOutputHashes___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bc", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_clearOutputHashes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 8);
lean_inc(x_7);
x_8 = l_System_FilePath_join(x_5, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 9);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_System_FilePath_join(x_8, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
x_13 = l_Lean_modToFilePath(x_10, x_11, x_12);
x_14 = l_Lake_clearFileHash(x_13, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lake_Module_clearOutputHashes___closed__1;
x_17 = l_Lean_modToFilePath(x_10, x_11, x_16);
lean_dec(x_10);
x_18 = l_Lake_clearFileHash(x_17, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_6, 12);
lean_inc(x_20);
lean_dec(x_6);
x_21 = l_System_FilePath_join(x_8, x_20);
lean_dec(x_20);
x_22 = l_Lake_Module_clearOutputHashes___closed__2;
x_23 = l_Lean_modToFilePath(x_21, x_11, x_22);
x_24 = l_Lake_clearFileHash(x_23, x_19);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = l_Lake_Module_clearOutputHashes___closed__3;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_21);
lean_dec(x_11);
x_29 = lean_box(0);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_24);
x_30 = l_Lake_Module_clearOutputHashes___closed__4;
x_31 = l_Lean_modToFilePath(x_21, x_11, x_30);
lean_dec(x_11);
lean_dec(x_21);
x_32 = l_Lake_clearFileHash(x_31, x_26);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = l_Lake_Module_clearOutputHashes___closed__3;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
lean_dec(x_11);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lake_Module_clearOutputHashes___closed__4;
x_38 = l_Lean_modToFilePath(x_21, x_11, x_37);
lean_dec(x_11);
lean_dec(x_21);
x_39 = l_Lake_clearFileHash(x_38, x_33);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_21);
lean_dec(x_11);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_24, 0);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_24);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_18);
if (x_44 == 0)
{
return x_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
return x_14;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cacheOutputHashes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 8);
lean_inc(x_7);
x_8 = l_System_FilePath_join(x_5, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 9);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_System_FilePath_join(x_8, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
x_13 = l_Lean_modToFilePath(x_10, x_11, x_12);
x_14 = l_Lake_cacheFileHash(x_13, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lake_Module_clearOutputHashes___closed__1;
x_17 = l_Lean_modToFilePath(x_10, x_11, x_16);
lean_dec(x_10);
x_18 = l_Lake_cacheFileHash(x_17, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_6, 12);
lean_inc(x_20);
lean_dec(x_6);
x_21 = l_System_FilePath_join(x_8, x_20);
lean_dec(x_20);
x_22 = l_Lake_Module_clearOutputHashes___closed__2;
x_23 = l_Lean_modToFilePath(x_21, x_11, x_22);
x_24 = l_Lake_cacheFileHash(x_23, x_19);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = l_Lake_Module_clearOutputHashes___closed__3;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_21);
lean_dec(x_11);
x_29 = lean_box(0);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_24);
x_30 = l_Lake_Module_clearOutputHashes___closed__4;
x_31 = l_Lean_modToFilePath(x_21, x_11, x_30);
lean_dec(x_11);
lean_dec(x_21);
x_32 = l_Lake_cacheFileHash(x_31, x_26);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = l_Lake_Module_clearOutputHashes___closed__3;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
lean_dec(x_11);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lake_Module_clearOutputHashes___closed__4;
x_38 = l_Lean_modToFilePath(x_21, x_11, x_37);
lean_dec(x_11);
lean_dec(x_21);
x_39 = l_Lake_cacheFileHash(x_38, x_33);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_21);
lean_dec(x_11);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_24, 0);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_24);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_18);
if (x_44 == 0)
{
return x_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
return x_14;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Module_getMTime(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lake_MTime_instOrd;
x_8 = l_Ord_instDecidableRelLt___rarg(x_7, x_2, x_6);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = l_Lake_MTime_instOrd;
x_13 = l_Ord_instDecidableRelLt___rarg(x_12, x_2, x_10);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate_x27___spec__5(x_13, x_3);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_21);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_22);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_1, x_4, x_9);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_31);
lean_ctor_set(x_29, 0, x_2);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_35);
lean_dec(x_8);
x_38 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_1, x_4, x_9);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_36);
lean_ctor_set(x_2, 1, x_42);
lean_ctor_set(x_2, 0, x_39);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lake_Module_checkExists(x_1, x_9);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_47);
lean_ctor_set(x_45, 0, x_2);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_45);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_8, 0);
x_52 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_53 = lean_ctor_get(x_8, 1);
lean_inc(x_53);
lean_inc(x_51);
lean_dec(x_8);
x_54 = l_Lake_Module_checkExists(x_1, x_9);
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
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_52);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_55);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
lean_dec(x_2);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate_x27___spec__5(x_61, x_3);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_7, 0);
x_64 = lean_ctor_get_uint8(x_63, sizeof(void*)*1);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_4);
lean_dec(x_1);
x_65 = lean_ctor_get(x_8, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_68 = x_8;
} else {
 lean_dec_ref(x_8);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 1);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_66);
x_70 = 0;
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_9);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_8, 0);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_76 = lean_ctor_get(x_8, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_77 = x_8;
} else {
 lean_dec_ref(x_8);
 x_77 = lean_box(0);
}
x_78 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_1, x_4, x_9);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_82 = lean_alloc_ctor(0, 2, 1);
} else {
 x_82 = x_77;
}
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
else
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_4);
x_85 = lean_ctor_get(x_8, 0);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_88 = x_8;
} else {
 lean_dec_ref(x_8);
 x_88 = lean_box(0);
}
x_89 = l_Lake_Module_checkExists(x_1, x_9);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(0, 2, 1);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set_uint8(x_93, sizeof(void*)*2, x_86);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; uint8_t x_97; 
x_97 = !lean_is_exclusive(x_18);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_98 = lean_ctor_get(x_18, 0);
x_99 = lean_ctor_get(x_17, 1);
lean_inc(x_99);
lean_dec(x_17);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get(x_101, 7);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
x_104 = l_Lean_modToFilePath(x_1, x_2, x_103);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lake_Module_clearOutputHashes___closed__1;
x_107 = l_Lean_modToFilePath(x_1, x_2, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_ctor_get(x_3, 12);
x_110 = l_System_FilePath_join(x_4, x_109);
x_111 = l_Lake_Module_clearOutputHashes___closed__2;
x_112 = l_Lean_modToFilePath(x_110, x_2, x_111);
lean_dec(x_110);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
lean_inc(x_5);
x_114 = l_Lake_Module_bcFile_x3f(x_5);
x_115 = lean_ctor_get(x_6, 2);
lean_inc(x_115);
lean_dec(x_6);
x_116 = lean_ctor_get(x_7, 2);
x_117 = l_Array_append___rarg(x_115, x_116);
x_118 = l_Array_append___rarg(x_117, x_8);
x_119 = l_Lake_compileLeanModule(x_9, x_105, x_108, x_113, x_114, x_13, x_10, x_11, x_12, x_118, x_102, x_98, x_19);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_108);
lean_dec(x_105);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_120, 1);
lean_ctor_set(x_18, 0, x_123);
lean_ctor_set(x_120, 1, x_18);
x_20 = x_120;
x_21 = x_121;
goto block_96;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_120, 0);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_120);
lean_ctor_set(x_18, 0, x_125);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_18);
x_20 = x_126;
x_21 = x_121;
goto block_96;
}
}
else
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_119, 1);
lean_inc(x_127);
lean_dec(x_119);
x_128 = !lean_is_exclusive(x_120);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_120, 1);
lean_ctor_set(x_18, 0, x_129);
lean_ctor_set(x_120, 1, x_18);
x_20 = x_120;
x_21 = x_127;
goto block_96;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_120, 0);
x_131 = lean_ctor_get(x_120, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_120);
lean_ctor_set(x_18, 0, x_131);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_18);
x_20 = x_132;
x_21 = x_127;
goto block_96;
}
}
}
else
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_133 = lean_ctor_get(x_18, 0);
x_134 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
x_135 = lean_ctor_get(x_18, 1);
lean_inc(x_135);
lean_inc(x_133);
lean_dec(x_18);
x_136 = lean_ctor_get(x_17, 1);
lean_inc(x_136);
lean_dec(x_17);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_ctor_get(x_138, 7);
lean_inc(x_139);
lean_dec(x_138);
x_140 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
x_141 = l_Lean_modToFilePath(x_1, x_2, x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Lake_Module_clearOutputHashes___closed__1;
x_144 = l_Lean_modToFilePath(x_1, x_2, x_143);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_ctor_get(x_3, 12);
x_147 = l_System_FilePath_join(x_4, x_146);
x_148 = l_Lake_Module_clearOutputHashes___closed__2;
x_149 = l_Lean_modToFilePath(x_147, x_2, x_148);
lean_dec(x_147);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
lean_inc(x_5);
x_151 = l_Lake_Module_bcFile_x3f(x_5);
x_152 = lean_ctor_get(x_6, 2);
lean_inc(x_152);
lean_dec(x_6);
x_153 = lean_ctor_get(x_7, 2);
x_154 = l_Array_append___rarg(x_152, x_153);
x_155 = l_Array_append___rarg(x_154, x_8);
x_156 = l_Lake_compileLeanModule(x_9, x_142, x_145, x_150, x_151, x_13, x_10, x_11, x_12, x_155, x_139, x_133, x_19);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_145);
lean_dec(x_142);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_161 = x_157;
} else {
 lean_dec_ref(x_157);
 x_161 = lean_box(0);
}
x_162 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_135);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_134);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_162);
x_20 = x_163;
x_21 = x_158;
goto block_96;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_164 = lean_ctor_get(x_156, 1);
lean_inc(x_164);
lean_dec(x_156);
x_165 = lean_ctor_get(x_157, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_157, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_167 = x_157;
} else {
 lean_dec_ref(x_157);
 x_167 = lean_box(0);
}
x_168 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_135);
lean_ctor_set_uint8(x_168, sizeof(void*)*2, x_134);
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_167;
}
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_168);
x_20 = x_169;
x_21 = x_164;
goto block_96;
}
}
block_96:
{
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = l_Lake_Module_clearOutputHashes(x_5, x_21);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_20, 0, x_29);
lean_ctor_set(x_27, 0, x_20);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_20, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_io_error_to_string(x_34);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_get_size(x_26);
x_39 = lean_array_push(x_26, x_37);
lean_ctor_set(x_23, 0, x_39);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_38);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_20);
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_io_error_to_string(x_40);
x_43 = 3;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_array_get_size(x_26);
x_46 = lean_array_push(x_26, x_44);
lean_ctor_set(x_23, 0, x_46);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_23, 0);
x_49 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_50 = lean_ctor_get(x_23, 1);
lean_inc(x_50);
lean_inc(x_48);
lean_dec(x_23);
x_51 = l_Lake_Module_clearOutputHashes(x_5, x_21);
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
x_55 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_49);
lean_ctor_set(x_20, 1, x_55);
lean_ctor_set(x_20, 0, x_52);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_20);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
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
x_60 = lean_io_error_to_string(x_57);
x_61 = 3;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_array_get_size(x_48);
x_64 = lean_array_push(x_48, x_62);
x_65 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_49);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_65);
lean_ctor_set(x_20, 0, x_63);
if (lean_is_scalar(x_59)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_59;
 lean_ctor_set_tag(x_66, 0);
}
lean_ctor_set(x_66, 0, x_20);
lean_ctor_set(x_66, 1, x_58);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_20, 1);
lean_inc(x_67);
lean_dec(x_20);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_67, sizeof(void*)*2);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
x_72 = l_Lake_Module_clearOutputHashes(x_5, x_21);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
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
if (lean_is_scalar(x_71)) {
 x_76 = lean_alloc_ctor(0, 2, 1);
} else {
 x_76 = x_71;
}
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_69);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_76);
if (lean_is_scalar(x_75)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_75;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
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
x_82 = lean_io_error_to_string(x_79);
x_83 = 3;
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = lean_array_get_size(x_68);
x_86 = lean_array_push(x_68, x_84);
if (lean_is_scalar(x_71)) {
 x_87 = lean_alloc_ctor(0, 2, 1);
} else {
 x_87 = x_71;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_70);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_69);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_81)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_81;
 lean_ctor_set_tag(x_89, 0);
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_80);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_5);
x_90 = !lean_is_exclusive(x_20);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_20);
lean_ctor_set(x_91, 1, x_21);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_20, 0);
x_93 = lean_ctor_get(x_20, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_20);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_21);
return x_95;
}
}
}
}
}
static lean_object* _init_l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Workspace_leanPath___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_instMonadStateOfLogJobM___spec__1___rarg), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, uint8_t x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_284; 
x_24 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1___boxed), 19, 12);
lean_closure_set(x_24, 0, x_13);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_6);
lean_closure_set(x_24, 3, x_12);
lean_closure_set(x_24, 4, x_1);
lean_closure_set(x_24, 5, x_7);
lean_closure_set(x_24, 6, x_8);
lean_closure_set(x_24, 7, x_11);
lean_closure_set(x_24, 8, x_10);
lean_closure_set(x_24, 9, x_9);
lean_closure_set(x_24, 10, x_4);
lean_closure_set(x_24, 11, x_5);
x_25 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__2;
x_26 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 8, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_24);
x_284 = !lean_is_exclusive(x_22);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_285 = lean_ctor_get(x_22, 0);
x_286 = l_System_FilePath_pathExists(x_16, x_23);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_unbox(x_287);
lean_dec(x_287);
if (x_288 == 0)
{
uint8_t x_289; 
lean_dec(x_18);
x_289 = !lean_is_exclusive(x_286);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_290 = lean_ctor_get(x_286, 1);
x_291 = lean_ctor_get(x_286, 0);
lean_dec(x_291);
x_292 = lean_ctor_get(x_15, 1);
lean_inc(x_292);
x_293 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_14, x_292, x_290);
x_294 = !lean_is_exclusive(x_293);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_295 = lean_ctor_get(x_293, 0);
x_296 = lean_ctor_get(x_293, 1);
x_297 = lean_unbox(x_295);
lean_dec(x_295);
if (x_297 == 0)
{
lean_object* x_298; 
lean_free_object(x_293);
lean_free_object(x_286);
x_298 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_22, x_296);
return x_298;
}
else
{
uint8_t x_299; lean_object* x_300; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_3);
x_299 = 1;
x_300 = lean_box(x_299);
lean_ctor_set(x_286, 1, x_22);
lean_ctor_set(x_286, 0, x_300);
lean_ctor_set(x_293, 0, x_286);
return x_293;
}
}
else
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_301 = lean_ctor_get(x_293, 0);
x_302 = lean_ctor_get(x_293, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_293);
x_303 = lean_unbox(x_301);
lean_dec(x_301);
if (x_303 == 0)
{
lean_object* x_304; 
lean_free_object(x_286);
x_304 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_22, x_302);
return x_304;
}
else
{
uint8_t x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_3);
x_305 = 1;
x_306 = lean_box(x_305);
lean_ctor_set(x_286, 1, x_22);
lean_ctor_set(x_286, 0, x_306);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_286);
lean_ctor_set(x_307, 1, x_302);
return x_307;
}
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_308 = lean_ctor_get(x_286, 1);
lean_inc(x_308);
lean_dec(x_286);
x_309 = lean_ctor_get(x_15, 1);
lean_inc(x_309);
x_310 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_14, x_309, x_308);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_313 = x_310;
} else {
 lean_dec_ref(x_310);
 x_313 = lean_box(0);
}
x_314 = lean_unbox(x_311);
lean_dec(x_311);
if (x_314 == 0)
{
lean_object* x_315; 
lean_dec(x_313);
x_315 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_22, x_312);
return x_315;
}
else
{
uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_3);
x_316 = 1;
x_317 = lean_box(x_316);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_22);
if (lean_is_scalar(x_313)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_313;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_312);
return x_319;
}
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_320 = lean_ctor_get(x_286, 1);
lean_inc(x_320);
lean_dec(x_286);
x_321 = l_Lake_readTraceFile_x3f(x_16, x_285, x_320);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = !lean_is_exclusive(x_322);
if (x_324 == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_322, 1);
lean_ctor_set(x_22, 0, x_325);
lean_ctor_set(x_322, 1, x_22);
x_27 = x_322;
x_28 = x_323;
goto block_283;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_322, 0);
x_327 = lean_ctor_get(x_322, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_322);
lean_ctor_set(x_22, 0, x_327);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_22);
x_27 = x_328;
x_28 = x_323;
goto block_283;
}
}
}
else
{
lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_329 = lean_ctor_get(x_22, 0);
x_330 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_331 = lean_ctor_get(x_22, 1);
lean_inc(x_331);
lean_inc(x_329);
lean_dec(x_22);
x_332 = l_System_FilePath_pathExists(x_16, x_23);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_unbox(x_333);
lean_dec(x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
lean_dec(x_18);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_336 = x_332;
} else {
 lean_dec_ref(x_332);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_15, 1);
lean_inc(x_337);
x_338 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_14, x_337, x_335);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_341 = x_338;
} else {
 lean_dec_ref(x_338);
 x_341 = lean_box(0);
}
x_342 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_342, 0, x_329);
lean_ctor_set(x_342, 1, x_331);
lean_ctor_set_uint8(x_342, sizeof(void*)*2, x_330);
x_343 = lean_unbox(x_339);
lean_dec(x_339);
if (x_343 == 0)
{
lean_object* x_344; 
lean_dec(x_341);
lean_dec(x_336);
x_344 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_342, x_340);
return x_344;
}
else
{
uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_3);
x_345 = 1;
x_346 = lean_box(x_345);
if (lean_is_scalar(x_336)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_336;
}
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_342);
if (lean_is_scalar(x_341)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_341;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_340);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_349 = lean_ctor_get(x_332, 1);
lean_inc(x_349);
lean_dec(x_332);
x_350 = l_Lake_readTraceFile_x3f(x_16, x_329, x_349);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_351, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_355 = x_351;
} else {
 lean_dec_ref(x_351);
 x_355 = lean_box(0);
}
x_356 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_331);
lean_ctor_set_uint8(x_356, sizeof(void*)*2, x_330);
if (lean_is_scalar(x_355)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_355;
}
lean_ctor_set(x_357, 0, x_353);
lean_ctor_set(x_357, 1, x_356);
x_27 = x_357;
x_28 = x_352;
goto block_283;
}
}
block_283:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_27, 1);
x_32 = lean_ctor_get(x_27, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
lean_dec(x_34);
x_36 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_14, x_18, x_28);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
if (x_35 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_free_object(x_36);
lean_dec(x_38);
lean_free_object(x_27);
x_40 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_31, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
x_43 = lean_unbox(x_41);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_free_object(x_36);
lean_free_object(x_27);
x_44 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_31, x_42);
return x_44;
}
else
{
uint8_t x_45; lean_object* x_46; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_3);
x_45 = 1;
x_46 = lean_box(x_45);
lean_ctor_set(x_27, 0, x_46);
lean_ctor_set(x_36, 0, x_27);
return x_36;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_36);
if (x_35 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_free_object(x_27);
x_49 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_31, x_48);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_unbox(x_47);
lean_dec(x_47);
if (x_50 == 0)
{
lean_object* x_51; 
lean_free_object(x_27);
x_51 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_31, x_48);
return x_51;
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_3);
x_52 = 1;
x_53 = lean_box(x_52);
lean_ctor_set(x_27, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_27);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_31, 0);
x_56 = lean_ctor_get_uint8(x_31, sizeof(void*)*2);
x_57 = lean_ctor_get(x_31, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_31);
x_58 = lean_ctor_get(x_21, 0);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_58, sizeof(void*)*1);
lean_dec(x_58);
x_60 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_14, x_18, x_28);
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
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_56);
if (x_59 == 0)
{
lean_object* x_65; 
lean_dec(x_63);
lean_dec(x_61);
lean_free_object(x_27);
x_65 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_64, x_62);
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
lean_free_object(x_27);
x_67 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_64, x_62);
return x_67;
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_3);
x_68 = 1;
x_69 = lean_box(x_68);
lean_ctor_set(x_27, 1, x_64);
lean_ctor_set(x_27, 0, x_69);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_27, 1);
lean_inc(x_71);
lean_dec(x_27);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get_uint8(x_71, sizeof(void*)*2);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_21, 0);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_76, sizeof(void*)*1);
lean_dec(x_76);
x_78 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_14, x_18, x_28);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 2, 1);
} else {
 x_82 = x_75;
}
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_73);
if (x_77 == 0)
{
lean_object* x_83; 
lean_dec(x_81);
lean_dec(x_79);
x_83 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_82, x_80);
return x_83;
}
else
{
uint8_t x_84; 
x_84 = lean_unbox(x_79);
lean_dec(x_79);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_81);
x_85 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_82, x_80);
return x_85;
}
else
{
uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_3);
x_86 = 1;
x_87 = lean_box(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
if (lean_is_scalar(x_81)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_81;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_80);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_29);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_91 = lean_ctor_get(x_29, 0);
x_92 = lean_ctor_get(x_27, 1);
lean_inc(x_92);
lean_dec(x_27);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
lean_ctor_set(x_29, 0, x_93);
lean_inc(x_15);
x_95 = l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___rarg(x_14, x_15, x_29, x_18, x_19, x_20, x_21, x_92, x_28);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_100, x_99);
return x_101;
}
else
{
uint8_t x_102; 
lean_dec(x_26);
lean_dec(x_15);
x_102 = !lean_is_exclusive(x_96);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_96, 1);
x_104 = lean_ctor_get(x_96, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_95);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_95, 1);
x_107 = lean_ctor_get(x_95, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_109 = lean_ctor_get_uint8(x_103, sizeof(void*)*2);
x_110 = 1;
x_111 = l_Lake_JobAction_merge(x_109, x_110);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_111);
x_112 = lean_array_get_size(x_94);
x_113 = lean_unsigned_to_nat(0u);
x_114 = lean_nat_dec_lt(x_113, x_112);
if (x_114 == 0)
{
uint8_t x_115; lean_object* x_116; 
lean_dec(x_112);
lean_dec(x_94);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_115 = 1;
x_116 = lean_box(x_115);
lean_ctor_set(x_96, 0, x_116);
return x_95;
}
else
{
uint8_t x_117; 
x_117 = lean_nat_dec_le(x_112, x_112);
if (x_117 == 0)
{
uint8_t x_118; lean_object* x_119; 
lean_dec(x_112);
lean_dec(x_94);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_118 = 1;
x_119 = lean_box(x_118);
lean_ctor_set(x_96, 0, x_119);
return x_95;
}
else
{
size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_free_object(x_95);
lean_free_object(x_96);
x_120 = 0;
x_121 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_122 = lean_box(0);
x_123 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_94, x_120, x_121, x_122, x_3, x_19, x_20, x_21, x_103, x_106);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_94);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
lean_dec(x_127);
x_128 = 1;
x_129 = lean_box(x_128);
lean_ctor_set(x_125, 0, x_129);
return x_123;
}
else
{
lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
lean_dec(x_125);
x_131 = 1;
x_132 = lean_box(x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
lean_ctor_set(x_123, 0, x_133);
return x_123;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = lean_ctor_get(x_123, 0);
x_135 = lean_ctor_get(x_123, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_123);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_138 = 1;
x_139 = lean_box(x_138);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_137;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_136);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_135);
return x_141;
}
}
}
}
else
{
lean_object* x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_142 = lean_ctor_get(x_103, 0);
x_143 = lean_ctor_get_uint8(x_103, sizeof(void*)*2);
x_144 = lean_ctor_get(x_103, 1);
lean_inc(x_144);
lean_inc(x_142);
lean_dec(x_103);
x_145 = 1;
x_146 = l_Lake_JobAction_merge(x_143, x_145);
x_147 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_144);
lean_ctor_set_uint8(x_147, sizeof(void*)*2, x_146);
x_148 = lean_array_get_size(x_94);
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_nat_dec_lt(x_149, x_148);
if (x_150 == 0)
{
uint8_t x_151; lean_object* x_152; 
lean_dec(x_148);
lean_dec(x_94);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_151 = 1;
x_152 = lean_box(x_151);
lean_ctor_set(x_96, 1, x_147);
lean_ctor_set(x_96, 0, x_152);
return x_95;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_148, x_148);
if (x_153 == 0)
{
uint8_t x_154; lean_object* x_155; 
lean_dec(x_148);
lean_dec(x_94);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_154 = 1;
x_155 = lean_box(x_154);
lean_ctor_set(x_96, 1, x_147);
lean_ctor_set(x_96, 0, x_155);
return x_95;
}
else
{
size_t x_156; size_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_free_object(x_95);
lean_free_object(x_96);
x_156 = 0;
x_157 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_158 = lean_box(0);
x_159 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_94, x_156, x_157, x_158, x_3, x_19, x_20, x_21, x_147, x_106);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_94);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_164 = x_160;
} else {
 lean_dec_ref(x_160);
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
if (lean_is_scalar(x_162)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_162;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_161);
return x_168;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_169 = lean_ctor_get(x_95, 1);
lean_inc(x_169);
lean_dec(x_95);
x_170 = lean_ctor_get(x_103, 0);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_103, sizeof(void*)*2);
x_172 = lean_ctor_get(x_103, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_173 = x_103;
} else {
 lean_dec_ref(x_103);
 x_173 = lean_box(0);
}
x_174 = 1;
x_175 = l_Lake_JobAction_merge(x_171, x_174);
if (lean_is_scalar(x_173)) {
 x_176 = lean_alloc_ctor(0, 2, 1);
} else {
 x_176 = x_173;
}
lean_ctor_set(x_176, 0, x_170);
lean_ctor_set(x_176, 1, x_172);
lean_ctor_set_uint8(x_176, sizeof(void*)*2, x_175);
x_177 = lean_array_get_size(x_94);
x_178 = lean_unsigned_to_nat(0u);
x_179 = lean_nat_dec_lt(x_178, x_177);
if (x_179 == 0)
{
uint8_t x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_177);
lean_dec(x_94);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_180 = 1;
x_181 = lean_box(x_180);
lean_ctor_set(x_96, 1, x_176);
lean_ctor_set(x_96, 0, x_181);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_96);
lean_ctor_set(x_182, 1, x_169);
return x_182;
}
else
{
uint8_t x_183; 
x_183 = lean_nat_dec_le(x_177, x_177);
if (x_183 == 0)
{
uint8_t x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_177);
lean_dec(x_94);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_184 = 1;
x_185 = lean_box(x_184);
lean_ctor_set(x_96, 1, x_176);
lean_ctor_set(x_96, 0, x_185);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_96);
lean_ctor_set(x_186, 1, x_169);
return x_186;
}
else
{
size_t x_187; size_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_free_object(x_96);
x_187 = 0;
x_188 = lean_usize_of_nat(x_177);
lean_dec(x_177);
x_189 = lean_box(0);
x_190 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_94, x_187, x_188, x_189, x_3, x_19, x_20, x_21, x_176, x_169);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_94);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_195 = x_191;
} else {
 lean_dec_ref(x_191);
 x_195 = lean_box(0);
}
x_196 = 1;
x_197 = lean_box(x_196);
if (lean_is_scalar(x_195)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_195;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_194);
if (lean_is_scalar(x_193)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_193;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_192);
return x_199;
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_200 = lean_ctor_get(x_96, 1);
lean_inc(x_200);
lean_dec(x_96);
x_201 = lean_ctor_get(x_95, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_202 = x_95;
} else {
 lean_dec_ref(x_95);
 x_202 = lean_box(0);
}
x_203 = lean_ctor_get(x_200, 0);
lean_inc(x_203);
x_204 = lean_ctor_get_uint8(x_200, sizeof(void*)*2);
x_205 = lean_ctor_get(x_200, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_206 = x_200;
} else {
 lean_dec_ref(x_200);
 x_206 = lean_box(0);
}
x_207 = 1;
x_208 = l_Lake_JobAction_merge(x_204, x_207);
if (lean_is_scalar(x_206)) {
 x_209 = lean_alloc_ctor(0, 2, 1);
} else {
 x_209 = x_206;
}
lean_ctor_set(x_209, 0, x_203);
lean_ctor_set(x_209, 1, x_205);
lean_ctor_set_uint8(x_209, sizeof(void*)*2, x_208);
x_210 = lean_array_get_size(x_94);
x_211 = lean_unsigned_to_nat(0u);
x_212 = lean_nat_dec_lt(x_211, x_210);
if (x_212 == 0)
{
uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_210);
lean_dec(x_94);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_213 = 1;
x_214 = lean_box(x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_209);
if (lean_is_scalar(x_202)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_202;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_201);
return x_216;
}
else
{
uint8_t x_217; 
x_217 = lean_nat_dec_le(x_210, x_210);
if (x_217 == 0)
{
uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_210);
lean_dec(x_94);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_218 = 1;
x_219 = lean_box(x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_209);
if (lean_is_scalar(x_202)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_202;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_201);
return x_221;
}
else
{
size_t x_222; size_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_202);
x_222 = 0;
x_223 = lean_usize_of_nat(x_210);
lean_dec(x_210);
x_224 = lean_box(0);
x_225 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_94, x_222, x_223, x_224, x_3, x_19, x_20, x_21, x_209, x_201);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_94);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_228 = x_225;
} else {
 lean_dec_ref(x_225);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_230 = x_226;
} else {
 lean_dec_ref(x_226);
 x_230 = lean_box(0);
}
x_231 = 1;
x_232 = lean_box(x_231);
if (lean_is_scalar(x_230)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_230;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_229);
if (lean_is_scalar(x_228)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_228;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_227);
return x_234;
}
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_235 = lean_ctor_get(x_29, 0);
lean_inc(x_235);
lean_dec(x_29);
x_236 = lean_ctor_get(x_27, 1);
lean_inc(x_236);
lean_dec(x_27);
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_237);
lean_inc(x_15);
x_240 = l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___rarg(x_14, x_15, x_239, x_18, x_19, x_20, x_21, x_236, x_28);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_unbox(x_242);
lean_dec(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_238);
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
lean_dec(x_240);
x_245 = lean_ctor_get(x_241, 1);
lean_inc(x_245);
lean_dec(x_241);
x_246 = l_Lake_buildUnlessUpToDate_x3f_go(x_15, x_16, x_26, x_17, x_3, x_19, x_20, x_21, x_245, x_244);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
lean_dec(x_26);
lean_dec(x_15);
x_247 = lean_ctor_get(x_241, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_248 = x_241;
} else {
 lean_dec_ref(x_241);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_240, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_250 = x_240;
} else {
 lean_dec_ref(x_240);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_247, 0);
lean_inc(x_251);
x_252 = lean_ctor_get_uint8(x_247, sizeof(void*)*2);
x_253 = lean_ctor_get(x_247, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_254 = x_247;
} else {
 lean_dec_ref(x_247);
 x_254 = lean_box(0);
}
x_255 = 1;
x_256 = l_Lake_JobAction_merge(x_252, x_255);
if (lean_is_scalar(x_254)) {
 x_257 = lean_alloc_ctor(0, 2, 1);
} else {
 x_257 = x_254;
}
lean_ctor_set(x_257, 0, x_251);
lean_ctor_set(x_257, 1, x_253);
lean_ctor_set_uint8(x_257, sizeof(void*)*2, x_256);
x_258 = lean_array_get_size(x_238);
x_259 = lean_unsigned_to_nat(0u);
x_260 = lean_nat_dec_lt(x_259, x_258);
if (x_260 == 0)
{
uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_258);
lean_dec(x_238);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_261 = 1;
x_262 = lean_box(x_261);
if (lean_is_scalar(x_248)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_248;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_257);
if (lean_is_scalar(x_250)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_250;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_249);
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
lean_dec(x_238);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_266 = 1;
x_267 = lean_box(x_266);
if (lean_is_scalar(x_248)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_248;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_257);
if (lean_is_scalar(x_250)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_250;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_249);
return x_269;
}
else
{
size_t x_270; size_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_250);
lean_dec(x_248);
x_270 = 0;
x_271 = lean_usize_of_nat(x_258);
lean_dec(x_258);
x_272 = lean_box(0);
x_273 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_238, x_270, x_271, x_272, x_3, x_19, x_20, x_21, x_257, x_249);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_238);
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
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_278 = x_274;
} else {
 lean_dec_ref(x_274);
 x_278 = lean_box(0);
}
x_279 = 1;
x_280 = lean_box(x_279);
if (lean_is_scalar(x_278)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_278;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_277);
if (lean_is_scalar(x_276)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_276;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_275);
return x_282;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_12 = x_3;
} else {
 lean_dec_ref(x_3);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_16 = x_8;
} else {
 lean_dec_ref(x_8);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = l_Lake_BuildTrace_mix(x_15, x_17);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*11);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*11);
x_27 = l_Lake_instOrdBuildType;
x_28 = lean_box(x_23);
x_29 = lean_box(x_26);
x_30 = l_Ord_instDecidableRelLe___rarg(x_27, x_28, x_29);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
x_32 = lean_array_size(x_31);
x_33 = 0;
x_34 = l_Array_mapMUnsafe_map___at_Lake_BuildType_leanArgs___spec__1(x_32, x_33, x_31);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
x_36 = l_Array_append___rarg(x_34, x_35);
lean_dec(x_35);
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
x_38 = lean_array_size(x_37);
x_39 = l_Array_mapMUnsafe_map___at_Lake_BuildType_leanArgs___spec__1(x_38, x_33, x_37);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_20, 0);
lean_inc(x_41);
lean_dec(x_20);
x_42 = lean_ctor_get(x_21, 7);
lean_inc(x_42);
lean_inc(x_41);
x_43 = l_System_FilePath_join(x_41, x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_24, 2);
lean_inc(x_44);
lean_dec(x_24);
x_45 = l_System_FilePath_join(x_43, x_44);
lean_dec(x_44);
x_46 = l_Lake_Module_recParseImports___closed__1;
x_47 = l_Lean_modToFilePath(x_45, x_2, x_46);
x_48 = l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(x_47, x_9);
if (x_30 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_389 = l_Lake_BuildType_leanArgs(x_26);
x_390 = l_Array_append___rarg(x_389, x_36);
lean_dec(x_36);
x_391 = l_Array_append___rarg(x_390, x_39);
lean_dec(x_39);
x_392 = l_Array_append___rarg(x_391, x_40);
lean_dec(x_40);
x_49 = x_392;
goto block_388;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_393 = l_Lake_BuildType_leanArgs(x_23);
x_394 = l_Array_append___rarg(x_393, x_36);
lean_dec(x_36);
x_395 = l_Array_append___rarg(x_394, x_39);
lean_dec(x_39);
x_396 = l_Array_append___rarg(x_395, x_40);
lean_dec(x_40);
x_49 = x_396;
goto block_388;
}
block_388:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; uint64_t x_351; 
x_50 = lean_array_get_size(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
if (x_52 == 0)
{
uint64_t x_382; 
lean_dec(x_50);
x_382 = l_Lake_Hash_nil;
x_351 = x_382;
goto block_381;
}
else
{
uint8_t x_383; 
x_383 = lean_nat_dec_le(x_50, x_50);
if (x_383 == 0)
{
uint64_t x_384; 
lean_dec(x_50);
x_384 = l_Lake_Hash_nil;
x_351 = x_384;
goto block_381;
}
else
{
size_t x_385; uint64_t x_386; uint64_t x_387; 
x_385 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_386 = l_Lake_Hash_nil;
x_387 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(x_49, x_33, x_385, x_386);
x_351 = x_387;
goto block_381;
}
}
block_350:
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_12);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
x_59 = l_Lake_BuildTrace_mix(x_58, x_56);
lean_inc(x_59);
lean_ctor_set(x_55, 1, x_59);
x_60 = lean_ctor_get(x_21, 8);
lean_inc(x_60);
x_61 = l_System_FilePath_join(x_41, x_60);
lean_dec(x_60);
x_62 = lean_ctor_get(x_21, 9);
lean_inc(x_62);
lean_inc(x_61);
x_63 = l_System_FilePath_join(x_61, x_62);
lean_dec(x_62);
x_64 = l_Lake_Module_recBuildLean___lambda__1___closed__1;
x_65 = l_Lean_modToFilePath(x_63, x_2, x_64);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
lean_dec(x_56);
x_67 = 3;
lean_inc(x_7);
lean_inc_n(x_1, 2);
x_68 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(x_1, x_2, x_4, x_10, x_11, x_21, x_22, x_25, x_45, x_47, x_49, x_61, x_63, x_1, x_59, x_65, x_67, x_66, x_5, x_6, x_7, x_55, x_54);
lean_dec(x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_69, 1);
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_7);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_dec(x_68);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_71, 0);
x_77 = l_Lake_Module_cacheOutputHashes(x_1, x_74);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_ctor_set(x_69, 0, x_79);
lean_ctor_set(x_77, 0, x_69);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_77, 0);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_77);
lean_ctor_set(x_69, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_69);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_77);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_77, 0);
x_85 = lean_io_error_to_string(x_84);
x_86 = 3;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_array_get_size(x_76);
x_89 = lean_array_push(x_76, x_87);
lean_ctor_set(x_71, 0, x_89);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 0, x_88);
lean_ctor_set_tag(x_77, 0);
lean_ctor_set(x_77, 0, x_69);
return x_77;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_77, 0);
x_91 = lean_ctor_get(x_77, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_77);
x_92 = lean_io_error_to_string(x_90);
x_93 = 3;
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_93);
x_95 = lean_array_get_size(x_76);
x_96 = lean_array_push(x_76, x_94);
lean_ctor_set(x_71, 0, x_96);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 0, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_69);
lean_ctor_set(x_97, 1, x_91);
return x_97;
}
}
}
else
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_71, 0);
x_99 = lean_ctor_get_uint8(x_71, sizeof(void*)*2);
x_100 = lean_ctor_get(x_71, 1);
lean_inc(x_100);
lean_inc(x_98);
lean_dec(x_71);
x_101 = l_Lake_Module_cacheOutputHashes(x_1, x_74);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_100);
lean_ctor_set_uint8(x_105, sizeof(void*)*2, x_99);
lean_ctor_set(x_69, 1, x_105);
lean_ctor_set(x_69, 0, x_102);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_69);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_109 = x_101;
} else {
 lean_dec_ref(x_101);
 x_109 = lean_box(0);
}
x_110 = lean_io_error_to_string(x_107);
x_111 = 3;
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = lean_array_get_size(x_98);
x_114 = lean_array_push(x_98, x_112);
x_115 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_100);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_99);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 1, x_115);
lean_ctor_set(x_69, 0, x_113);
if (lean_is_scalar(x_109)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_109;
 lean_ctor_set_tag(x_116, 0);
}
lean_ctor_set(x_116, 0, x_69);
lean_ctor_set(x_116, 1, x_108);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_7, 0);
lean_inc(x_117);
lean_dec(x_7);
x_118 = lean_ctor_get_uint8(x_117, sizeof(void*)*1 + 1);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_68, 1);
lean_inc(x_119);
lean_dec(x_68);
x_120 = !lean_is_exclusive(x_71);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_71, 0);
x_122 = l_Lake_Module_cacheOutputHashes(x_1, x_119);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_122, 0);
lean_ctor_set(x_69, 0, x_124);
lean_ctor_set(x_122, 0, x_69);
return x_122;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_122, 0);
x_126 = lean_ctor_get(x_122, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_122);
lean_ctor_set(x_69, 0, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_69);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_122);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_122, 0);
x_130 = lean_io_error_to_string(x_129);
x_131 = 3;
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_131);
x_133 = lean_array_get_size(x_121);
x_134 = lean_array_push(x_121, x_132);
lean_ctor_set(x_71, 0, x_134);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 0, x_133);
lean_ctor_set_tag(x_122, 0);
lean_ctor_set(x_122, 0, x_69);
return x_122;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_135 = lean_ctor_get(x_122, 0);
x_136 = lean_ctor_get(x_122, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_122);
x_137 = lean_io_error_to_string(x_135);
x_138 = 3;
x_139 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_138);
x_140 = lean_array_get_size(x_121);
x_141 = lean_array_push(x_121, x_139);
lean_ctor_set(x_71, 0, x_141);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 0, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_69);
lean_ctor_set(x_142, 1, x_136);
return x_142;
}
}
}
else
{
lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_71, 0);
x_144 = lean_ctor_get_uint8(x_71, sizeof(void*)*2);
x_145 = lean_ctor_get(x_71, 1);
lean_inc(x_145);
lean_inc(x_143);
lean_dec(x_71);
x_146 = l_Lake_Module_cacheOutputHashes(x_1, x_119);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_150, 0, x_143);
lean_ctor_set(x_150, 1, x_145);
lean_ctor_set_uint8(x_150, sizeof(void*)*2, x_144);
lean_ctor_set(x_69, 1, x_150);
lean_ctor_set(x_69, 0, x_147);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_69);
lean_ctor_set(x_151, 1, x_148);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_152 = lean_ctor_get(x_146, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_154 = x_146;
} else {
 lean_dec_ref(x_146);
 x_154 = lean_box(0);
}
x_155 = lean_io_error_to_string(x_152);
x_156 = 3;
x_157 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_156);
x_158 = lean_array_get_size(x_143);
x_159 = lean_array_push(x_143, x_157);
x_160 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_145);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_144);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 1, x_160);
lean_ctor_set(x_69, 0, x_158);
if (lean_is_scalar(x_154)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_154;
 lean_ctor_set_tag(x_161, 0);
}
lean_ctor_set(x_161, 0, x_69);
lean_ctor_set(x_161, 1, x_153);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_68);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_68, 0);
lean_dec(x_163);
x_164 = !lean_is_exclusive(x_71);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_box(0);
lean_ctor_set(x_69, 0, x_165);
return x_68;
}
else
{
lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_71, 0);
x_167 = lean_ctor_get_uint8(x_71, sizeof(void*)*2);
x_168 = lean_ctor_get(x_71, 1);
lean_inc(x_168);
lean_inc(x_166);
lean_dec(x_71);
x_169 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*2, x_167);
x_170 = lean_box(0);
lean_ctor_set(x_69, 1, x_169);
lean_ctor_set(x_69, 0, x_170);
return x_68;
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_171 = lean_ctor_get(x_68, 1);
lean_inc(x_171);
lean_dec(x_68);
x_172 = lean_ctor_get(x_71, 0);
lean_inc(x_172);
x_173 = lean_ctor_get_uint8(x_71, sizeof(void*)*2);
x_174 = lean_ctor_get(x_71, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_175 = x_71;
} else {
 lean_dec_ref(x_71);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 2, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_172);
lean_ctor_set(x_176, 1, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*2, x_173);
x_177 = lean_box(0);
lean_ctor_set(x_69, 1, x_176);
lean_ctor_set(x_69, 0, x_177);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_69);
lean_ctor_set(x_178, 1, x_171);
return x_178;
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_69, 1);
x_180 = lean_ctor_get(x_69, 0);
lean_inc(x_179);
lean_inc(x_180);
lean_dec(x_69);
x_181 = lean_unbox(x_180);
lean_dec(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_7);
x_182 = lean_ctor_get(x_68, 1);
lean_inc(x_182);
lean_dec(x_68);
x_183 = lean_ctor_get(x_179, 0);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_179, sizeof(void*)*2);
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_186 = x_179;
} else {
 lean_dec_ref(x_179);
 x_186 = lean_box(0);
}
x_187 = l_Lake_Module_cacheOutputHashes(x_1, x_182);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
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
if (lean_is_scalar(x_186)) {
 x_191 = lean_alloc_ctor(0, 2, 1);
} else {
 x_191 = x_186;
}
lean_ctor_set(x_191, 0, x_183);
lean_ctor_set(x_191, 1, x_185);
lean_ctor_set_uint8(x_191, sizeof(void*)*2, x_184);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_188);
lean_ctor_set(x_192, 1, x_191);
if (lean_is_scalar(x_190)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_190;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_189);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_194 = lean_ctor_get(x_187, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_187, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_196 = x_187;
} else {
 lean_dec_ref(x_187);
 x_196 = lean_box(0);
}
x_197 = lean_io_error_to_string(x_194);
x_198 = 3;
x_199 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_198);
x_200 = lean_array_get_size(x_183);
x_201 = lean_array_push(x_183, x_199);
if (lean_is_scalar(x_186)) {
 x_202 = lean_alloc_ctor(0, 2, 1);
} else {
 x_202 = x_186;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_185);
lean_ctor_set_uint8(x_202, sizeof(void*)*2, x_184);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_202);
if (lean_is_scalar(x_196)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_196;
 lean_ctor_set_tag(x_204, 0);
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_195);
return x_204;
}
}
else
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_7, 0);
lean_inc(x_205);
lean_dec(x_7);
x_206 = lean_ctor_get_uint8(x_205, sizeof(void*)*1 + 1);
lean_dec(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_207 = lean_ctor_get(x_68, 1);
lean_inc(x_207);
lean_dec(x_68);
x_208 = lean_ctor_get(x_179, 0);
lean_inc(x_208);
x_209 = lean_ctor_get_uint8(x_179, sizeof(void*)*2);
x_210 = lean_ctor_get(x_179, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_211 = x_179;
} else {
 lean_dec_ref(x_179);
 x_211 = lean_box(0);
}
x_212 = l_Lake_Module_cacheOutputHashes(x_1, x_207);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_216 = lean_alloc_ctor(0, 2, 1);
} else {
 x_216 = x_211;
}
lean_ctor_set(x_216, 0, x_208);
lean_ctor_set(x_216, 1, x_210);
lean_ctor_set_uint8(x_216, sizeof(void*)*2, x_209);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_213);
lean_ctor_set(x_217, 1, x_216);
if (lean_is_scalar(x_215)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_215;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_214);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_219 = lean_ctor_get(x_212, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_212, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_221 = x_212;
} else {
 lean_dec_ref(x_212);
 x_221 = lean_box(0);
}
x_222 = lean_io_error_to_string(x_219);
x_223 = 3;
x_224 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set_uint8(x_224, sizeof(void*)*1, x_223);
x_225 = lean_array_get_size(x_208);
x_226 = lean_array_push(x_208, x_224);
if (lean_is_scalar(x_211)) {
 x_227 = lean_alloc_ctor(0, 2, 1);
} else {
 x_227 = x_211;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_210);
lean_ctor_set_uint8(x_227, sizeof(void*)*2, x_209);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_227);
if (lean_is_scalar(x_221)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_221;
 lean_ctor_set_tag(x_229, 0);
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_220);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_1);
x_230 = lean_ctor_get(x_68, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_231 = x_68;
} else {
 lean_dec_ref(x_68);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_179, 0);
lean_inc(x_232);
x_233 = lean_ctor_get_uint8(x_179, sizeof(void*)*2);
x_234 = lean_ctor_get(x_179, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_235 = x_179;
} else {
 lean_dec_ref(x_179);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(0, 2, 1);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_232);
lean_ctor_set(x_236, 1, x_234);
lean_ctor_set_uint8(x_236, sizeof(void*)*2, x_233);
x_237 = lean_box(0);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
if (lean_is_scalar(x_231)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_231;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_230);
return x_239;
}
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_7);
lean_dec(x_1);
x_240 = !lean_is_exclusive(x_68);
if (x_240 == 0)
{
lean_object* x_241; uint8_t x_242; 
x_241 = lean_ctor_get(x_68, 0);
lean_dec(x_241);
x_242 = !lean_is_exclusive(x_69);
if (x_242 == 0)
{
return x_68;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_69, 0);
x_244 = lean_ctor_get(x_69, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_69);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
lean_ctor_set(x_68, 0, x_245);
return x_68;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_246 = lean_ctor_get(x_68, 1);
lean_inc(x_246);
lean_dec(x_68);
x_247 = lean_ctor_get(x_69, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_69, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_249 = x_69;
} else {
 lean_dec_ref(x_69);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_246);
return x_251;
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_7);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_68);
if (x_252 == 0)
{
return x_68;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_68, 0);
x_254 = lean_ctor_get(x_68, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_68);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; 
x_256 = lean_ctor_get(x_55, 0);
x_257 = lean_ctor_get_uint8(x_55, sizeof(void*)*2);
x_258 = lean_ctor_get(x_55, 1);
lean_inc(x_258);
lean_inc(x_256);
lean_dec(x_55);
lean_inc(x_56);
x_259 = l_Lake_BuildTrace_mix(x_258, x_56);
lean_inc(x_259);
x_260 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_260, 0, x_256);
lean_ctor_set(x_260, 1, x_259);
lean_ctor_set_uint8(x_260, sizeof(void*)*2, x_257);
x_261 = lean_ctor_get(x_21, 8);
lean_inc(x_261);
x_262 = l_System_FilePath_join(x_41, x_261);
lean_dec(x_261);
x_263 = lean_ctor_get(x_21, 9);
lean_inc(x_263);
lean_inc(x_262);
x_264 = l_System_FilePath_join(x_262, x_263);
lean_dec(x_263);
x_265 = l_Lake_Module_recBuildLean___lambda__1___closed__1;
x_266 = l_Lean_modToFilePath(x_264, x_2, x_265);
x_267 = lean_ctor_get(x_56, 1);
lean_inc(x_267);
lean_dec(x_56);
x_268 = 3;
lean_inc(x_7);
lean_inc_n(x_1, 2);
x_269 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(x_1, x_2, x_4, x_10, x_11, x_21, x_22, x_25, x_45, x_47, x_49, x_262, x_264, x_1, x_259, x_266, x_268, x_267, x_5, x_6, x_7, x_260, x_54);
lean_dec(x_266);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_273 = x_270;
} else {
 lean_dec_ref(x_270);
 x_273 = lean_box(0);
}
x_274 = lean_unbox(x_272);
lean_dec(x_272);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_7);
x_275 = lean_ctor_get(x_269, 1);
lean_inc(x_275);
lean_dec(x_269);
x_276 = lean_ctor_get(x_271, 0);
lean_inc(x_276);
x_277 = lean_ctor_get_uint8(x_271, sizeof(void*)*2);
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
x_280 = l_Lake_Module_cacheOutputHashes(x_1, x_275);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
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
 x_284 = lean_alloc_ctor(0, 2, 1);
} else {
 x_284 = x_279;
}
lean_ctor_set(x_284, 0, x_276);
lean_ctor_set(x_284, 1, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*2, x_277);
if (lean_is_scalar(x_273)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_273;
}
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_283;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_282);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_287 = lean_ctor_get(x_280, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_280, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_289 = x_280;
} else {
 lean_dec_ref(x_280);
 x_289 = lean_box(0);
}
x_290 = lean_io_error_to_string(x_287);
x_291 = 3;
x_292 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set_uint8(x_292, sizeof(void*)*1, x_291);
x_293 = lean_array_get_size(x_276);
x_294 = lean_array_push(x_276, x_292);
if (lean_is_scalar(x_279)) {
 x_295 = lean_alloc_ctor(0, 2, 1);
} else {
 x_295 = x_279;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_278);
lean_ctor_set_uint8(x_295, sizeof(void*)*2, x_277);
if (lean_is_scalar(x_273)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_273;
 lean_ctor_set_tag(x_296, 1);
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_295);
if (lean_is_scalar(x_289)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_289;
 lean_ctor_set_tag(x_297, 0);
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_288);
return x_297;
}
}
else
{
lean_object* x_298; uint8_t x_299; 
x_298 = lean_ctor_get(x_7, 0);
lean_inc(x_298);
lean_dec(x_7);
x_299 = lean_ctor_get_uint8(x_298, sizeof(void*)*1 + 1);
lean_dec(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_300 = lean_ctor_get(x_269, 1);
lean_inc(x_300);
lean_dec(x_269);
x_301 = lean_ctor_get(x_271, 0);
lean_inc(x_301);
x_302 = lean_ctor_get_uint8(x_271, sizeof(void*)*2);
x_303 = lean_ctor_get(x_271, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_304 = x_271;
} else {
 lean_dec_ref(x_271);
 x_304 = lean_box(0);
}
x_305 = l_Lake_Module_cacheOutputHashes(x_1, x_300);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_308 = x_305;
} else {
 lean_dec_ref(x_305);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_309 = lean_alloc_ctor(0, 2, 1);
} else {
 x_309 = x_304;
}
lean_ctor_set(x_309, 0, x_301);
lean_ctor_set(x_309, 1, x_303);
lean_ctor_set_uint8(x_309, sizeof(void*)*2, x_302);
if (lean_is_scalar(x_273)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_273;
}
lean_ctor_set(x_310, 0, x_306);
lean_ctor_set(x_310, 1, x_309);
if (lean_is_scalar(x_308)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_308;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_307);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_312 = lean_ctor_get(x_305, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_305, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_314 = x_305;
} else {
 lean_dec_ref(x_305);
 x_314 = lean_box(0);
}
x_315 = lean_io_error_to_string(x_312);
x_316 = 3;
x_317 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set_uint8(x_317, sizeof(void*)*1, x_316);
x_318 = lean_array_get_size(x_301);
x_319 = lean_array_push(x_301, x_317);
if (lean_is_scalar(x_304)) {
 x_320 = lean_alloc_ctor(0, 2, 1);
} else {
 x_320 = x_304;
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_303);
lean_ctor_set_uint8(x_320, sizeof(void*)*2, x_302);
if (lean_is_scalar(x_273)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_273;
 lean_ctor_set_tag(x_321, 1);
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_320);
if (lean_is_scalar(x_314)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_314;
 lean_ctor_set_tag(x_322, 0);
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_313);
return x_322;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_1);
x_323 = lean_ctor_get(x_269, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_324 = x_269;
} else {
 lean_dec_ref(x_269);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get(x_271, 0);
lean_inc(x_325);
x_326 = lean_ctor_get_uint8(x_271, sizeof(void*)*2);
x_327 = lean_ctor_get(x_271, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_328 = x_271;
} else {
 lean_dec_ref(x_271);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 2, 1);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_325);
lean_ctor_set(x_329, 1, x_327);
lean_ctor_set_uint8(x_329, sizeof(void*)*2, x_326);
x_330 = lean_box(0);
if (lean_is_scalar(x_273)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_273;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_329);
if (lean_is_scalar(x_324)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_324;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_323);
return x_332;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_7);
lean_dec(x_1);
x_333 = lean_ctor_get(x_269, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_334 = x_269;
} else {
 lean_dec_ref(x_269);
 x_334 = lean_box(0);
}
x_335 = lean_ctor_get(x_270, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_270, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_337 = x_270;
} else {
 lean_dec_ref(x_270);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
if (lean_is_scalar(x_334)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_334;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_333);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_7);
lean_dec(x_1);
x_340 = lean_ctor_get(x_269, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_269, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_342 = x_269;
} else {
 lean_dec_ref(x_269);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
}
}
else
{
uint8_t x_344; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_344 = !lean_is_exclusive(x_53);
if (x_344 == 0)
{
lean_object* x_345; 
if (lean_is_scalar(x_12)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_12;
}
lean_ctor_set(x_345, 0, x_53);
lean_ctor_set(x_345, 1, x_54);
return x_345;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_53, 0);
x_347 = lean_ctor_get(x_53, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_53);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
if (lean_is_scalar(x_12)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_12;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_54);
return x_349;
}
}
}
block_381:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_352 = l_Lake_Module_recBuildDeps___lambda__2___closed__2;
x_353 = lean_box_uint64(x_351);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = l_Lake_BuildTrace_mix(x_18, x_354);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_356; 
x_356 = !lean_is_exclusive(x_48);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_48, 1);
if (lean_is_scalar(x_16)) {
 x_358 = lean_alloc_ctor(0, 2, 1);
} else {
 x_358 = x_16;
}
lean_ctor_set(x_358, 0, x_13);
lean_ctor_set(x_358, 1, x_355);
lean_ctor_set_uint8(x_358, sizeof(void*)*2, x_14);
lean_ctor_set(x_48, 1, x_358);
x_53 = x_48;
x_54 = x_357;
goto block_350;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_359 = lean_ctor_get(x_48, 0);
x_360 = lean_ctor_get(x_48, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_48);
if (lean_is_scalar(x_16)) {
 x_361 = lean_alloc_ctor(0, 2, 1);
} else {
 x_361 = x_16;
}
lean_ctor_set(x_361, 0, x_13);
lean_ctor_set(x_361, 1, x_355);
lean_ctor_set_uint8(x_361, sizeof(void*)*2, x_14);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_361);
x_53 = x_362;
x_54 = x_360;
goto block_350;
}
}
else
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_48);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_364 = lean_ctor_get(x_48, 0);
x_365 = lean_ctor_get(x_48, 1);
x_366 = lean_io_error_to_string(x_364);
x_367 = 3;
x_368 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set_uint8(x_368, sizeof(void*)*1, x_367);
x_369 = lean_array_get_size(x_13);
x_370 = lean_array_push(x_13, x_368);
if (lean_is_scalar(x_16)) {
 x_371 = lean_alloc_ctor(0, 2, 1);
} else {
 x_371 = x_16;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_355);
lean_ctor_set_uint8(x_371, sizeof(void*)*2, x_14);
lean_ctor_set(x_48, 1, x_371);
lean_ctor_set(x_48, 0, x_369);
x_53 = x_48;
x_54 = x_365;
goto block_350;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_372 = lean_ctor_get(x_48, 0);
x_373 = lean_ctor_get(x_48, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_48);
x_374 = lean_io_error_to_string(x_372);
x_375 = 3;
x_376 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*1, x_375);
x_377 = lean_array_get_size(x_13);
x_378 = lean_array_push(x_13, x_376);
if (lean_is_scalar(x_16)) {
 x_379 = lean_alloc_ctor(0, 2, 1);
} else {
 x_379 = x_16;
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_355);
lean_ctor_set_uint8(x_379, sizeof(void*)*2, x_14);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_379);
x_53 = x_380;
x_54 = x_373;
goto block_350;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__1), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = l_Lake_BuildTrace_nil;
x_14 = l_Lake_Job_mapM___rarg(x_3, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_13, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1;
lean_inc(x_8);
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = l_Lake_Module_depsFacetConfig___closed__2;
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, lean_box(0));
x_15 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__2), 9, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_8);
x_16 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg), 8, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = 0;
x_18 = l_Lake_withRegisterJob___rarg(x_11, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
uint8_t x_24; lean_object* x_25; 
x_24 = lean_unbox(x_17);
lean_dec(x_17);
x_25 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_24, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_16);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_nullFormat___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Module_recBuildLean(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanArts", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_leanArtsFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_leanArtsFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_leanArtsFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_leanArtsFacetConfig___closed__3;
x_2 = 1;
x_3 = l_Lake_Module_leanArtsFacetConfig___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_leanArtsFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_leanArtsFacetConfig___elambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 8);
lean_inc(x_13);
x_14 = l_System_FilePath_join(x_11, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 9);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_System_FilePath_join(x_14, x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
x_19 = l_Lean_modToFilePath(x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
x_20 = 0;
lean_inc(x_19);
x_21 = l_Lake_fetchFileTrace(x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 1);
x_31 = l_Lake_BuildTrace_mix(x_30, x_27);
lean_ctor_set(x_23, 1, x_31);
lean_ctor_set(x_22, 0, x_19);
return x_21;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_32);
lean_dec(x_23);
x_35 = l_Lake_BuildTrace_mix(x_34, x_27);
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_33);
lean_ctor_set(x_22, 1, x_36);
lean_ctor_set(x_22, 0, x_19);
return x_21;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
lean_dec(x_22);
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_41 = x_23;
} else {
 lean_dec_ref(x_23);
 x_41 = lean_box(0);
}
x_42 = l_Lake_BuildTrace_mix(x_40, x_37);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 1);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_39);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_21, 0, x_44);
return x_21;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_dec(x_21);
x_46 = lean_ctor_get(x_22, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_47 = x_22;
} else {
 lean_dec_ref(x_22);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_23, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_50 = lean_ctor_get(x_23, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_51 = x_23;
} else {
 lean_dec_ref(x_23);
 x_51 = lean_box(0);
}
x_52 = l_Lake_BuildTrace_mix(x_50, x_46);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 1);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_49);
if (lean_is_scalar(x_47)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_47;
}
lean_ctor_set(x_54, 0, x_19);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_19);
x_56 = !lean_is_exclusive(x_21);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_21, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
return x_21;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_22, 0);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_22);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_21, 0, x_61);
return x_21;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_dec(x_21);
x_63 = lean_ctor_get(x_22, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_65 = x_22;
} else {
 lean_dec_ref(x_22);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = l_Lake_BuildTrace_nil;
x_20 = l_Lake_Job_mapM___rarg(x_14, x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_19, x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_11, 0, x_22);
lean_ctor_set(x_20, 0, x_11);
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
lean_ctor_set(x_11, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_11);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = l_Lake_BuildTrace_nil;
x_36 = l_Lake_Job_mapM___rarg(x_30, x_32, x_33, x_34, x_2, x_3, x_4, x_5, x_35, x_12);
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
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_31);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_10, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_10;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_10, 0, x_51);
return x_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_dec(x_10);
x_53 = lean_ctor_get(x_11, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_55 = x_11;
} else {
 lean_dec_ref(x_11);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
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
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
return x_10;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_10, 0);
x_60 = lean_ctor_get(x_10, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_10);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lake_Module_oleanFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oleanFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oleanFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_oleanFacetConfig___closed__1;
x_2 = 1;
x_3 = l_Lake_Module_oleanFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_oleanFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_oleanFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_oleanFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Module_oleanFacetConfig___elambda__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 8);
lean_inc(x_13);
x_14 = l_System_FilePath_join(x_11, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 9);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_System_FilePath_join(x_14, x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lake_Module_clearOutputHashes___closed__1;
x_19 = l_Lean_modToFilePath(x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
x_20 = 0;
lean_inc(x_19);
x_21 = l_Lake_fetchFileTrace(x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 1);
x_31 = l_Lake_BuildTrace_mix(x_30, x_27);
lean_ctor_set(x_23, 1, x_31);
lean_ctor_set(x_22, 0, x_19);
return x_21;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_32);
lean_dec(x_23);
x_35 = l_Lake_BuildTrace_mix(x_34, x_27);
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_33);
lean_ctor_set(x_22, 1, x_36);
lean_ctor_set(x_22, 0, x_19);
return x_21;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
lean_dec(x_22);
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_41 = x_23;
} else {
 lean_dec_ref(x_23);
 x_41 = lean_box(0);
}
x_42 = l_Lake_BuildTrace_mix(x_40, x_37);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 1);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_39);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_21, 0, x_44);
return x_21;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_dec(x_21);
x_46 = lean_ctor_get(x_22, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_47 = x_22;
} else {
 lean_dec_ref(x_22);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_23, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_50 = lean_ctor_get(x_23, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_51 = x_23;
} else {
 lean_dec_ref(x_23);
 x_51 = lean_box(0);
}
x_52 = l_Lake_BuildTrace_mix(x_50, x_46);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 1);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_49);
if (lean_is_scalar(x_47)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_47;
}
lean_ctor_set(x_54, 0, x_19);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_19);
x_56 = !lean_is_exclusive(x_21);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_21, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
return x_21;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_22, 0);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_22);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_21, 0, x_61);
return x_21;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_dec(x_21);
x_63 = lean_ctor_get(x_22, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_65 = x_22;
} else {
 lean_dec_ref(x_22);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = l_Lake_BuildTrace_nil;
x_20 = l_Lake_Job_mapM___rarg(x_14, x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_19, x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_11, 0, x_22);
lean_ctor_set(x_20, 0, x_11);
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
lean_ctor_set(x_11, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_11);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = l_Lake_BuildTrace_nil;
x_36 = l_Lake_Job_mapM___rarg(x_30, x_32, x_33, x_34, x_2, x_3, x_4, x_5, x_35, x_12);
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
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_31);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_10, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_10;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_10, 0, x_51);
return x_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_dec(x_10);
x_53 = lean_ctor_get(x_11, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_55 = x_11;
} else {
 lean_dec_ref(x_11);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
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
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
return x_10;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_10, 0);
x_60 = lean_ctor_get(x_10, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_10);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lake_Module_ileanFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_clearOutputHashes___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_ileanFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_ileanFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_ileanFacetConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_ileanFacetConfig___closed__2;
x_2 = 1;
x_3 = l_Lake_Module_ileanFacetConfig___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_ileanFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_ileanFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_ileanFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Module_ileanFacetConfig___elambda__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 8);
lean_inc(x_13);
x_14 = l_System_FilePath_join(x_11, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 12);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_System_FilePath_join(x_14, x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lake_Module_clearOutputHashes___closed__2;
x_19 = l_Lean_modToFilePath(x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
x_20 = 0;
lean_inc(x_19);
x_21 = l_Lake_fetchFileTrace(x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_6, 2);
lean_inc(x_31);
lean_dec(x_6);
x_32 = l_Lake_BuildTrace_mix(x_27, x_31);
lean_ctor_set(x_23, 1, x_32);
lean_ctor_set(x_22, 0, x_19);
return x_21;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
lean_inc(x_33);
lean_dec(x_23);
x_35 = lean_ctor_get(x_6, 2);
lean_inc(x_35);
lean_dec(x_6);
x_36 = l_Lake_BuildTrace_mix(x_27, x_35);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_34);
lean_ctor_set(x_22, 1, x_37);
lean_ctor_set(x_22, 0, x_19);
return x_21;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_22, 0);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_41 = x_23;
} else {
 lean_dec_ref(x_23);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_6, 2);
lean_inc(x_42);
lean_dec(x_6);
x_43 = l_Lake_BuildTrace_mix(x_38, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 1);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_40);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_19);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_21, 0, x_45);
return x_21;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_48 = x_22;
} else {
 lean_dec_ref(x_22);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_23, 0);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_51 = x_23;
} else {
 lean_dec_ref(x_23);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_6, 2);
lean_inc(x_52);
lean_dec(x_6);
x_53 = l_Lake_BuildTrace_mix(x_47, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 1);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_50);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_19);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_46);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_19);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_21, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_22);
if (x_59 == 0)
{
return x_21;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_22, 0);
x_61 = lean_ctor_get(x_22, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_22);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_21, 0, x_62);
return x_21;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
lean_dec(x_21);
x_64 = lean_ctor_get(x_22, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_66 = x_22;
} else {
 lean_dec_ref(x_22);
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
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = l_Lake_BuildTrace_nil;
x_20 = l_Lake_Job_mapM___rarg(x_14, x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_19, x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_11, 0, x_22);
lean_ctor_set(x_20, 0, x_11);
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
lean_ctor_set(x_11, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_11);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = l_Lake_BuildTrace_nil;
x_36 = l_Lake_Job_mapM___rarg(x_30, x_32, x_33, x_34, x_2, x_3, x_4, x_5, x_35, x_12);
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
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_31);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_10, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_10;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_10, 0, x_51);
return x_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_dec(x_10);
x_53 = lean_ctor_get(x_11, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_55 = x_11;
} else {
 lean_dec_ref(x_11);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
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
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
return x_10;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_10, 0);
x_60 = lean_ctor_get(x_10, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_10);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lake_Module_cFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_clearOutputHashes___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_cFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_cFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_cFacetConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_cFacetConfig___closed__2;
x_2 = 1;
x_3 = l_Lake_Module_cFacetConfig___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_cFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_cFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_cFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Module_cFacetConfig___elambda__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 8);
lean_inc(x_13);
x_14 = l_System_FilePath_join(x_11, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 12);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_System_FilePath_join(x_14, x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lake_Module_clearOutputHashes___closed__4;
x_19 = l_Lean_modToFilePath(x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
x_20 = 0;
lean_inc(x_19);
x_21 = l_Lake_fetchFileTrace(x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_23, 1);
lean_dec(x_30);
lean_ctor_set(x_23, 1, x_27);
lean_ctor_set(x_22, 0, x_19);
return x_21;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
lean_ctor_set(x_22, 1, x_33);
lean_ctor_set(x_22, 0, x_19);
return x_21;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_37 = x_23;
} else {
 lean_dec_ref(x_23);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 1);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_42 = x_22;
} else {
 lean_dec_ref(x_22);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_23, 0);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_45 = x_23;
} else {
 lean_dec_ref(x_23);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 1);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_44);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_19);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_21, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_21;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_21, 0, x_54);
return x_21;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_dec(x_21);
x_56 = lean_ctor_get(x_22, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_22, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_58 = x_22;
} else {
 lean_dec_ref(x_22);
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
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = l_Lake_BuildTrace_nil;
x_20 = l_Lake_Job_mapM___rarg(x_14, x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_19, x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_11, 0, x_22);
lean_ctor_set(x_20, 0, x_11);
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
lean_ctor_set(x_11, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_11);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = l_Lake_BuildTrace_nil;
x_36 = l_Lake_Job_mapM___rarg(x_30, x_32, x_33, x_34, x_2, x_3, x_4, x_5, x_35, x_12);
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
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_31);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_10, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_10;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_10, 0, x_51);
return x_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_dec(x_10);
x_53 = lean_ctor_get(x_11, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_55 = x_11;
} else {
 lean_dec_ref(x_11);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
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
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
return x_10;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_10, 0);
x_60 = lean_ctor_get(x_10, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_10);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lake_Module_bcFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_clearOutputHashes___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_bcFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_bcFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_bcFacetConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_bcFacetConfig___closed__2;
x_2 = 1;
x_3 = l_Lake_Module_bcFacetConfig___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_bcFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_bcFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_bcFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Module_bcFacetConfig___elambda__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c.o.export", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 8);
x_16 = l_System_FilePath_join(x_14, x_15);
x_17 = lean_ctor_get(x_2, 12);
x_18 = l_System_FilePath_join(x_16, x_17);
x_19 = l_Lake_Module_recBuildLeanCToOExport___lambda__1___closed__1;
x_20 = l_Lean_modToFilePath(x_18, x_3, x_19);
lean_dec(x_18);
x_21 = lean_ctor_get(x_4, 5);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_ctor_get(x_5, 5);
x_23 = l_Array_append___rarg(x_21, x_22);
x_24 = l_Lake_BuildTrace_nil;
x_25 = l_Lake_buildLeanO(x_20, x_7, x_23, x_6, x_8, x_9, x_10, x_11, x_24, x_13);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
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
lean_ctor_set(x_31, 1, x_12);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":c.o", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-DLEAN_EXPORTING", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_recBuildLeanCToOExport___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Module_recBuildLeanCToOExport___closed__3;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (with exports)", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
lean_dec(x_8);
x_10 = 2;
x_11 = l_Lake_instDecidableEqVerbosity(x_9, x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = 1;
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1;
lean_inc(x_12);
x_15 = l_Lean_Name_toString(x_12, x_13, x_14);
x_16 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lake_Module_recBuildLeanCToOExport___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*11);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*11);
x_28 = l_Lake_instOrdBuildType;
x_29 = lean_box(x_24);
x_30 = lean_box(x_27);
x_31 = l_Ord_instDecidableRelLe___rarg(x_28, x_29, x_30);
x_32 = lean_ctor_get(x_23, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 3);
lean_inc(x_33);
x_34 = l_Lake_Module_cFacetConfig___closed__1;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, lean_box(0));
if (x_11 == 0)
{
x_37 = x_16;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = l_Lake_Module_recBuildLeanCToOExport___closed__5;
x_37 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_string_append(x_19, x_37);
lean_dec(x_37);
x_39 = lean_string_append(x_38, x_16);
if (x_31 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = l_Lake_BuildType_leancArgs(x_27);
x_49 = l_Array_append___rarg(x_48, x_32);
lean_dec(x_32);
x_50 = l_Array_append___rarg(x_49, x_33);
lean_dec(x_33);
x_40 = x_50;
goto block_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = l_Lake_BuildType_leancArgs(x_24);
x_52 = l_Array_append___rarg(x_51, x_32);
lean_dec(x_32);
x_53 = l_Array_append___rarg(x_52, x_33);
lean_dec(x_33);
x_40 = x_53;
goto block_47;
}
block_47:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_41 = l_Lake_Module_recBuildLeanCToOExport___closed__4;
x_42 = l_Array_append___rarg(x_40, x_41);
x_43 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__1___boxed), 13, 6);
lean_closure_set(x_43, 0, x_21);
lean_closure_set(x_43, 1, x_22);
lean_closure_set(x_43, 2, x_12);
lean_closure_set(x_43, 3, x_23);
lean_closure_set(x_43, 4, x_26);
lean_closure_set(x_43, 5, x_42);
x_44 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg), 8, 2);
lean_closure_set(x_44, 0, x_36);
lean_closure_set(x_44, 1, x_43);
x_45 = 0;
x_46 = l_Lake_withRegisterJob___rarg(x_39, x_44, x_45, x_2, x_3, x_4, x_5, x_6, x_7);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_Module_recBuildLeanCToOExport___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("o", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("export", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_clearOutputHashes___closed__2;
x_2 = l_Lake_Module_coExportFacetConfig___closed__1;
x_3 = l_Lake_Module_coExportFacetConfig___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_coExportFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_coExportFacetConfig___closed__4;
x_2 = 1;
x_3 = l_Lake_Module_coExportFacetConfig___closed__5;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_coExportFacetConfig___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_coExportFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToONoExport___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c.o.noexport", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 8);
lean_inc(x_14);
x_15 = l_System_FilePath_join(x_12, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 12);
lean_inc(x_16);
x_17 = l_System_FilePath_join(x_15, x_16);
lean_dec(x_16);
x_18 = l_Lake_Module_recBuildLeanCToONoExport___lambda__1___closed__1;
x_19 = l_Lean_modToFilePath(x_17, x_2, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 5);
lean_inc(x_24);
x_25 = l_Array_append___rarg(x_21, x_24);
lean_dec(x_24);
x_26 = lean_ctor_get_uint8(x_20, sizeof(void*)*11);
x_27 = lean_ctor_get_uint8(x_23, sizeof(void*)*11);
x_28 = l_Lake_instOrdBuildType;
x_29 = lean_box(x_26);
x_30 = lean_box(x_27);
x_31 = l_Ord_instDecidableRelLe___rarg(x_28, x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_20, 3);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_23, 3);
lean_inc(x_33);
lean_dec(x_23);
x_34 = l_Lake_BuildType_leancArgs(x_27);
x_35 = l_Array_append___rarg(x_34, x_32);
lean_dec(x_32);
x_36 = l_Array_append___rarg(x_35, x_33);
lean_dec(x_33);
x_37 = l_Lake_BuildTrace_nil;
x_38 = l_Lake_buildLeanO(x_19, x_3, x_25, x_36, x_4, x_5, x_6, x_7, x_37, x_9);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_8);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_8);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_20, 3);
lean_inc(x_50);
lean_dec(x_20);
x_51 = lean_ctor_get(x_23, 3);
lean_inc(x_51);
lean_dec(x_23);
x_52 = l_Lake_BuildType_leancArgs(x_26);
x_53 = l_Array_append___rarg(x_52, x_50);
lean_dec(x_50);
x_54 = l_Array_append___rarg(x_53, x_51);
lean_dec(x_51);
x_55 = l_Lake_BuildTrace_nil;
x_56 = l_Lake_buildLeanO(x_19, x_3, x_25, x_54, x_4, x_5, x_6, x_7, x_55, x_9);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_8);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_8);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
x_64 = !lean_is_exclusive(x_56);
if (x_64 == 0)
{
return x_56;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_56, 0);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_56);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToONoExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (without exports)", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
lean_dec(x_8);
x_10 = 2;
x_11 = l_Lake_instDecidableEqVerbosity(x_9, x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = 1;
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1;
lean_inc(x_12);
x_15 = l_Lean_Name_toString(x_12, x_13, x_14);
x_16 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lake_Module_recBuildLeanCToOExport___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lake_Module_cFacetConfig___closed__1;
lean_inc(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, lean_box(0));
x_23 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToONoExport___lambda__1___boxed), 9, 2);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_12);
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg), 8, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
if (x_11 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_string_append(x_19, x_16);
x_26 = lean_string_append(x_25, x_16);
x_27 = 0;
x_28 = l_Lake_withRegisterJob___rarg(x_26, x_24, x_27, x_2, x_3, x_4, x_5, x_6, x_7);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = l_Lake_Module_recBuildLeanCToONoExport___closed__1;
x_30 = lean_string_append(x_19, x_29);
x_31 = lean_string_append(x_30, x_16);
x_32 = 0;
x_33 = l_Lake_withRegisterJob___rarg(x_31, x_24, x_32, x_2, x_3, x_4, x_5, x_6, x_7);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Module_recBuildLeanCToONoExport___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_coNoExportFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("noexport", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coNoExportFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_clearOutputHashes___closed__2;
x_2 = l_Lake_Module_coExportFacetConfig___closed__1;
x_3 = l_Lake_Module_coNoExportFacetConfig___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_coNoExportFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToONoExport), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coNoExportFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_coNoExportFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coNoExportFacetConfig___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_coNoExportFacetConfig___closed__3;
x_2 = 1;
x_3 = l_Lake_Module_coNoExportFacetConfig___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_coNoExportFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_coNoExportFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_coNoExportFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_System_Platform_isWindows;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lake_Module_coExportFacetConfig___closed__3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_6(x_2, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lake_Module_coNoExportFacetConfig___closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_apply_6(x_2, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
}
static lean_object* _init_l_Lake_Module_coFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_clearOutputHashes___closed__2;
x_2 = l_Lake_Module_coExportFacetConfig___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_coFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_coFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_coFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coFacetConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_coFacetConfig___closed__2;
x_2 = 1;
x_3 = l_Lake_Module_coFacetConfig___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_coFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_coFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_coFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanBcToO___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bc.o", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 8);
lean_inc(x_14);
x_15 = l_System_FilePath_join(x_12, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 12);
lean_inc(x_16);
x_17 = l_System_FilePath_join(x_15, x_16);
lean_dec(x_16);
x_18 = l_Lake_Module_recBuildLeanBcToO___lambda__1___closed__1;
x_19 = l_Lean_modToFilePath(x_17, x_2, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 5);
lean_inc(x_24);
x_25 = l_Array_append___rarg(x_21, x_24);
lean_dec(x_24);
x_26 = lean_ctor_get_uint8(x_20, sizeof(void*)*11);
x_27 = lean_ctor_get_uint8(x_23, sizeof(void*)*11);
x_28 = l_Lake_instOrdBuildType;
x_29 = lean_box(x_26);
x_30 = lean_box(x_27);
x_31 = l_Ord_instDecidableRelLe___rarg(x_28, x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_20, 3);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_23, 3);
lean_inc(x_33);
lean_dec(x_23);
x_34 = l_Lake_BuildType_leancArgs(x_27);
x_35 = l_Array_append___rarg(x_34, x_32);
lean_dec(x_32);
x_36 = l_Array_append___rarg(x_35, x_33);
lean_dec(x_33);
x_37 = l_Lake_BuildTrace_nil;
x_38 = l_Lake_buildLeanO(x_19, x_3, x_25, x_36, x_4, x_5, x_6, x_7, x_37, x_9);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_8);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_8);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_20, 3);
lean_inc(x_50);
lean_dec(x_20);
x_51 = lean_ctor_get(x_23, 3);
lean_inc(x_51);
lean_dec(x_23);
x_52 = l_Lake_BuildType_leancArgs(x_26);
x_53 = l_Array_append___rarg(x_52, x_50);
lean_dec(x_50);
x_54 = l_Array_append___rarg(x_53, x_51);
lean_dec(x_51);
x_55 = l_Lake_BuildTrace_nil;
x_56 = l_Lake_buildLeanO(x_19, x_3, x_25, x_54, x_4, x_5, x_6, x_7, x_55, x_9);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_8);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_8);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
x_64 = !lean_is_exclusive(x_56);
if (x_64 == 0)
{
return x_56;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_56, 0);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_56);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanBcToO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":bc.o", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1;
lean_inc(x_8);
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lake_Module_recBuildLeanBcToO___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lake_Module_bcFacetConfig___closed__1;
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, lean_box(0));
x_19 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanBcToO___lambda__1___boxed), 9, 2);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_8);
x_20 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg), 8, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = 0;
x_22 = l_Lake_withRegisterJob___rarg(x_15, x_20, x_21, x_2, x_3, x_4, x_5, x_6, x_7);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Module_recBuildLeanBcToO___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_bcoFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_clearOutputHashes___closed__4;
x_2 = l_Lake_Module_coExportFacetConfig___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_bcoFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanBcToO), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_bcoFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_bcoFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_bcoFacetConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_bcoFacetConfig___closed__2;
x_2 = 1;
x_3 = l_Lake_Module_bcoFacetConfig___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_bcoFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_bcoFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_bcoFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*11 + 1);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*11 + 1);
lean_dec(x_14);
x_16 = l_Lake_Backend_orPreferLeft(x_11, x_15);
x_17 = lean_box(x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lake_Module_bcoFacetConfig___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_apply_6(x_2, x_19, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
x_21 = l_Lake_Module_coExportFacetConfig___closed__3;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_apply_6(x_2, x_22, x_3, x_4, x_5, x_6, x_7);
return x_23;
}
}
}
static lean_object* _init_l_Lake_Module_oExportFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_coExportFacetConfig___closed__1;
x_2 = l_Lake_Module_coExportFacetConfig___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oExportFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oExportFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oExportFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oExportFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oExportFacetConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_oExportFacetConfig___closed__2;
x_2 = 1;
x_3 = l_Lake_Module_oExportFacetConfig___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_oExportFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_oExportFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_oExportFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the LLVM backend only supports exporting Lean symbols", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*11 + 1);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*11 + 1);
lean_dec(x_14);
x_16 = l_Lake_Backend_orPreferLeft(x_11, x_15);
x_17 = lean_box(x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_array_get_size(x_6);
x_19 = l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__2;
x_20 = lean_array_push(x_6, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
x_23 = l_Lake_Module_coNoExportFacetConfig___closed__2;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_apply_6(x_2, x_24, x_3, x_4, x_5, x_6, x_7);
return x_25;
}
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_coExportFacetConfig___closed__1;
x_2 = l_Lake_Module_coNoExportFacetConfig___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oNoExportFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oNoExportFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_oNoExportFacetConfig___closed__2;
x_2 = 1;
x_3 = l_Lake_Module_oNoExportFacetConfig___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_oNoExportFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_oNoExportFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_oleanFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*11 + 1);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*11 + 1);
lean_dec(x_14);
x_16 = l_Lake_Backend_orPreferLeft(x_11, x_15);
x_17 = lean_box(x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lake_Module_bcoFacetConfig___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_apply_6(x_2, x_19, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
x_21 = l_Lake_Module_coFacetConfig___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_apply_6(x_2, x_22, x_3, x_4, x_5, x_6, x_7);
return x_23;
}
}
}
static lean_object* _init_l_Lake_Module_oFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_coExportFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oFacetConfig___elambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oFacetConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_oFacetConfig___closed__2;
x_2 = 1;
x_3 = l_Lake_Module_oFacetConfig___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_oFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_oFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_oFacetConfig___elambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_21);
x_3 = x_24;
x_4 = x_25;
x_9 = x_22;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_size(x_1);
x_18 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_17, x_2, x_1);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_ctor_get(x_4, 7);
x_21 = l_Array_append___rarg(x_19, x_20);
if (x_5 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_8);
x_22 = lean_ctor_get(x_10, 18);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 12);
lean_inc(x_23);
lean_dec(x_10);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
x_27 = l_Array_append___rarg(x_18, x_21);
lean_dec(x_21);
x_28 = l_Array_append___rarg(x_27, x_6);
x_29 = l_Array_append___rarg(x_28, x_22);
lean_dec(x_22);
x_30 = l_Lake_compileSharedLib(x_7, x_29, x_23, x_25, x_16);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
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
x_35 = lean_ctor_get(x_31, 1);
lean_ctor_set(x_15, 0, x_35);
lean_ctor_set(x_31, 1, x_15);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
lean_ctor_set(x_15, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_15);
lean_ctor_set(x_30, 0, x_38);
return x_30;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_42 = x_31;
} else {
 lean_dec_ref(x_31);
 x_42 = lean_box(0);
}
lean_ctor_set(x_15, 0, x_41);
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_15);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_30, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_31, 1);
lean_ctor_set(x_15, 0, x_48);
lean_ctor_set(x_31, 1, x_15);
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_31, 0);
x_50 = lean_ctor_get(x_31, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_31);
lean_ctor_set(x_15, 0, x_50);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_15);
lean_ctor_set(x_30, 0, x_51);
return x_30;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_30, 1);
lean_inc(x_52);
lean_dec(x_30);
x_53 = lean_ctor_get(x_31, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_31, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_55 = x_31;
} else {
 lean_dec_ref(x_31);
 x_55 = lean_box(0);
}
lean_ctor_set(x_15, 0, x_54);
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_15);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_free_object(x_15);
lean_dec(x_26);
x_58 = !lean_is_exclusive(x_30);
if (x_58 == 0)
{
return x_30;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_30, 0);
x_60 = lean_ctor_get(x_30, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_30);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_15, 0);
x_63 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_64 = lean_ctor_get(x_15, 1);
lean_inc(x_64);
lean_inc(x_62);
lean_dec(x_15);
x_65 = l_Array_append___rarg(x_18, x_21);
lean_dec(x_21);
x_66 = l_Array_append___rarg(x_65, x_6);
x_67 = l_Array_append___rarg(x_66, x_22);
lean_dec(x_22);
x_68 = l_Lake_compileSharedLib(x_7, x_67, x_23, x_62, x_16);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
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
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_74 = x_69;
} else {
 lean_dec_ref(x_69);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_64);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_63);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_71;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_70);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_79 = x_68;
} else {
 lean_dec_ref(x_68);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_69, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_82 = x_69;
} else {
 lean_dec_ref(x_69);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_64);
lean_ctor_set_uint8(x_83, sizeof(void*)*2, x_63);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_79)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_79;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_64);
x_86 = lean_ctor_get(x_68, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_68, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_88 = x_68;
} else {
 lean_dec_ref(x_68);
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
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_10, 18);
lean_inc(x_90);
x_91 = lean_ctor_get(x_10, 12);
lean_inc(x_91);
lean_dec(x_10);
x_92 = !lean_is_exclusive(x_15);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; size_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_93 = lean_ctor_get(x_15, 0);
x_94 = lean_ctor_get(x_15, 1);
x_95 = l_Array_append___rarg(x_8, x_9);
x_96 = lean_array_size(x_95);
x_97 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_96, x_2, x_95);
x_98 = l_Array_append___rarg(x_18, x_97);
lean_dec(x_97);
x_99 = l_Array_append___rarg(x_98, x_21);
lean_dec(x_21);
x_100 = l_Array_append___rarg(x_99, x_6);
x_101 = l_Array_append___rarg(x_100, x_90);
lean_dec(x_90);
x_102 = l_Lake_compileSharedLib(x_7, x_101, x_91, x_93, x_16);
lean_dec(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_103, 1);
lean_ctor_set(x_15, 0, x_107);
lean_ctor_set(x_103, 1, x_15);
return x_102;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_103, 0);
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_103);
lean_ctor_set(x_15, 0, x_109);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_15);
lean_ctor_set(x_102, 0, x_110);
return x_102;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
lean_dec(x_102);
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_114 = x_103;
} else {
 lean_dec_ref(x_103);
 x_114 = lean_box(0);
}
lean_ctor_set(x_15, 0, x_113);
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_15);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
return x_116;
}
}
else
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_102);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_102, 0);
lean_dec(x_118);
x_119 = !lean_is_exclusive(x_103);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_103, 1);
lean_ctor_set(x_15, 0, x_120);
lean_ctor_set(x_103, 1, x_15);
return x_102;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_103, 0);
x_122 = lean_ctor_get(x_103, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_103);
lean_ctor_set(x_15, 0, x_122);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_15);
lean_ctor_set(x_102, 0, x_123);
return x_102;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_102, 1);
lean_inc(x_124);
lean_dec(x_102);
x_125 = lean_ctor_get(x_103, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_103, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_127 = x_103;
} else {
 lean_dec_ref(x_103);
 x_127 = lean_box(0);
}
lean_ctor_set(x_15, 0, x_126);
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_15);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_free_object(x_15);
lean_dec(x_94);
x_130 = !lean_is_exclusive(x_102);
if (x_130 == 0)
{
return x_102;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_102, 0);
x_132 = lean_ctor_get(x_102, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_102);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; size_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_134 = lean_ctor_get(x_15, 0);
x_135 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_136 = lean_ctor_get(x_15, 1);
lean_inc(x_136);
lean_inc(x_134);
lean_dec(x_15);
x_137 = l_Array_append___rarg(x_8, x_9);
x_138 = lean_array_size(x_137);
x_139 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_138, x_2, x_137);
x_140 = l_Array_append___rarg(x_18, x_139);
lean_dec(x_139);
x_141 = l_Array_append___rarg(x_140, x_21);
lean_dec(x_21);
x_142 = l_Array_append___rarg(x_141, x_6);
x_143 = l_Array_append___rarg(x_142, x_90);
lean_dec(x_90);
x_144 = l_Lake_compileSharedLib(x_7, x_143, x_91, x_134, x_16);
lean_dec(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_145, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_150 = x_145;
} else {
 lean_dec_ref(x_145);
 x_150 = lean_box(0);
}
x_151 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_136);
lean_ctor_set_uint8(x_151, sizeof(void*)*2, x_135);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
if (lean_is_scalar(x_147)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_147;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_146);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_154 = lean_ctor_get(x_144, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_155 = x_144;
} else {
 lean_dec_ref(x_144);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_145, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_145, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_158 = x_145;
} else {
 lean_dec_ref(x_145);
 x_158 = lean_box(0);
}
x_159 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_136);
lean_ctor_set_uint8(x_159, sizeof(void*)*2, x_135);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_159);
if (lean_is_scalar(x_155)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_155;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_154);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_136);
x_162 = lean_ctor_get(x_144, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_144, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_164 = x_144;
} else {
 lean_dec_ref(x_144);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_recBuildDynlib___lambda__4___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_instMonadStateOfLogJobM___spec__1___rarg), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_recBuildDynlib___lambda__4___closed__4;
x_2 = l_Lake_Module_recBuildDynlib___lambda__4___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_instMonadStateOfLogJobM___spec__1___rarg), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
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
x_19 = lean_ctor_get(x_12, 2);
lean_inc(x_19);
x_20 = l_Lake_BuildTrace_mix(x_17, x_19);
x_21 = l_Lake_Module_recBuildDeps___lambda__2___closed__3;
x_22 = l_Lake_BuildTrace_mix(x_20, x_21);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 6);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_ctor_get(x_27, 6);
lean_inc(x_28);
x_29 = l_Array_append___rarg(x_26, x_28);
lean_dec(x_28);
x_30 = lean_array_get_size(x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_ctor_get(x_24, 8);
lean_inc(x_34);
x_35 = l_System_FilePath_join(x_33, x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_24, 9);
lean_inc(x_36);
lean_dec(x_24);
x_37 = l_System_FilePath_join(x_35, x_36);
lean_dec(x_36);
x_38 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_39 = lean_name_mangle(x_3, x_38);
x_40 = lean_string_append(x_38, x_39);
x_41 = l_Lake_Module_recBuildDynlib___lambda__4___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_Lake_sharedLibExt;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_44, x_38);
x_46 = l_System_FilePath_join(x_37, x_45);
lean_dec(x_45);
x_47 = lean_box_usize(x_5);
x_48 = lean_box(x_6);
lean_inc(x_46);
lean_inc(x_29);
x_49 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 16, 9);
lean_closure_set(x_49, 0, x_4);
lean_closure_set(x_49, 1, x_47);
lean_closure_set(x_49, 2, x_25);
lean_closure_set(x_49, 3, x_27);
lean_closure_set(x_49, 4, x_48);
lean_closure_set(x_49, 5, x_29);
lean_closure_set(x_49, 6, x_46);
lean_closure_set(x_49, 7, x_7);
lean_closure_set(x_49, 8, x_8);
x_50 = l_Lake_Module_recBuildDynlib___lambda__4___closed__5;
x_51 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 8, 2);
lean_closure_set(x_51, 0, x_50);
lean_closure_set(x_51, 1, x_49);
if (x_32 == 0)
{
uint64_t x_92; 
lean_dec(x_30);
lean_dec(x_29);
x_92 = l_Lake_Hash_nil;
x_52 = x_92;
goto block_91;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_le(x_30, x_30);
if (x_93 == 0)
{
uint64_t x_94; 
lean_dec(x_30);
lean_dec(x_29);
x_94 = l_Lake_Hash_nil;
x_52 = x_94;
goto block_91;
}
else
{
size_t x_95; uint64_t x_96; uint64_t x_97; 
x_95 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_96 = l_Lake_Hash_nil;
x_97 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(x_29, x_5, x_95, x_96);
lean_dec(x_29);
x_52 = x_97;
goto block_91;
}
}
block_91:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_53 = l_Lake_Module_recBuildDeps___lambda__2___closed__2;
x_54 = lean_box_uint64(x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lake_BuildTrace_mix(x_22, x_55);
if (lean_is_scalar(x_18)) {
 x_57 = lean_alloc_ctor(0, 2, 1);
} else {
 x_57 = x_18;
}
lean_ctor_set(x_57, 0, x_15);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_16);
x_58 = 0;
lean_inc(x_46);
x_59 = l_Lake_buildFileUnlessUpToDate_x27(x_46, x_51, x_58, x_9, x_10, x_11, x_12, x_57, x_14);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_59, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_60, 0);
lean_dec(x_64);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_39);
lean_ctor_set(x_60, 0, x_65);
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_46);
lean_ctor_set(x_67, 1, x_39);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_59, 0, x_68);
return x_59;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_dec(x_59);
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_71 = x_60;
} else {
 lean_dec_ref(x_60);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_46);
lean_ctor_set(x_72, 1, x_39);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_46);
lean_dec(x_39);
x_75 = !lean_is_exclusive(x_59);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_59, 0);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_60);
if (x_77 == 0)
{
return x_59;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_60, 0);
x_79 = lean_ctor_get(x_60, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_60);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_59, 0, x_80);
return x_59;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_59, 1);
lean_inc(x_81);
lean_dec(x_59);
x_82 = lean_ctor_get(x_60, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_60, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_84 = x_60;
} else {
 lean_dec_ref(x_60);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_46);
lean_dec(x_39);
x_87 = !lean_is_exclusive(x_59);
if (x_87 == 0)
{
return x_59;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_59, 0);
x_89 = lean_ctor_get(x_59, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_59);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_box_usize(x_5);
x_16 = lean_box(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__4___boxed), 14, 7);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_15);
lean_closure_set(x_17, 5, x_16);
lean_closure_set(x_17, 6, x_8);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
x_19 = l_Task_Priority_default;
x_20 = 0;
x_21 = l_Lake_Job_mapM___rarg(x_7, x_17, x_19, x_20, x_9, x_10, x_11, x_12, x_18, x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
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
lean_ctor_set(x_27, 1, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_box_usize(x_4);
x_16 = lean_box(x_5);
x_17 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__5___boxed), 14, 7);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_8);
lean_closure_set(x_17, 4, x_15);
lean_closure_set(x_17, 5, x_16);
lean_closure_set(x_17, 6, x_6);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
x_19 = l_Task_Priority_default;
x_20 = 0;
x_21 = l_Lake_Job_bindM___rarg(x_7, x_17, x_19, x_20, x_9, x_10, x_11, x_12, x_18, x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
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
lean_ctor_set(x_27, 1, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_2 = l_Lake_Module_recParseImports___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Module_recBuildDynlib___lambda__7___closed__1;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lake_Module_recBuildDynlib___lambda__7___closed__2;
x_2 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Module_recBuildDynlib___lambda__7___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; uint8_t x_312; 
x_13 = l_Lake_Job_collectArray___rarg(x_6);
x_312 = l_System_Platform_isWindows;
if (x_312 == 0)
{
uint8_t x_313; 
x_313 = 0;
x_14 = x_313;
goto block_311;
}
else
{
uint8_t x_314; 
x_314 = 1;
x_14 = x_314;
goto block_311;
}
block_311:
{
lean_object* x_15; lean_object* x_76; lean_object* x_77; lean_object* x_166; lean_object* x_167; lean_object* x_183; lean_object* x_184; 
if (x_14 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_5);
x_208 = l_Lake_Module_recBuildDynlib___lambda__7___closed__4;
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_11);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_12);
x_15 = x_210;
goto block_75;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_5);
lean_ctor_set(x_212, 1, x_211);
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_213 = lean_apply_6(x_7, x_212, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
lean_dec(x_214);
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_io_wait(x_218, x_215);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
x_223 = !lean_is_exclusive(x_220);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_220, 0);
x_225 = lean_ctor_get(x_220, 1);
lean_dec(x_225);
x_226 = lean_ctor_get(x_221, 0);
lean_inc(x_226);
lean_dec(x_221);
x_227 = lean_array_get_size(x_226);
x_228 = lean_unsigned_to_nat(0u);
x_229 = lean_nat_dec_lt(x_228, x_227);
if (x_229 == 0)
{
lean_dec(x_227);
lean_dec(x_226);
lean_ctor_set(x_220, 1, x_217);
x_183 = x_220;
x_184 = x_222;
goto block_207;
}
else
{
uint8_t x_230; 
x_230 = lean_nat_dec_le(x_227, x_227);
if (x_230 == 0)
{
lean_dec(x_227);
lean_dec(x_226);
lean_ctor_set(x_220, 1, x_217);
x_183 = x_220;
x_184 = x_222;
goto block_207;
}
else
{
size_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
lean_free_object(x_220);
x_231 = lean_usize_of_nat(x_227);
lean_dec(x_227);
x_232 = lean_box(0);
x_233 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_226, x_4, x_231, x_232, x_217, x_222);
lean_dec(x_226);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = !lean_is_exclusive(x_234);
if (x_236 == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_234, 0);
lean_dec(x_237);
lean_ctor_set(x_234, 0, x_224);
x_183 = x_234;
x_184 = x_235;
goto block_207;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_234, 1);
lean_inc(x_238);
lean_dec(x_234);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_224);
lean_ctor_set(x_239, 1, x_238);
x_183 = x_239;
x_184 = x_235;
goto block_207;
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_240 = lean_ctor_get(x_220, 0);
lean_inc(x_240);
lean_dec(x_220);
x_241 = lean_ctor_get(x_221, 0);
lean_inc(x_241);
lean_dec(x_221);
x_242 = lean_array_get_size(x_241);
x_243 = lean_unsigned_to_nat(0u);
x_244 = lean_nat_dec_lt(x_243, x_242);
if (x_244 == 0)
{
lean_object* x_245; 
lean_dec(x_242);
lean_dec(x_241);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_240);
lean_ctor_set(x_245, 1, x_217);
x_183 = x_245;
x_184 = x_222;
goto block_207;
}
else
{
uint8_t x_246; 
x_246 = lean_nat_dec_le(x_242, x_242);
if (x_246 == 0)
{
lean_object* x_247; 
lean_dec(x_242);
lean_dec(x_241);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_240);
lean_ctor_set(x_247, 1, x_217);
x_183 = x_247;
x_184 = x_222;
goto block_207;
}
else
{
size_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_248 = lean_usize_of_nat(x_242);
lean_dec(x_242);
x_249 = lean_box(0);
x_250 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_241, x_4, x_248, x_249, x_217, x_222);
lean_dec(x_241);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_240);
lean_ctor_set(x_255, 1, x_253);
x_183 = x_255;
x_184 = x_252;
goto block_207;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_256 = lean_ctor_get(x_220, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_219, 1);
lean_inc(x_257);
lean_dec(x_219);
x_258 = !lean_is_exclusive(x_220);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_259 = lean_ctor_get(x_220, 0);
x_260 = lean_ctor_get(x_220, 1);
lean_dec(x_260);
x_261 = lean_ctor_get(x_256, 0);
lean_inc(x_261);
lean_dec(x_256);
x_262 = lean_array_get_size(x_261);
x_263 = lean_unsigned_to_nat(0u);
x_264 = lean_nat_dec_lt(x_263, x_262);
if (x_264 == 0)
{
lean_dec(x_262);
lean_dec(x_261);
lean_ctor_set(x_220, 1, x_217);
x_183 = x_220;
x_184 = x_257;
goto block_207;
}
else
{
uint8_t x_265; 
x_265 = lean_nat_dec_le(x_262, x_262);
if (x_265 == 0)
{
lean_dec(x_262);
lean_dec(x_261);
lean_ctor_set(x_220, 1, x_217);
x_183 = x_220;
x_184 = x_257;
goto block_207;
}
else
{
size_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
lean_free_object(x_220);
x_266 = lean_usize_of_nat(x_262);
lean_dec(x_262);
x_267 = lean_box(0);
x_268 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_261, x_4, x_266, x_267, x_217, x_257);
lean_dec(x_261);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = !lean_is_exclusive(x_269);
if (x_271 == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_269, 0);
lean_dec(x_272);
lean_ctor_set_tag(x_269, 1);
lean_ctor_set(x_269, 0, x_259);
x_183 = x_269;
x_184 = x_270;
goto block_207;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_269, 1);
lean_inc(x_273);
lean_dec(x_269);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_259);
lean_ctor_set(x_274, 1, x_273);
x_183 = x_274;
x_184 = x_270;
goto block_207;
}
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_275 = lean_ctor_get(x_220, 0);
lean_inc(x_275);
lean_dec(x_220);
x_276 = lean_ctor_get(x_256, 0);
lean_inc(x_276);
lean_dec(x_256);
x_277 = lean_array_get_size(x_276);
x_278 = lean_unsigned_to_nat(0u);
x_279 = lean_nat_dec_lt(x_278, x_277);
if (x_279 == 0)
{
lean_object* x_280; 
lean_dec(x_277);
lean_dec(x_276);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_275);
lean_ctor_set(x_280, 1, x_217);
x_183 = x_280;
x_184 = x_257;
goto block_207;
}
else
{
uint8_t x_281; 
x_281 = lean_nat_dec_le(x_277, x_277);
if (x_281 == 0)
{
lean_object* x_282; 
lean_dec(x_277);
lean_dec(x_276);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_275);
lean_ctor_set(x_282, 1, x_217);
x_183 = x_282;
x_184 = x_257;
goto block_207;
}
else
{
size_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_283 = lean_usize_of_nat(x_277);
lean_dec(x_277);
x_284 = lean_box(0);
x_285 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_276, x_4, x_283, x_284, x_217, x_257);
lean_dec(x_276);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_289 = x_286;
} else {
 lean_dec_ref(x_286);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
 lean_ctor_set_tag(x_290, 1);
}
lean_ctor_set(x_290, 0, x_275);
lean_ctor_set(x_290, 1, x_288);
x_183 = x_290;
x_184 = x_287;
goto block_207;
}
}
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_217);
x_291 = !lean_is_exclusive(x_219);
if (x_291 == 0)
{
x_15 = x_219;
goto block_75;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_219, 0);
x_293 = lean_ctor_get(x_219, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_219);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_15 = x_294;
goto block_75;
}
}
}
else
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_213);
if (x_295 == 0)
{
lean_object* x_296; uint8_t x_297; 
x_296 = lean_ctor_get(x_213, 0);
lean_dec(x_296);
x_297 = !lean_is_exclusive(x_214);
if (x_297 == 0)
{
x_15 = x_213;
goto block_75;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_214, 0);
x_299 = lean_ctor_get(x_214, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_214);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set(x_213, 0, x_300);
x_15 = x_213;
goto block_75;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_301 = lean_ctor_get(x_213, 1);
lean_inc(x_301);
lean_dec(x_213);
x_302 = lean_ctor_get(x_214, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_214, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_304 = x_214;
} else {
 lean_dec_ref(x_214);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_301);
x_15 = x_306;
goto block_75;
}
}
}
else
{
uint8_t x_307; 
x_307 = !lean_is_exclusive(x_213);
if (x_307 == 0)
{
x_15 = x_213;
goto block_75;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_213, 0);
x_309 = lean_ctor_get(x_213, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_213);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_15 = x_310;
goto block_75;
}
}
}
block_75:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box_usize(x_4);
x_25 = lean_box(x_14);
x_26 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__6___boxed), 14, 7);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_3);
lean_closure_set(x_26, 3, x_24);
lean_closure_set(x_26, 4, x_25);
lean_closure_set(x_26, 5, x_23);
lean_closure_set(x_26, 6, x_22);
x_27 = l_Task_Priority_default;
x_28 = 0;
x_29 = l_Lake_BuildTrace_nil;
x_30 = l_Lake_Job_bindM___rarg(x_13, x_26, x_27, x_28, x_7, x_8, x_9, x_10, x_29, x_18);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_16, 0, x_32);
lean_ctor_set(x_30, 0, x_16);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_16, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_16);
lean_dec(x_20);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_dec(x_16);
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_dec(x_17);
x_43 = lean_box_usize(x_4);
x_44 = lean_box(x_14);
x_45 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__6___boxed), 14, 7);
lean_closure_set(x_45, 0, x_1);
lean_closure_set(x_45, 1, x_2);
lean_closure_set(x_45, 2, x_3);
lean_closure_set(x_45, 3, x_43);
lean_closure_set(x_45, 4, x_44);
lean_closure_set(x_45, 5, x_42);
lean_closure_set(x_45, 6, x_41);
x_46 = l_Task_Priority_default;
x_47 = 0;
x_48 = l_Lake_BuildTrace_nil;
x_49 = l_Lake_Job_bindM___rarg(x_13, x_45, x_46, x_47, x_7, x_8, x_9, x_10, x_48, x_18);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
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
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_40);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_40);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_57 = x_49;
} else {
 lean_dec_ref(x_49);
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
uint8_t x_59; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_15, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_16);
if (x_61 == 0)
{
return x_15;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_16, 0);
x_63 = lean_ctor_get(x_16, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_16);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_15, 0, x_64);
return x_15;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_dec(x_15);
x_66 = lean_ctor_get(x_16, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_68 = x_16;
} else {
 lean_dec_ref(x_16);
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
uint8_t x_71; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_15);
if (x_71 == 0)
{
return x_15;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_15, 0);
x_73 = lean_ctor_get(x_15, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_15);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
block_165:
{
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_139; lean_object* x_140; 
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_139 = lean_array_size(x_78);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_78);
x_140 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(x_139, x_4, x_78, x_7, x_8, x_9, x_10, x_79, x_77);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = !lean_is_exclusive(x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_141, 0);
x_145 = l_Lake_Job_collectArray___rarg(x_144);
lean_dec(x_144);
lean_ctor_set(x_141, 0, x_145);
x_80 = x_141;
x_81 = x_142;
goto block_138;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_141, 0);
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_141);
x_148 = l_Lake_Job_collectArray___rarg(x_146);
lean_dec(x_146);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_80 = x_149;
x_81 = x_142;
goto block_138;
}
}
else
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_140, 1);
lean_inc(x_150);
lean_dec(x_140);
x_151 = !lean_is_exclusive(x_141);
if (x_151 == 0)
{
x_80 = x_141;
x_81 = x_150;
goto block_138;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_141, 0);
x_153 = lean_ctor_get(x_141, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_141);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_80 = x_154;
x_81 = x_150;
goto block_138;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_78);
x_155 = !lean_is_exclusive(x_140);
if (x_155 == 0)
{
x_15 = x_140;
goto block_75;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_140, 0);
x_157 = lean_ctor_get(x_140, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_140);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_15 = x_158;
goto block_75;
}
}
block_138:
{
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_array_get_size(x_78);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
if (x_86 == 0)
{
lean_object* x_126; 
lean_dec(x_84);
lean_dec(x_78);
x_126 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_88 = x_126;
goto block_125;
}
else
{
uint8_t x_127; 
x_127 = lean_nat_dec_le(x_84, x_84);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_84);
lean_dec(x_78);
x_128 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_88 = x_128;
goto block_125;
}
else
{
size_t x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_130 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_131 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__10(x_78, x_4, x_129, x_130);
lean_dec(x_78);
x_88 = x_131;
goto block_125;
}
}
block_125:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4(x_88, x_87);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_91 = l_Lake_fetchExternLibs(x_90, x_7, x_8, x_9, x_10, x_83, x_81);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_91, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_92);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_92, 0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_82);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_92, 0, x_97);
x_15 = x_91;
goto block_75;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_92, 0);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_82);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_91, 0, x_101);
x_15 = x_91;
goto block_75;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
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
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_82);
lean_ctor_set(x_106, 1, x_103);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_102);
x_15 = x_108;
goto block_75;
}
}
else
{
uint8_t x_109; 
lean_dec(x_82);
x_109 = !lean_is_exclusive(x_91);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_91, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_92);
if (x_111 == 0)
{
x_15 = x_91;
goto block_75;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_92, 0);
x_113 = lean_ctor_get(x_92, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_92);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_91, 0, x_114);
x_15 = x_91;
goto block_75;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_91, 1);
lean_inc(x_115);
lean_dec(x_91);
x_116 = lean_ctor_get(x_92, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_92, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_118 = x_92;
} else {
 lean_dec_ref(x_92);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_115);
x_15 = x_120;
goto block_75;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_82);
x_121 = !lean_is_exclusive(x_91);
if (x_121 == 0)
{
x_15 = x_91;
goto block_75;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_91, 0);
x_123 = lean_ctor_get(x_91, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_91);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_15 = x_124;
goto block_75;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_78);
x_132 = !lean_is_exclusive(x_80);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_80);
lean_ctor_set(x_133, 1, x_81);
x_15 = x_133;
goto block_75;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_80, 0);
x_135 = lean_ctor_get(x_80, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_80);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_81);
x_15 = x_137;
goto block_75;
}
}
}
}
else
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_76);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_76);
lean_ctor_set(x_160, 1, x_77);
x_15 = x_160;
goto block_75;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_76, 0);
x_162 = lean_ctor_get(x_76, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_76);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_77);
x_15 = x_164;
goto block_75;
}
}
}
block_182:
{
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_166, 1);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec(x_169);
lean_ctor_set(x_166, 1, x_170);
x_76 = x_166;
x_77 = x_167;
goto block_165;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_166, 0);
x_172 = lean_ctor_get(x_166, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_166);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_173);
x_76 = x_174;
x_77 = x_167;
goto block_165;
}
}
else
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_166);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_166, 1);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec(x_176);
lean_ctor_set(x_166, 1, x_177);
x_76 = x_166;
x_77 = x_167;
goto block_165;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_166, 0);
x_179 = lean_ctor_get(x_166, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_166);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_180);
x_76 = x_181;
x_77 = x_167;
goto block_165;
}
}
}
block_207:
{
if (lean_obj_tag(x_183) == 0)
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_183);
if (x_185 == 0)
{
lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_183, 1);
x_187 = 0;
x_188 = l_Lake_BuildTrace_nil;
x_189 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*2, x_187);
lean_ctor_set(x_183, 1, x_189);
x_166 = x_183;
x_167 = x_184;
goto block_182;
}
else
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_ctor_get(x_183, 0);
x_191 = lean_ctor_get(x_183, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_183);
x_192 = 0;
x_193 = l_Lake_BuildTrace_nil;
x_194 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*2, x_192);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_190);
lean_ctor_set(x_195, 1, x_194);
x_166 = x_195;
x_167 = x_184;
goto block_182;
}
}
else
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_183);
if (x_196 == 0)
{
lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_183, 1);
x_198 = 0;
x_199 = l_Lake_BuildTrace_nil;
x_200 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set_uint8(x_200, sizeof(void*)*2, x_198);
lean_ctor_set(x_183, 1, x_200);
x_166 = x_183;
x_167 = x_184;
goto block_182;
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_183, 0);
x_202 = lean_ctor_get(x_183, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_183);
x_203 = 0;
x_204 = l_Lake_BuildTrace_nil;
x_205 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set_uint8(x_205, sizeof(void*)*2, x_203);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_201);
lean_ctor_set(x_206, 1, x_205);
x_166 = x_206;
x_167 = x_184;
goto block_182;
}
}
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":dynlib", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1;
lean_inc(x_8);
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = l_Lake_Module_recParseImports___lambda__4___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lake_Module_recBuildDynlib___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 8);
lean_inc(x_18);
x_19 = lean_box(x_9);
x_20 = lean_apply_1(x_18, x_19);
x_21 = lean_array_size(x_20);
x_22 = lean_box_usize(x_21);
x_23 = l_Lake_Module_recBuildDynlib___boxed__const__1;
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1___boxed), 10, 4);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_20);
x_25 = l_Lake_Module_recBuildDynlib___boxed__const__1;
x_26 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__7___boxed), 12, 5);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_17);
lean_closure_set(x_26, 2, x_8);
lean_closure_set(x_26, 3, x_25);
lean_closure_set(x_26, 4, x_1);
x_27 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recComputeTransImports___spec__3___rarg), 8, 2);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_26);
x_28 = 0;
x_29 = l_Lake_withRegisterJob___rarg(x_15, x_27, x_28, x_2, x_3, x_4, x_5, x_6, x_7);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Module_recBuildDynlib___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Module_recBuildDynlib___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Lake_Module_recBuildDynlib___lambda__3(x_1, x_17, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l_Lake_Module_recBuildDynlib___lambda__4(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l_Lake_Module_recBuildDynlib___lambda__5(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lake_Module_recBuildDynlib___lambda__6(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Lake_Module_recBuildDynlib___lambda__7(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_dynlibFacetConfig___elambda__1___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFacetConfig___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at_Lake_Module_dynlibFacetConfig___elambda__1___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_dynlibFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_dynlibFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_dynlibFacetConfig___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_dynlibFacetConfig___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_dynlibFacetConfig___closed__1;
x_2 = 1;
x_3 = l_Lake_Module_dynlibFacetConfig___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_dynlibFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_dynlibFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_Module_dynlibFacetConfig___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at_Lake_Module_dynlibFacetConfig___elambda__1___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFacetConfig___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Module_dynlibFacetConfig___elambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_importsFacetConfig___closed__2;
x_3 = l_Lake_Module_importsFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
x_3 = l_Lake_Module_transImportsFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
x_3 = l_Lake_Module_precompileImportsFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__3;
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
x_3 = l_Lake_Module_depsFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__4;
x_2 = l_Lake_Module_leanArtsFacetConfig___closed__2;
x_3 = l_Lake_Module_leanArtsFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__5;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__2;
x_3 = l_Lake_Module_oleanFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__6;
x_2 = l_Lake_Module_ileanFacetConfig___closed__1;
x_3 = l_Lake_Module_ileanFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__7;
x_2 = l_Lake_Module_cFacetConfig___closed__1;
x_3 = l_Lake_Module_cFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__8;
x_2 = l_Lake_Module_bcFacetConfig___closed__1;
x_3 = l_Lake_Module_bcFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__9;
x_2 = l_Lake_Module_coFacetConfig___closed__1;
x_3 = l_Lake_Module_coFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__10;
x_2 = l_Lake_Module_coExportFacetConfig___closed__3;
x_3 = l_Lake_Module_coExportFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__11;
x_2 = l_Lake_Module_coNoExportFacetConfig___closed__2;
x_3 = l_Lake_Module_coNoExportFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__12;
x_2 = l_Lake_Module_bcoFacetConfig___closed__1;
x_3 = l_Lake_Module_bcoFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__13;
x_2 = l_Lake_Module_oFacetConfig___closed__1;
x_3 = l_Lake_Module_oFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__14;
x_2 = l_Lake_Module_oExportFacetConfig___closed__1;
x_3 = l_Lake_Module_oExportFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__15;
x_2 = l_Lake_Module_oNoExportFacetConfig___closed__1;
x_3 = l_Lake_Module_oNoExportFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initModuleFacetConfigs___closed__16;
x_2 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2;
x_3 = l_Lake_Module_dynlibFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initModuleFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_initModuleFacetConfigs___closed__17;
return x_1;
}
}
lean_object* initialize_Lake_Util_OrdHashSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_List(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Target(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Module(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_OrdHashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ParseImportsFast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Target(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1);
l_Lake_recBuildExternDynlibs___closed__1 = _init_l_Lake_recBuildExternDynlibs___closed__1();
lean_mark_persistent(l_Lake_recBuildExternDynlibs___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__8___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__2);
l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__4);
l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Module_recParseImports___spec__9___closed__5);
l_Lake_Module_recParseImports___lambda__2___closed__1 = _init_l_Lake_Module_recParseImports___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Module_recParseImports___lambda__2___closed__1);
l_Lake_Module_recParseImports___lambda__4___closed__1 = _init_l_Lake_Module_recParseImports___lambda__4___closed__1();
lean_mark_persistent(l_Lake_Module_recParseImports___lambda__4___closed__1);
l_Lake_Module_recParseImports___lambda__4___closed__2 = _init_l_Lake_Module_recParseImports___lambda__4___closed__2();
lean_mark_persistent(l_Lake_Module_recParseImports___lambda__4___closed__2);
l_Lake_Module_recParseImports___closed__1 = _init_l_Lake_Module_recParseImports___closed__1();
lean_mark_persistent(l_Lake_Module_recParseImports___closed__1);
l_Lake_Module_recParseImports___closed__2 = _init_l_Lake_Module_recParseImports___closed__2();
lean_mark_persistent(l_Lake_Module_recParseImports___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_importsFacetConfig___elambda__1___spec__2___closed__2);
l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__1 = _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__1();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__1);
l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__2 = _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__2();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__2);
l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__3 = _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__3();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__3);
l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__4 = _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__4();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__4);
l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__5 = _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__5();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__5);
l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__6 = _init_l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__6();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_Module_importsFacetConfig___elambda__1___spec__1___closed__6);
l_Lake_Module_importsFacetConfig___closed__1 = _init_l_Lake_Module_importsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__1);
l_Lake_Module_importsFacetConfig___closed__2 = _init_l_Lake_Module_importsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__2);
l_Lake_Module_importsFacetConfig___closed__3 = _init_l_Lake_Module_importsFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__3);
l_Lake_Module_importsFacetConfig___closed__4 = _init_l_Lake_Module_importsFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__4);
l_Lake_Module_importsFacetConfig___closed__5 = _init_l_Lake_Module_importsFacetConfig___closed__5();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__5);
l_Lake_Module_importsFacetConfig = _init_l_Lake_Module_importsFacetConfig();
lean_mark_persistent(l_Lake_Module_importsFacetConfig);
l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__4___lambda__1___closed__2);
l_Lake_collectImportsAux___closed__1 = _init_l_Lake_collectImportsAux___closed__1();
lean_mark_persistent(l_Lake_collectImportsAux___closed__1);
l_Lake_collectImportsAux___closed__2 = _init_l_Lake_collectImportsAux___closed__2();
lean_mark_persistent(l_Lake_collectImportsAux___closed__2);
l_Lake_collectImportsAux___closed__3 = _init_l_Lake_collectImportsAux___closed__3();
lean_mark_persistent(l_Lake_collectImportsAux___closed__3);
l_Lake_collectImportsAux___closed__4 = _init_l_Lake_collectImportsAux___closed__4();
lean_mark_persistent(l_Lake_collectImportsAux___closed__4);
l_Lake_collectImportsAux___closed__5 = _init_l_Lake_collectImportsAux___closed__5();
lean_mark_persistent(l_Lake_collectImportsAux___closed__5);
l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recComputeTransImports___spec__1___closed__2);
l_Lake_Module_transImportsFacetConfig___closed__1 = _init_l_Lake_Module_transImportsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig___closed__1);
l_Lake_Module_transImportsFacetConfig___closed__2 = _init_l_Lake_Module_transImportsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig___closed__2);
l_Lake_Module_transImportsFacetConfig___closed__3 = _init_l_Lake_Module_transImportsFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig___closed__3);
l_Lake_Module_transImportsFacetConfig = _init_l_Lake_Module_transImportsFacetConfig();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig);
l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_computePrecompileImportsAux___spec__1___closed__2);
l_Lake_Module_precompileImportsFacetConfig___closed__1 = _init_l_Lake_Module_precompileImportsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_precompileImportsFacetConfig___closed__1);
l_Lake_Module_precompileImportsFacetConfig___closed__2 = _init_l_Lake_Module_precompileImportsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_precompileImportsFacetConfig___closed__2);
l_Lake_Module_precompileImportsFacetConfig___closed__3 = _init_l_Lake_Module_precompileImportsFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_precompileImportsFacetConfig___closed__3);
l_Lake_Module_precompileImportsFacetConfig = _init_l_Lake_Module_precompileImportsFacetConfig();
lean_mark_persistent(l_Lake_Module_precompileImportsFacetConfig);
l_Lake_fetchExternLibs___closed__1 = _init_l_Lake_fetchExternLibs___closed__1();
lean_mark_persistent(l_Lake_fetchExternLibs___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__2);
l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2);
l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__4___closed__2);
l_Lake_Module_recBuildDeps___lambda__2___closed__1 = _init_l_Lake_Module_recBuildDeps___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDeps___lambda__2___closed__1);
l_Lake_Module_recBuildDeps___lambda__2___closed__2 = _init_l_Lake_Module_recBuildDeps___lambda__2___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildDeps___lambda__2___closed__2);
l_Lake_Module_recBuildDeps___lambda__2___closed__3___boxed__const__1 = _init_l_Lake_Module_recBuildDeps___lambda__2___closed__3___boxed__const__1();
lean_mark_persistent(l_Lake_Module_recBuildDeps___lambda__2___closed__3___boxed__const__1);
l_Lake_Module_recBuildDeps___lambda__2___closed__3 = _init_l_Lake_Module_recBuildDeps___lambda__2___closed__3();
lean_mark_persistent(l_Lake_Module_recBuildDeps___lambda__2___closed__3);
l_Lake_Module_recBuildDeps___closed__1 = _init_l_Lake_Module_recBuildDeps___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDeps___closed__1);
l_Lake_Module_recBuildDeps___closed__2 = _init_l_Lake_Module_recBuildDeps___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildDeps___closed__2);
l_Lake_Module_depsFacetConfig___closed__1 = _init_l_Lake_Module_depsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_depsFacetConfig___closed__1);
l_Lake_Module_depsFacetConfig___closed__2 = _init_l_Lake_Module_depsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_depsFacetConfig___closed__2);
l_Lake_Module_depsFacetConfig___closed__3 = _init_l_Lake_Module_depsFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_depsFacetConfig___closed__3);
l_Lake_Module_depsFacetConfig___closed__4 = _init_l_Lake_Module_depsFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_depsFacetConfig___closed__4);
l_Lake_Module_depsFacetConfig___closed__5 = _init_l_Lake_Module_depsFacetConfig___closed__5();
lean_mark_persistent(l_Lake_Module_depsFacetConfig___closed__5);
l_Lake_Module_depsFacetConfig = _init_l_Lake_Module_depsFacetConfig();
lean_mark_persistent(l_Lake_Module_depsFacetConfig);
l_Lake_Module_clearOutputHashes___closed__1 = _init_l_Lake_Module_clearOutputHashes___closed__1();
lean_mark_persistent(l_Lake_Module_clearOutputHashes___closed__1);
l_Lake_Module_clearOutputHashes___closed__2 = _init_l_Lake_Module_clearOutputHashes___closed__2();
lean_mark_persistent(l_Lake_Module_clearOutputHashes___closed__2);
l_Lake_Module_clearOutputHashes___closed__3 = _init_l_Lake_Module_clearOutputHashes___closed__3();
l_Lake_Module_clearOutputHashes___closed__4 = _init_l_Lake_Module_clearOutputHashes___closed__4();
lean_mark_persistent(l_Lake_Module_clearOutputHashes___closed__4);
l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__1 = _init_l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__1();
lean_mark_persistent(l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__1);
l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__2 = _init_l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__2();
lean_mark_persistent(l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__2);
l_Lake_Module_recBuildLean___lambda__1___closed__1 = _init_l_Lake_Module_recBuildLean___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLean___lambda__1___closed__1);
l_Lake_Module_leanArtsFacetConfig___closed__1 = _init_l_Lake_Module_leanArtsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_leanArtsFacetConfig___closed__1);
l_Lake_Module_leanArtsFacetConfig___closed__2 = _init_l_Lake_Module_leanArtsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_leanArtsFacetConfig___closed__2);
l_Lake_Module_leanArtsFacetConfig___closed__3 = _init_l_Lake_Module_leanArtsFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_leanArtsFacetConfig___closed__3);
l_Lake_Module_leanArtsFacetConfig___closed__4 = _init_l_Lake_Module_leanArtsFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_leanArtsFacetConfig___closed__4);
l_Lake_Module_leanArtsFacetConfig___closed__5 = _init_l_Lake_Module_leanArtsFacetConfig___closed__5();
lean_mark_persistent(l_Lake_Module_leanArtsFacetConfig___closed__5);
l_Lake_Module_leanArtsFacetConfig = _init_l_Lake_Module_leanArtsFacetConfig();
lean_mark_persistent(l_Lake_Module_leanArtsFacetConfig);
l_Lake_Module_oleanFacetConfig___closed__1 = _init_l_Lake_Module_oleanFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig___closed__1);
l_Lake_Module_oleanFacetConfig___closed__2 = _init_l_Lake_Module_oleanFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig___closed__2);
l_Lake_Module_oleanFacetConfig___closed__3 = _init_l_Lake_Module_oleanFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig___closed__3);
l_Lake_Module_oleanFacetConfig = _init_l_Lake_Module_oleanFacetConfig();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig);
l_Lake_Module_ileanFacetConfig___closed__1 = _init_l_Lake_Module_ileanFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_ileanFacetConfig___closed__1);
l_Lake_Module_ileanFacetConfig___closed__2 = _init_l_Lake_Module_ileanFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_ileanFacetConfig___closed__2);
l_Lake_Module_ileanFacetConfig___closed__3 = _init_l_Lake_Module_ileanFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_ileanFacetConfig___closed__3);
l_Lake_Module_ileanFacetConfig___closed__4 = _init_l_Lake_Module_ileanFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_ileanFacetConfig___closed__4);
l_Lake_Module_ileanFacetConfig = _init_l_Lake_Module_ileanFacetConfig();
lean_mark_persistent(l_Lake_Module_ileanFacetConfig);
l_Lake_Module_cFacetConfig___closed__1 = _init_l_Lake_Module_cFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_cFacetConfig___closed__1);
l_Lake_Module_cFacetConfig___closed__2 = _init_l_Lake_Module_cFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_cFacetConfig___closed__2);
l_Lake_Module_cFacetConfig___closed__3 = _init_l_Lake_Module_cFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_cFacetConfig___closed__3);
l_Lake_Module_cFacetConfig___closed__4 = _init_l_Lake_Module_cFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_cFacetConfig___closed__4);
l_Lake_Module_cFacetConfig = _init_l_Lake_Module_cFacetConfig();
lean_mark_persistent(l_Lake_Module_cFacetConfig);
l_Lake_Module_bcFacetConfig___closed__1 = _init_l_Lake_Module_bcFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_bcFacetConfig___closed__1);
l_Lake_Module_bcFacetConfig___closed__2 = _init_l_Lake_Module_bcFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_bcFacetConfig___closed__2);
l_Lake_Module_bcFacetConfig___closed__3 = _init_l_Lake_Module_bcFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_bcFacetConfig___closed__3);
l_Lake_Module_bcFacetConfig___closed__4 = _init_l_Lake_Module_bcFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_bcFacetConfig___closed__4);
l_Lake_Module_bcFacetConfig = _init_l_Lake_Module_bcFacetConfig();
lean_mark_persistent(l_Lake_Module_bcFacetConfig);
l_Lake_Module_recBuildLeanCToOExport___lambda__1___closed__1 = _init_l_Lake_Module_recBuildLeanCToOExport___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToOExport___lambda__1___closed__1);
l_Lake_Module_recBuildLeanCToOExport___closed__1 = _init_l_Lake_Module_recBuildLeanCToOExport___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToOExport___closed__1);
l_Lake_Module_recBuildLeanCToOExport___closed__2 = _init_l_Lake_Module_recBuildLeanCToOExport___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToOExport___closed__2);
l_Lake_Module_recBuildLeanCToOExport___closed__3 = _init_l_Lake_Module_recBuildLeanCToOExport___closed__3();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToOExport___closed__3);
l_Lake_Module_recBuildLeanCToOExport___closed__4 = _init_l_Lake_Module_recBuildLeanCToOExport___closed__4();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToOExport___closed__4);
l_Lake_Module_recBuildLeanCToOExport___closed__5 = _init_l_Lake_Module_recBuildLeanCToOExport___closed__5();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToOExport___closed__5);
l_Lake_Module_coExportFacetConfig___closed__1 = _init_l_Lake_Module_coExportFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_coExportFacetConfig___closed__1);
l_Lake_Module_coExportFacetConfig___closed__2 = _init_l_Lake_Module_coExportFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_coExportFacetConfig___closed__2);
l_Lake_Module_coExportFacetConfig___closed__3 = _init_l_Lake_Module_coExportFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_coExportFacetConfig___closed__3);
l_Lake_Module_coExportFacetConfig___closed__4 = _init_l_Lake_Module_coExportFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_coExportFacetConfig___closed__4);
l_Lake_Module_coExportFacetConfig___closed__5 = _init_l_Lake_Module_coExportFacetConfig___closed__5();
lean_mark_persistent(l_Lake_Module_coExportFacetConfig___closed__5);
l_Lake_Module_coExportFacetConfig___closed__6 = _init_l_Lake_Module_coExportFacetConfig___closed__6();
lean_mark_persistent(l_Lake_Module_coExportFacetConfig___closed__6);
l_Lake_Module_coExportFacetConfig = _init_l_Lake_Module_coExportFacetConfig();
lean_mark_persistent(l_Lake_Module_coExportFacetConfig);
l_Lake_Module_recBuildLeanCToONoExport___lambda__1___closed__1 = _init_l_Lake_Module_recBuildLeanCToONoExport___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToONoExport___lambda__1___closed__1);
l_Lake_Module_recBuildLeanCToONoExport___closed__1 = _init_l_Lake_Module_recBuildLeanCToONoExport___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToONoExport___closed__1);
l_Lake_Module_coNoExportFacetConfig___closed__1 = _init_l_Lake_Module_coNoExportFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_coNoExportFacetConfig___closed__1);
l_Lake_Module_coNoExportFacetConfig___closed__2 = _init_l_Lake_Module_coNoExportFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_coNoExportFacetConfig___closed__2);
l_Lake_Module_coNoExportFacetConfig___closed__3 = _init_l_Lake_Module_coNoExportFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_coNoExportFacetConfig___closed__3);
l_Lake_Module_coNoExportFacetConfig___closed__4 = _init_l_Lake_Module_coNoExportFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_coNoExportFacetConfig___closed__4);
l_Lake_Module_coNoExportFacetConfig___closed__5 = _init_l_Lake_Module_coNoExportFacetConfig___closed__5();
lean_mark_persistent(l_Lake_Module_coNoExportFacetConfig___closed__5);
l_Lake_Module_coNoExportFacetConfig = _init_l_Lake_Module_coNoExportFacetConfig();
lean_mark_persistent(l_Lake_Module_coNoExportFacetConfig);
l_Lake_Module_coFacetConfig___closed__1 = _init_l_Lake_Module_coFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_coFacetConfig___closed__1);
l_Lake_Module_coFacetConfig___closed__2 = _init_l_Lake_Module_coFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_coFacetConfig___closed__2);
l_Lake_Module_coFacetConfig___closed__3 = _init_l_Lake_Module_coFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_coFacetConfig___closed__3);
l_Lake_Module_coFacetConfig___closed__4 = _init_l_Lake_Module_coFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_coFacetConfig___closed__4);
l_Lake_Module_coFacetConfig = _init_l_Lake_Module_coFacetConfig();
lean_mark_persistent(l_Lake_Module_coFacetConfig);
l_Lake_Module_recBuildLeanBcToO___lambda__1___closed__1 = _init_l_Lake_Module_recBuildLeanBcToO___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLeanBcToO___lambda__1___closed__1);
l_Lake_Module_recBuildLeanBcToO___closed__1 = _init_l_Lake_Module_recBuildLeanBcToO___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLeanBcToO___closed__1);
l_Lake_Module_bcoFacetConfig___closed__1 = _init_l_Lake_Module_bcoFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_bcoFacetConfig___closed__1);
l_Lake_Module_bcoFacetConfig___closed__2 = _init_l_Lake_Module_bcoFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_bcoFacetConfig___closed__2);
l_Lake_Module_bcoFacetConfig___closed__3 = _init_l_Lake_Module_bcoFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_bcoFacetConfig___closed__3);
l_Lake_Module_bcoFacetConfig___closed__4 = _init_l_Lake_Module_bcoFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_bcoFacetConfig___closed__4);
l_Lake_Module_bcoFacetConfig = _init_l_Lake_Module_bcoFacetConfig();
lean_mark_persistent(l_Lake_Module_bcoFacetConfig);
l_Lake_Module_oExportFacetConfig___closed__1 = _init_l_Lake_Module_oExportFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_oExportFacetConfig___closed__1);
l_Lake_Module_oExportFacetConfig___closed__2 = _init_l_Lake_Module_oExportFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_oExportFacetConfig___closed__2);
l_Lake_Module_oExportFacetConfig___closed__3 = _init_l_Lake_Module_oExportFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_oExportFacetConfig___closed__3);
l_Lake_Module_oExportFacetConfig___closed__4 = _init_l_Lake_Module_oExportFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_oExportFacetConfig___closed__4);
l_Lake_Module_oExportFacetConfig = _init_l_Lake_Module_oExportFacetConfig();
lean_mark_persistent(l_Lake_Module_oExportFacetConfig);
l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__1 = _init_l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__1();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__1);
l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__2 = _init_l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__2();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___elambda__2___closed__2);
l_Lake_Module_oNoExportFacetConfig___closed__1 = _init_l_Lake_Module_oNoExportFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___closed__1);
l_Lake_Module_oNoExportFacetConfig___closed__2 = _init_l_Lake_Module_oNoExportFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___closed__2);
l_Lake_Module_oNoExportFacetConfig___closed__3 = _init_l_Lake_Module_oNoExportFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___closed__3);
l_Lake_Module_oNoExportFacetConfig___closed__4 = _init_l_Lake_Module_oNoExportFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___closed__4);
l_Lake_Module_oNoExportFacetConfig = _init_l_Lake_Module_oNoExportFacetConfig();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig);
l_Lake_Module_oFacetConfig___closed__1 = _init_l_Lake_Module_oFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_oFacetConfig___closed__1);
l_Lake_Module_oFacetConfig___closed__2 = _init_l_Lake_Module_oFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_oFacetConfig___closed__2);
l_Lake_Module_oFacetConfig___closed__3 = _init_l_Lake_Module_oFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_oFacetConfig___closed__3);
l_Lake_Module_oFacetConfig___closed__4 = _init_l_Lake_Module_oFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_oFacetConfig___closed__4);
l_Lake_Module_oFacetConfig = _init_l_Lake_Module_oFacetConfig();
lean_mark_persistent(l_Lake_Module_oFacetConfig);
l_Lake_Module_recBuildDynlib___lambda__4___closed__1 = _init_l_Lake_Module_recBuildDynlib___lambda__4___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__4___closed__1);
l_Lake_Module_recBuildDynlib___lambda__4___closed__2 = _init_l_Lake_Module_recBuildDynlib___lambda__4___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__4___closed__2);
l_Lake_Module_recBuildDynlib___lambda__4___closed__3 = _init_l_Lake_Module_recBuildDynlib___lambda__4___closed__3();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__4___closed__3);
l_Lake_Module_recBuildDynlib___lambda__4___closed__4 = _init_l_Lake_Module_recBuildDynlib___lambda__4___closed__4();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__4___closed__4);
l_Lake_Module_recBuildDynlib___lambda__4___closed__5 = _init_l_Lake_Module_recBuildDynlib___lambda__4___closed__5();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__4___closed__5);
l_Lake_Module_recBuildDynlib___lambda__7___closed__1 = _init_l_Lake_Module_recBuildDynlib___lambda__7___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__7___closed__1);
l_Lake_Module_recBuildDynlib___lambda__7___closed__2 = _init_l_Lake_Module_recBuildDynlib___lambda__7___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__7___closed__2);
l_Lake_Module_recBuildDynlib___lambda__7___closed__3 = _init_l_Lake_Module_recBuildDynlib___lambda__7___closed__3();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__7___closed__3);
l_Lake_Module_recBuildDynlib___lambda__7___closed__4 = _init_l_Lake_Module_recBuildDynlib___lambda__7___closed__4();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__7___closed__4);
l_Lake_Module_recBuildDynlib___closed__1 = _init_l_Lake_Module_recBuildDynlib___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___closed__1);
l_Lake_Module_recBuildDynlib___boxed__const__1 = _init_l_Lake_Module_recBuildDynlib___boxed__const__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___boxed__const__1);
l_Lake_Module_dynlibFacetConfig___closed__1 = _init_l_Lake_Module_dynlibFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_dynlibFacetConfig___closed__1);
l_Lake_Module_dynlibFacetConfig___closed__2 = _init_l_Lake_Module_dynlibFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_dynlibFacetConfig___closed__2);
l_Lake_Module_dynlibFacetConfig___closed__3 = _init_l_Lake_Module_dynlibFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_dynlibFacetConfig___closed__3);
l_Lake_Module_dynlibFacetConfig = _init_l_Lake_Module_dynlibFacetConfig();
lean_mark_persistent(l_Lake_Module_dynlibFacetConfig);
l_Lake_initModuleFacetConfigs___closed__1 = _init_l_Lake_initModuleFacetConfigs___closed__1();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__1);
l_Lake_initModuleFacetConfigs___closed__2 = _init_l_Lake_initModuleFacetConfigs___closed__2();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__2);
l_Lake_initModuleFacetConfigs___closed__3 = _init_l_Lake_initModuleFacetConfigs___closed__3();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__3);
l_Lake_initModuleFacetConfigs___closed__4 = _init_l_Lake_initModuleFacetConfigs___closed__4();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__4);
l_Lake_initModuleFacetConfigs___closed__5 = _init_l_Lake_initModuleFacetConfigs___closed__5();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__5);
l_Lake_initModuleFacetConfigs___closed__6 = _init_l_Lake_initModuleFacetConfigs___closed__6();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__6);
l_Lake_initModuleFacetConfigs___closed__7 = _init_l_Lake_initModuleFacetConfigs___closed__7();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__7);
l_Lake_initModuleFacetConfigs___closed__8 = _init_l_Lake_initModuleFacetConfigs___closed__8();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__8);
l_Lake_initModuleFacetConfigs___closed__9 = _init_l_Lake_initModuleFacetConfigs___closed__9();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__9);
l_Lake_initModuleFacetConfigs___closed__10 = _init_l_Lake_initModuleFacetConfigs___closed__10();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__10);
l_Lake_initModuleFacetConfigs___closed__11 = _init_l_Lake_initModuleFacetConfigs___closed__11();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__11);
l_Lake_initModuleFacetConfigs___closed__12 = _init_l_Lake_initModuleFacetConfigs___closed__12();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__12);
l_Lake_initModuleFacetConfigs___closed__13 = _init_l_Lake_initModuleFacetConfigs___closed__13();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__13);
l_Lake_initModuleFacetConfigs___closed__14 = _init_l_Lake_initModuleFacetConfigs___closed__14();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__14);
l_Lake_initModuleFacetConfigs___closed__15 = _init_l_Lake_initModuleFacetConfigs___closed__15();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__15);
l_Lake_initModuleFacetConfigs___closed__16 = _init_l_Lake_initModuleFacetConfigs___closed__16();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__16);
l_Lake_initModuleFacetConfigs___closed__17 = _init_l_Lake_initModuleFacetConfigs___closed__17();
lean_mark_persistent(l_Lake_initModuleFacetConfigs___closed__17);
l_Lake_initModuleFacetConfigs = _init_l_Lake_initModuleFacetConfigs();
lean_mark_persistent(l_Lake_initModuleFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

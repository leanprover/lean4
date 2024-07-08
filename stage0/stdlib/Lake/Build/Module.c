// Lean compiler output
// Module: Lake.Build.Module
// Imports: Init Lake.Util.OrdHashSet Lake.Util.List Lean.Elab.ParseImportsFast Lake.Build.Common
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
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__1;
static lean_object* l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__1;
extern lean_object* l_Lake_MTime_instOrd;
static lean_object* l_Lake_Module_transImportsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_Module_recParseImports___spec__6(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Module_bcFile_x3f(lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__4;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__2;
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig;
LEAN_EXPORT uint8_t l_List_elem___at_Lake_Module_recParseImports___spec__4(lean_object*, lean_object*);
static lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__2;
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__2;
extern lean_object* l_Lake_instOrdBuildType;
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_nameToSharedLib(lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__13;
static lean_object* l_Lake_Module_recBuildLean___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lake_Module_recBuildDeps___spec__8(lean_object*, lean_object*);
static uint8_t l_Lake_Module_clearOutputHashes___closed__3;
lean_object* l_Lake_instBEqModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
static lean_object* l_Lake_Module_depsFacetConfig___closed__1;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__4;
lean_object* l_IO_FS_withIsolatedStreams___at_Lake_computeDynlibOfShared___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint64_t l_Lake_computeArrayHash___at_Lake_buildO___spec__1(lean_object*);
static lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_Module_recBuildDeps___spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_bcFacetConfig___closed__2;
static lean_object* l_Lake_Module_clearOutputHashes___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__5;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_Module_recBuildDeps___spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig;
static lean_object* l_Lake_Module_ileanFacetConfig___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_initModuleFacetConfigs___closed__10;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Module_recParseImports___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildUnlessUpToDate_x3f_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4(size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
static lean_object* l_Lake_Module_oExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__15(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___lambda__1___closed__1;
extern lean_object* l_Lake_instOrdJobAction;
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(size_t, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___closed__1;
uint8_t l_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__4;
static lean_object* l_Lake_Module_bcFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___closed__1;
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Module_recBuildDeps___spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Module_recBuildLean___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__5;
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_ileanFacetConfig___closed__1;
static lean_object* l_Lake_Module_coExportFacetConfig___closed__5;
static lean_object* l_Lake_initModuleFacetConfigs___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1;
lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_Module_recParseImports___spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_Module_recParseImports___spec__5(lean_object*, lean_object*);
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_clearOutputHashes(lean_object*, lean_object*);
extern uint64_t l_Lake_platformTrace;
size_t lean_usize_of_nat(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashableModule___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Module_recParseImports___spec__8___at_Lake_Module_recParseImports___spec__9(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lake_Module_getMTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_collectImportsAux___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___boxed(lean_object**);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1;
lean_object* l_Lake_Module_checkExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oleanFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_cacheOutputHashes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFacetConfig;
static lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__12;
lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lake_Module_recParseImports___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lake_Module_coExportFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig;
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_initModuleFacetConfigs;
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coExportFacetConfig___closed__2;
static lean_object* l_Lake_Module_bcoFacetConfig___closed__3;
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_Module_recParseImports___spec__3(lean_object*, lean_object*);
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildJob_collectArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_withRegisterJob___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__1;
static lean_object* l_Lake_Module_oExportFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig;
static lean_object* l_Lake_initModuleFacetConfigs___closed__16;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Module_ileanFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig;
static lean_object* l_Lake_Module_bcFacetConfig___closed__1;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_Workspace_leanPath(lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__2;
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig;
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___lambda__1___closed__3;
static lean_object* l_Lake_Module_recBuildLeanBcToO___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Module_recBuildDeps___spec__12___at_Lake_Module_recBuildDeps___spec__13(lean_object*, lean_object*);
lean_object* l_Lake_cacheFileHash(lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__1;
static lean_object* l_Lake_Module_oFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
extern lean_object* l_Task_Priority_default;
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_cFacetConfig___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__1;
static lean_object* l_Lake_Module_oleanFacetConfig___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFacetConfig;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_Module_recBuildDeps___spec__10(lean_object*, lean_object*);
static lean_object* l_Lake_Module_coExportFacetConfig___closed__4;
static lean_object* l_Lake_initModuleFacetConfigs___closed__17;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__5;
static lean_object* l_Lake_Module_cFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EResult_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__3;
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__2;
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oFacetConfig___closed__2;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_Module_recBuildDeps___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_bcoFacetConfig;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recComputeTransImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1___closed__3___boxed__const__1;
static lean_object* l_Lake_Module_coExportFacetConfig___closed__1;
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recParseImports___closed__1;
static lean_object* l_Lake_Module_depsFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_recBuildExternDynlibs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Module_recBuildDeps___spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recBuildExternDynlibs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__6;
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__11(lean_object*, lean_object*);
static lean_object* l_Lake_Module_cFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_leanArtsFacetConfig___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__4;
lean_object* l_Lake_EquipT_lift___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_clearOutputHashes___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2(lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__14;
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Module_recParseImports___spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Module_recBuildLean___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLean___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
static lean_object* l_Lake_Module_oleanFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToONoExport___closed__1;
uint8_t l_Lake_Backend_orPreferLeft(uint8_t, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_recBuildExternDynlibs___closed__1;
static lean_object* l_Lake_initModuleFacetConfigs___closed__11;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
static lean_object* l_Lake_Module_bcoFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildJob_mixArray___rarg(lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2;
static lean_object* l_Lake_Module_oleanFacetConfig___closed__4;
uint64_t l_Lean_Name_hash___override(lean_object*);
uint8_t l_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computePrecompileImportsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coFacetConfig___closed__2;
extern lean_object* l_Lake_Module_dynlibSuffix;
lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashablePackage___boxed(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Module_recBuildDynlib___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__1;
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_oleanFacetConfig___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_transImportsFacetConfig___closed__2;
static lean_object* l_Lake_Module_precompileImportsFacetConfig___closed__1;
static lean_object* l_Lake_Module_coFacetConfig___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_clearOutputHashes___closed__4;
static lean_object* l_Lake_initModuleFacetConfigs___closed__3;
static lean_object* l_Lake_Module_recBuildDeps___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__2;
uint8_t lean_internal_has_llvm_backend(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__3;
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instBEqPackage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_Module_recParseImports___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_precompileImportsFacetConfig___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_Module_recBuildDeps___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Module_recBuildLean___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oExportFacetConfig___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig;
static lean_object* l_Lake_Module_depsFacetConfig___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recComputePrecompileImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__1;
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__2;
static lean_object* l_Lake_initModuleFacetConfigs___closed__9;
lean_object* l_Lean_Name_toStringWithSep(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_dynlibFacetConfig___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__3(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Module_recParseImports___spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
lean_object* l_Lake_BuildType_leancArgs(uint8_t);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__6;
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__3;
static lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__2;
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__3;
lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(size_t, size_t, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___lambda__1(lean_object*);
lean_object* l_Lake_buildFileUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lake_Module_recBuildDeps___spec__8___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__15;
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__2;
lean_object* l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_clearFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectImportsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectImportsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Module_recBuildDeps___spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computePrecompileImportsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_17, 0, x_14);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_5);
x_18 = lean_apply_6(x_4, x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
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
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_27 = lean_array_uset(x_16, x_2, x_23);
x_2 = x_26;
x_3 = x_27;
x_7 = x_24;
x_8 = x_22;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
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
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_19, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_19, 0, x_36);
return x_18;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_dec(x_19);
x_38 = lean_ctor_get(x_20, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_40 = x_20;
} else {
 lean_dec_ref(x_20);
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
lean_ctor_set(x_18, 0, x_42);
return x_18;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_45 = x_19;
} else {
 lean_dec_ref(x_19);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_48 = x_20;
} else {
 lean_dec_ref(x_20);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
if (lean_is_scalar(x_45)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_45;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_18);
if (x_52 == 0)
{
return x_18;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_18, 0);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_18);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_54; 
x_54 = lean_usize_dec_lt(x_3, x_2);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_8);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_9);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_10);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; lean_object* x_74; 
x_58 = lean_array_uget(x_1, x_3);
x_59 = lean_ctor_get(x_4, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_dec(x_4);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 8);
lean_inc(x_63);
x_64 = l_System_FilePath_join(x_61, x_63);
x_65 = lean_ctor_get(x_62, 10);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_System_FilePath_join(x_64, x_65);
x_67 = lean_array_push(x_60, x_66);
x_68 = lean_ctor_get(x_58, 10);
lean_inc(x_68);
x_69 = 0;
x_70 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_71 = l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1(x_58, x_70, x_68);
lean_dec(x_68);
x_72 = lean_array_get_size(x_71);
x_73 = lean_usize_of_nat(x_72);
lean_dec(x_72);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_74 = l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2(x_73, x_69, x_71, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_75, 0);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_76);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 0);
x_82 = l_Array_append___rarg(x_59, x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_67);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_76, 0, x_84);
x_11 = x_75;
x_12 = x_77;
goto block_53;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_76, 0);
x_86 = lean_ctor_get(x_76, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_76);
x_87 = l_Array_append___rarg(x_59, x_85);
lean_dec(x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_67);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set(x_75, 0, x_90);
x_11 = x_75;
x_12 = x_77;
goto block_53;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_75, 1);
lean_inc(x_91);
lean_dec(x_75);
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
x_95 = l_Array_append___rarg(x_59, x_92);
lean_dec(x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_67);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
if (lean_is_scalar(x_94)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_94;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_91);
x_11 = x_99;
x_12 = x_77;
goto block_53;
}
}
else
{
lean_object* x_100; uint8_t x_101; 
lean_dec(x_67);
lean_dec(x_59);
x_100 = lean_ctor_get(x_74, 1);
lean_inc(x_100);
lean_dec(x_74);
x_101 = !lean_is_exclusive(x_75);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_75, 0);
lean_dec(x_102);
x_103 = !lean_is_exclusive(x_76);
if (x_103 == 0)
{
x_11 = x_75;
x_12 = x_100;
goto block_53;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_76, 0);
x_105 = lean_ctor_get(x_76, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_76);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_75, 0, x_106);
x_11 = x_75;
x_12 = x_100;
goto block_53;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_75, 1);
lean_inc(x_107);
lean_dec(x_75);
x_108 = lean_ctor_get(x_76, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_76, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_110 = x_76;
} else {
 lean_dec_ref(x_76);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
x_11 = x_112;
x_12 = x_100;
goto block_53;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_67);
lean_dec(x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_113 = !lean_is_exclusive(x_74);
if (x_113 == 0)
{
return x_74;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_74, 0);
x_115 = lean_ctor_get(x_74, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_74);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
block_53:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_11, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_27 = x_13;
} else {
 lean_dec_ref(x_13);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_12);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_dec(x_13);
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
lean_dec(x_14);
x_35 = 1;
x_36 = lean_usize_add(x_3, x_35);
x_3 = x_36;
x_4 = x_34;
x_8 = x_33;
x_9 = x_32;
x_10 = x_12;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_11, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_11);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_11, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_12);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_49 = x_13;
} else {
 lean_dec_ref(x_13);
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
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_12);
return x_52;
}
}
}
}
}
static lean_object* _init_l_Lake_recBuildExternDynlibs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
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
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Lake_recBuildExternDynlibs___closed__1;
x_12 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3(x_1, x_9, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_13, 1);
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set(x_13, 0, x_24);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_15, 1, x_19);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_13, 1, x_27);
lean_ctor_set(x_13, 0, x_26);
lean_ctor_set(x_14, 0, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_12, 0, x_28);
return x_12;
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
lean_ctor_set(x_13, 1, x_31);
lean_ctor_set(x_13, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_29);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_19);
lean_ctor_set(x_12, 0, x_34);
return x_12;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_37 = x_14;
} else {
 lean_dec_ref(x_14);
 x_37 = lean_box(0);
}
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
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
if (lean_is_scalar(x_37)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_37;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_12, 0, x_43);
return x_12;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_dec(x_12);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_46 = x_13;
} else {
 lean_dec_ref(x_13);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_48 = x_14;
} else {
 lean_dec_ref(x_14);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_51 = x_15;
} else {
 lean_dec_ref(x_15);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_45);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_44);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_12);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_12, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_13, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_14);
if (x_60 == 0)
{
return x_12;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_14, 0);
x_62 = lean_ctor_get(x_14, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_14);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_13, 0, x_63);
return x_12;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_dec(x_13);
x_65 = lean_ctor_get(x_14, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_14, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_67 = x_14;
} else {
 lean_dec_ref(x_14);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_12, 0, x_69);
return x_12;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_12, 1);
lean_inc(x_70);
lean_dec(x_12);
x_71 = lean_ctor_get(x_13, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_72 = x_13;
} else {
 lean_dec_ref(x_13);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_14, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_14, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_75 = x_14;
} else {
 lean_dec_ref(x_14);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_70);
return x_78;
}
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_12);
if (x_79 == 0)
{
return x_12;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_12, 0);
x_81 = lean_ctor_get(x_12, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_12);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
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
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_apply_1(x_1, x_17);
lean_ctor_set(x_11, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_apply_1(x_1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_10, 0, x_22);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_26 = x_11;
} else {
 lean_dec_ref(x_11);
 x_26 = lean_box(0);
}
x_27 = lean_apply_1(x_1, x_24);
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
lean_ctor_set(x_9, 0, x_29);
return x_9;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_32 = x_10;
} else {
 lean_dec_ref(x_10);
 x_32 = lean_box(0);
}
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
x_36 = lean_apply_1(x_1, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_30);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_9, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_10, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_10, 0, x_47);
return x_9;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_dec(x_10);
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_51 = x_11;
} else {
 lean_dec_ref(x_11);
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
lean_ctor_set(x_9, 0, x_53);
return x_9;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
lean_dec(x_9);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_56 = x_10;
} else {
 lean_dec_ref(x_10);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_11, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_59 = x_11;
} else {
 lean_dec_ref(x_11);
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
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_9);
if (x_63 == 0)
{
return x_9;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_9, 0);
x_65 = lean_ctor_get(x_9, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_9);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lake_Module_recParseImports___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_4, 2);
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
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_Module_recParseImports___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_Name_hash___override(x_5);
x_7 = lean_hashset_mk_idx(x_4, x_6);
x_8 = lean_array_uget(x_3, x_7);
x_9 = l_List_elem___at_Lake_Module_recParseImports___spec__4(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Module_recParseImports___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_17 = lean_apply_1(x_1, x_14);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_19 = lean_hashset_mk_idx(x_16, x_18);
x_20 = lean_array_uget(x_2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_uset(x_2, x_19, x_21);
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Module_recParseImports___spec__8___at_Lake_Module_recParseImports___spec__9(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_Name_hash___override(x_7);
lean_dec(x_7);
x_9 = lean_hashset_mk_idx(x_6, x_8);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 1, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
x_17 = l_Lean_Name_hash___override(x_16);
lean_dec(x_16);
x_18 = lean_hashset_mk_idx(x_15, x_17);
x_19 = lean_array_uget(x_1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_uset(x_1, x_18, x_20);
x_1 = x_21;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_Module_recParseImports___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lake_Module_recParseImports___spec__8___at_Lake_Module_recParseImports___spec__9(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_Module_recParseImports___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashSetImp_moveEntries___at_Lake_Module_recParseImports___spec__7(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Module_recParseImports___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_List_replace___at_Lake_Module_recParseImports___spec__10(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
x_16 = lean_name_eq(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_List_replace___at_Lake_Module_recParseImports___spec__10(x_13, x_2, x_3);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_Module_recParseImports___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = l_Lean_Name_hash___override(x_7);
lean_dec(x_7);
lean_inc(x_6);
x_9 = lean_hashset_mk_idx(x_6, x_8);
x_10 = lean_array_uget(x_5, x_9);
x_11 = l_List_elem___at_Lake_Module_recParseImports___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_array_uset(x_5, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_6);
lean_dec(x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Lean_HashSetImp_expand___at_Lake_Module_recParseImports___spec__6(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = lean_array_uset(x_5, x_9, x_18);
lean_inc(x_2);
x_20 = l_List_replace___at_Lake_Module_recParseImports___spec__10(x_10, x_2, x_2);
lean_dec(x_2);
x_21 = lean_array_uset(x_19, x_9, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
x_26 = l_Lean_Name_hash___override(x_25);
lean_dec(x_25);
lean_inc(x_24);
x_27 = lean_hashset_mk_idx(x_24, x_26);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_List_elem___at_Lake_Module_recParseImports___spec__4(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = lean_nat_dec_le(x_31, x_24);
lean_dec(x_24);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_HashSetImp_expand___at_Lake_Module_recParseImports___spec__6(x_31, x_33);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_24);
x_37 = lean_box(0);
x_38 = lean_array_uset(x_23, x_27, x_37);
lean_inc(x_2);
x_39 = l_List_replace___at_Lake_Module_recParseImports___spec__10(x_28, x_2, x_2);
lean_dec(x_2);
x_40 = lean_array_uset(x_38, x_27, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashableModule___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqModule___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_HashSetImp_contains___at_Lake_Module_recParseImports___spec__3(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = lean_array_push(x_5, x_2);
x_7 = l_Lean_HashSetImp_insert___at_Lake_Module_recParseImports___spec__5(x_3, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_apply_1(x_2, x_17);
lean_ctor_set(x_11, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_apply_1(x_2, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_10, 0, x_22);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_26 = x_11;
} else {
 lean_dec_ref(x_11);
 x_26 = lean_box(0);
}
x_27 = lean_apply_1(x_2, x_24);
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
lean_ctor_set(x_9, 0, x_29);
return x_9;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_32 = x_10;
} else {
 lean_dec_ref(x_10);
 x_32 = lean_box(0);
}
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
x_36 = lean_apply_1(x_2, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_30);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_9, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_10, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_10, 0, x_47);
return x_9;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_dec(x_10);
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_51 = x_11;
} else {
 lean_dec_ref(x_11);
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
lean_ctor_set(x_9, 0, x_53);
return x_9;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
lean_dec(x_9);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_56 = x_10;
} else {
 lean_dec_ref(x_10);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_11, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_59 = x_11;
} else {
 lean_dec_ref(x_11);
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
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_9);
if (x_63 == 0)
{
return x_9;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_9, 0);
x_65 = lean_ctor_get(x_9, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_9);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Functor_mapRev___at_Lake_Module_recParseImports___spec__11___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__3(lean_object* x_1, lean_object* x_2) {
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
x_4 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_1, x_3);
return x_4;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_Workspace_findModule_x3f___boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__3;
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__2;
x_17 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg), 8, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg), 8, 2);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__3), 2, 1);
lean_closure_set(x_19, 0, x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Functor_mapRev___at_Lake_Module_recParseImports___spec__11___rarg(x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_2 = x_28;
x_4 = x_25;
x_8 = x_26;
x_9 = x_24;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_20, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_21, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_21, 0, x_37);
return x_20;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_dec(x_21);
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_41 = x_22;
} else {
 lean_dec_ref(x_22);
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
lean_ctor_set(x_20, 0, x_43);
return x_20;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_dec(x_20);
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
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_49 = x_22;
} else {
 lean_dec_ref(x_22);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_46;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_20);
if (x_53 == 0)
{
return x_20;
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
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_9);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_10);
return x_59;
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
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_270; 
x_192 = lean_ctor_get(x_1, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 2);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_ctor_get(x_195, 7);
lean_inc(x_196);
lean_dec(x_195);
x_197 = l_System_FilePath_join(x_194, x_196);
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
lean_dec(x_192);
x_199 = lean_ctor_get(x_198, 2);
lean_inc(x_199);
lean_dec(x_198);
x_200 = l_System_FilePath_join(x_197, x_199);
x_201 = lean_ctor_get(x_1, 1);
lean_inc(x_201);
lean_dec(x_1);
x_202 = l_Lake_Module_recParseImports___closed__1;
x_203 = l_Lean_modToFilePath(x_200, x_201, x_202);
lean_dec(x_200);
x_270 = l_IO_FS_readFile(x_203, x_7);
if (lean_obj_tag(x_270) == 0)
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_270, 1);
lean_ctor_set(x_270, 1, x_5);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_6);
x_204 = x_273;
x_205 = x_272;
goto block_269;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = lean_ctor_get(x_270, 0);
x_275 = lean_ctor_get(x_270, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_270);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_5);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_6);
x_204 = x_277;
x_205 = x_275;
goto block_269;
}
}
else
{
uint8_t x_278; 
x_278 = !lean_is_exclusive(x_270);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_279 = lean_ctor_get(x_270, 0);
x_280 = lean_ctor_get(x_270, 1);
x_281 = lean_io_error_to_string(x_279);
x_282 = 3;
x_283 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set_uint8(x_283, sizeof(void*)*1, x_282);
x_284 = lean_array_get_size(x_5);
x_285 = lean_array_push(x_5, x_283);
lean_ctor_set(x_270, 1, x_285);
lean_ctor_set(x_270, 0, x_284);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_270);
lean_ctor_set(x_286, 1, x_6);
x_204 = x_286;
x_205 = x_280;
goto block_269;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_287 = lean_ctor_get(x_270, 0);
x_288 = lean_ctor_get(x_270, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_270);
x_289 = lean_io_error_to_string(x_287);
x_290 = 3;
x_291 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set_uint8(x_291, sizeof(void*)*1, x_290);
x_292 = lean_array_get_size(x_5);
x_293 = lean_array_push(x_5, x_291);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_6);
x_204 = x_295;
x_205 = x_288;
goto block_269;
}
}
block_191:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_array_get_size(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
lean_ctor_set(x_10, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_17, x_17);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
lean_ctor_set(x_10, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_10);
lean_free_object(x_8);
x_25 = 0;
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_28 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12(x_15, x_25, x_26, x_27, x_2, x_3, x_4, x_16, x_12, x_9);
lean_dec(x_15);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_29, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_ctor_set(x_30, 0, x_37);
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_29, 0, x_41);
return x_28;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_45 = x_30;
} else {
 lean_dec_ref(x_30);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_28, 0, x_48);
return x_28;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_dec(x_28);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_51 = x_29;
} else {
 lean_dec_ref(x_29);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_30, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_54 = x_30;
} else {
 lean_dec_ref(x_30);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
if (lean_is_scalar(x_51)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_51;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_28);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_28, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_29);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_29, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_30);
if (x_63 == 0)
{
return x_28;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_30, 0);
x_65 = lean_ctor_get(x_30, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_30);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_29, 0, x_66);
return x_28;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_29, 1);
lean_inc(x_67);
lean_dec(x_29);
x_68 = lean_ctor_get(x_30, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_70 = x_30;
} else {
 lean_dec_ref(x_30);
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
lean_ctor_set(x_28, 0, x_72);
return x_28;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_28, 1);
lean_inc(x_73);
lean_dec(x_28);
x_74 = lean_ctor_get(x_29, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_75 = x_29;
} else {
 lean_dec_ref(x_29);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_30, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_30, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_78 = x_30;
} else {
 lean_dec_ref(x_30);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
if (lean_is_scalar(x_75)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_75;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
return x_81;
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_28);
if (x_82 == 0)
{
return x_28;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_28, 0);
x_84 = lean_ctor_get(x_28, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_28);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_10, 0);
x_87 = lean_ctor_get(x_10, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_10);
x_88 = lean_array_get_size(x_86);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_nat_dec_lt(x_89, x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
lean_ctor_set(x_8, 0, x_92);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_8);
lean_ctor_set(x_93, 1, x_9);
return x_93;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_le(x_88, x_88);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_87);
lean_ctor_set(x_8, 0, x_96);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_8);
lean_ctor_set(x_97, 1, x_9);
return x_97;
}
else
{
size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; 
lean_free_object(x_8);
x_98 = 0;
x_99 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_100 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_101 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12(x_86, x_98, x_99, x_100, x_2, x_3, x_4, x_87, x_12, x_9);
lean_dec(x_86);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_105 = x_101;
} else {
 lean_dec_ref(x_101);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_107 = x_102;
} else {
 lean_dec_ref(x_102);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_103, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_110 = x_103;
} else {
 lean_dec_ref(x_103);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
if (lean_is_scalar(x_107)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_107;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_106);
if (lean_is_scalar(x_105)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_105;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_104);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_115 = lean_ctor_get(x_101, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_116 = x_101;
} else {
 lean_dec_ref(x_101);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_102, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_118 = x_102;
} else {
 lean_dec_ref(x_102);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_103, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_103, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_121 = x_103;
} else {
 lean_dec_ref(x_103);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_117);
if (lean_is_scalar(x_116)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_116;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_115);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_101, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_101, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_127 = x_101;
} else {
 lean_dec_ref(x_101);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_129 = lean_ctor_get(x_8, 1);
lean_inc(x_129);
lean_dec(x_8);
x_130 = lean_ctor_get(x_10, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_10, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_132 = x_10;
} else {
 lean_dec_ref(x_10);
 x_132 = lean_box(0);
}
x_133 = lean_array_get_size(x_130);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_nat_dec_lt(x_134, x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_132)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_132;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_131);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_129);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_9);
return x_139;
}
else
{
uint8_t x_140; 
x_140 = lean_nat_dec_le(x_133, x_133);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_132)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_132;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_131);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_129);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_9);
return x_144;
}
else
{
size_t x_145; size_t x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_132);
x_145 = 0;
x_146 = lean_usize_of_nat(x_133);
lean_dec(x_133);
x_147 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_148 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12(x_130, x_145, x_146, x_147, x_2, x_3, x_4, x_131, x_129, x_9);
lean_dec(x_130);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_152 = x_148;
} else {
 lean_dec_ref(x_148);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_154 = x_149;
} else {
 lean_dec_ref(x_149);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_150, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_150, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_157 = x_150;
} else {
 lean_dec_ref(x_150);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
if (lean_is_scalar(x_154)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_154;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_153);
if (lean_is_scalar(x_152)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_152;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_151);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_162 = lean_ctor_get(x_148, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_163 = x_148;
} else {
 lean_dec_ref(x_148);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_149, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_165 = x_149;
} else {
 lean_dec_ref(x_149);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_150, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_150, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_168 = x_150;
} else {
 lean_dec_ref(x_150);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
if (lean_is_scalar(x_165)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_165;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_164);
if (lean_is_scalar(x_163)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_163;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_162);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_148, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_148, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_174 = x_148;
} else {
 lean_dec_ref(x_148);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_176 = !lean_is_exclusive(x_8);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_ctor_get(x_8, 0);
lean_dec(x_177);
x_178 = !lean_is_exclusive(x_10);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_8);
lean_ctor_set(x_179, 1, x_9);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_10, 0);
x_181 = lean_ctor_get(x_10, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_10);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_8, 0, x_182);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_8);
lean_ctor_set(x_183, 1, x_9);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_8, 1);
lean_inc(x_184);
lean_dec(x_8);
x_185 = lean_ctor_get(x_10, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_10, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_187 = x_10;
} else {
 lean_dec_ref(x_10);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_184);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_9);
return x_190;
}
}
}
block_269:
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_204, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_206, 0);
x_211 = lean_ctor_get(x_206, 1);
x_212 = l_Lean_parseImports_x27(x_210, x_203, x_205);
lean_dec(x_203);
lean_dec(x_210);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
lean_ctor_set(x_206, 0, x_213);
x_8 = x_204;
x_9 = x_214;
goto block_191;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_dec(x_212);
x_217 = lean_io_error_to_string(x_215);
x_218 = 3;
x_219 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set_uint8(x_219, sizeof(void*)*1, x_218);
x_220 = lean_array_get_size(x_211);
x_221 = lean_array_push(x_211, x_219);
lean_ctor_set_tag(x_206, 1);
lean_ctor_set(x_206, 1, x_221);
lean_ctor_set(x_206, 0, x_220);
x_8 = x_204;
x_9 = x_216;
goto block_191;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_206, 0);
x_223 = lean_ctor_get(x_206, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_206);
x_224 = l_Lean_parseImports_x27(x_222, x_203, x_205);
lean_dec(x_203);
lean_dec(x_222);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_223);
lean_ctor_set(x_204, 0, x_227);
x_8 = x_204;
x_9 = x_226;
goto block_191;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_224, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 1);
lean_inc(x_229);
lean_dec(x_224);
x_230 = lean_io_error_to_string(x_228);
x_231 = 3;
x_232 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set_uint8(x_232, sizeof(void*)*1, x_231);
x_233 = lean_array_get_size(x_223);
x_234 = lean_array_push(x_223, x_232);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set(x_204, 0, x_235);
x_8 = x_204;
x_9 = x_229;
goto block_191;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_ctor_get(x_204, 1);
lean_inc(x_236);
lean_dec(x_204);
x_237 = lean_ctor_get(x_206, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_206, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_239 = x_206;
} else {
 lean_dec_ref(x_206);
 x_239 = lean_box(0);
}
x_240 = l_Lean_parseImports_x27(x_237, x_203, x_205);
lean_dec(x_203);
lean_dec(x_237);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
if (lean_is_scalar(x_239)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_239;
}
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_238);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_236);
x_8 = x_244;
x_9 = x_242;
goto block_191;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_245 = lean_ctor_get(x_240, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_240, 1);
lean_inc(x_246);
lean_dec(x_240);
x_247 = lean_io_error_to_string(x_245);
x_248 = 3;
x_249 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*1, x_248);
x_250 = lean_array_get_size(x_238);
x_251 = lean_array_push(x_238, x_249);
if (lean_is_scalar(x_239)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_239;
 lean_ctor_set_tag(x_252, 1);
}
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_236);
x_8 = x_253;
x_9 = x_246;
goto block_191;
}
}
}
else
{
uint8_t x_254; 
lean_dec(x_203);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_254 = !lean_is_exclusive(x_204);
if (x_254 == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_204, 0);
lean_dec(x_255);
x_256 = !lean_is_exclusive(x_206);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_204);
lean_ctor_set(x_257, 1, x_205);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_206, 0);
x_259 = lean_ctor_get(x_206, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_206);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
lean_ctor_set(x_204, 0, x_260);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_204);
lean_ctor_set(x_261, 1, x_205);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_262 = lean_ctor_get(x_204, 1);
lean_inc(x_262);
lean_dec(x_204);
x_263 = lean_ctor_get(x_206, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_206, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_265 = x_206;
} else {
 lean_dec_ref(x_206);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_262);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_205);
return x_268;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lake_Module_recParseImports___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lake_Module_recParseImports___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_Module_recParseImports___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lake_Module_recParseImports___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Module_recParseImports___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lake_Module_recParseImports___spec__10(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Module_recParseImports(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
x_1 = l_Lake_Module_recParseImports___closed__1;
x_2 = l_Lake_Module_importsFacetConfig___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_importsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_importsFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_importsFacetConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_importsFacetConfig___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_importsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_importsFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__2(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": bad import '", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_56; lean_object* x_57; uint8_t x_101; 
x_101 = lean_usize_dec_lt(x_5, x_4);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_6);
lean_ctor_set(x_102, 1, x_10);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_11);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_12);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_185; 
x_105 = lean_array_uget(x_3, x_5);
x_106 = lean_ctor_get(x_6, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_6, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_108 = x_6;
} else {
 lean_dec_ref(x_6);
 x_108 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_105);
x_185 = lean_apply_7(x_2, x_105, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_dec(x_185);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
lean_dec(x_186);
x_191 = !lean_is_exclusive(x_187);
if (x_191 == 0)
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_ctor_get(x_187, 0);
lean_dec(x_192);
x_193 = !lean_is_exclusive(x_188);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_194 = lean_ctor_get(x_188, 0);
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_107);
x_196 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_107, x_195);
lean_dec(x_195);
x_197 = lean_unbox(x_194);
lean_dec(x_194);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_106);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
lean_ctor_set(x_187, 0, x_200);
lean_ctor_set(x_188, 1, x_190);
lean_ctor_set(x_188, 0, x_187);
x_109 = x_188;
x_110 = x_189;
goto block_184;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_inc(x_105);
x_201 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_196, x_105);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_106);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_box(0);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
lean_ctor_set(x_187, 0, x_204);
lean_ctor_set(x_188, 1, x_190);
lean_ctor_set(x_188, 0, x_187);
x_109 = x_188;
x_110 = x_189;
goto block_184;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = lean_ctor_get(x_188, 0);
x_206 = lean_ctor_get(x_188, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_188);
lean_inc(x_107);
x_207 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_107, x_206);
lean_dec(x_206);
x_208 = lean_unbox(x_205);
lean_dec(x_205);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_106);
lean_ctor_set(x_209, 1, x_207);
x_210 = lean_box(0);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
lean_ctor_set(x_187, 0, x_211);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_187);
lean_ctor_set(x_212, 1, x_190);
x_109 = x_212;
x_110 = x_189;
goto block_184;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_inc(x_105);
x_213 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_207, x_105);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_106);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_box(0);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
lean_ctor_set(x_187, 0, x_216);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_187);
lean_ctor_set(x_217, 1, x_190);
x_109 = x_217;
x_110 = x_189;
goto block_184;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_218 = lean_ctor_get(x_187, 1);
lean_inc(x_218);
lean_dec(x_187);
x_219 = lean_ctor_get(x_188, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_188, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_221 = x_188;
} else {
 lean_dec_ref(x_188);
 x_221 = lean_box(0);
}
lean_inc(x_107);
x_222 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_107, x_220);
lean_dec(x_220);
x_223 = lean_unbox(x_219);
lean_dec(x_219);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_106);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_box(0);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_218);
if (lean_is_scalar(x_221)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_221;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_190);
x_109 = x_228;
x_110 = x_189;
goto block_184;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_inc(x_105);
x_229 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_222, x_105);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_106);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_box(0);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_218);
if (lean_is_scalar(x_221)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_221;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_190);
x_109 = x_234;
x_110 = x_189;
goto block_184;
}
}
}
else
{
lean_object* x_235; uint8_t x_236; 
lean_dec(x_106);
x_235 = lean_ctor_get(x_185, 1);
lean_inc(x_235);
lean_dec(x_185);
x_236 = !lean_is_exclusive(x_186);
if (x_236 == 0)
{
lean_object* x_237; uint8_t x_238; 
x_237 = lean_ctor_get(x_186, 0);
lean_dec(x_237);
x_238 = !lean_is_exclusive(x_187);
if (x_238 == 0)
{
x_109 = x_186;
x_110 = x_235;
goto block_184;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_187, 0);
x_240 = lean_ctor_get(x_187, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_187);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set(x_186, 0, x_241);
x_109 = x_186;
x_110 = x_235;
goto block_184;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_242 = lean_ctor_get(x_186, 1);
lean_inc(x_242);
lean_dec(x_186);
x_243 = lean_ctor_get(x_187, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_187, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_245 = x_187;
} else {
 lean_dec_ref(x_187);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_242);
x_109 = x_247;
x_110 = x_235;
goto block_184;
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_248 = !lean_is_exclusive(x_185);
if (x_248 == 0)
{
return x_185;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_185, 0);
x_250 = lean_ctor_get(x_185, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_185);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
block_184:
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_105);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_109, 0);
lean_dec(x_113);
x_56 = x_109;
x_57 = x_110;
goto block_100;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_111);
lean_ctor_set(x_115, 1, x_114);
x_56 = x_115;
x_57 = x_110;
goto block_100;
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_109);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_109, 0);
lean_dec(x_117);
x_118 = !lean_is_exclusive(x_111);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_119 = lean_ctor_get(x_111, 0);
x_120 = lean_ctor_get(x_111, 1);
x_121 = l_Array_shrink___rarg(x_120, x_119);
lean_dec(x_119);
x_122 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_123 = lean_string_append(x_122, x_1);
x_124 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_ctor_get(x_105, 1);
lean_inc(x_126);
lean_dec(x_105);
x_127 = 1;
x_128 = l_Lean_Name_toString(x_126, x_127);
x_129 = lean_string_append(x_125, x_128);
lean_dec(x_128);
x_130 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_131 = lean_string_append(x_129, x_130);
x_132 = 3;
x_133 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_132);
x_134 = lean_array_push(x_121, x_133);
x_135 = lean_box(x_127);
if (lean_is_scalar(x_108)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_108;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_107);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set_tag(x_111, 0);
lean_ctor_set(x_111, 1, x_134);
lean_ctor_set(x_111, 0, x_138);
x_56 = x_109;
x_57 = x_110;
goto block_100;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_139 = lean_ctor_get(x_111, 0);
x_140 = lean_ctor_get(x_111, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_111);
x_141 = l_Array_shrink___rarg(x_140, x_139);
lean_dec(x_139);
x_142 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_143 = lean_string_append(x_142, x_1);
x_144 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_ctor_get(x_105, 1);
lean_inc(x_146);
lean_dec(x_105);
x_147 = 1;
x_148 = l_Lean_Name_toString(x_146, x_147);
x_149 = lean_string_append(x_145, x_148);
lean_dec(x_148);
x_150 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_151 = lean_string_append(x_149, x_150);
x_152 = 3;
x_153 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_152);
x_154 = lean_array_push(x_141, x_153);
x_155 = lean_box(x_147);
if (lean_is_scalar(x_108)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_108;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_107);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_154);
lean_ctor_set(x_109, 0, x_159);
x_56 = x_109;
x_57 = x_110;
goto block_100;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_160 = lean_ctor_get(x_109, 1);
lean_inc(x_160);
lean_dec(x_109);
x_161 = lean_ctor_get(x_111, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_111, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_163 = x_111;
} else {
 lean_dec_ref(x_111);
 x_163 = lean_box(0);
}
x_164 = l_Array_shrink___rarg(x_162, x_161);
lean_dec(x_161);
x_165 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_166 = lean_string_append(x_165, x_1);
x_167 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_168 = lean_string_append(x_166, x_167);
x_169 = lean_ctor_get(x_105, 1);
lean_inc(x_169);
lean_dec(x_105);
x_170 = 1;
x_171 = l_Lean_Name_toString(x_169, x_170);
x_172 = lean_string_append(x_168, x_171);
lean_dec(x_171);
x_173 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_174 = lean_string_append(x_172, x_173);
x_175 = 3;
x_176 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_175);
x_177 = lean_array_push(x_164, x_176);
x_178 = lean_box(x_170);
if (lean_is_scalar(x_108)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_108;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_107);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
if (lean_is_scalar(x_163)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_163;
 lean_ctor_set_tag(x_182, 0);
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_177);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_160);
x_56 = x_183;
x_57 = x_110;
goto block_100;
}
}
}
}
block_55:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
lean_ctor_set(x_15, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_13, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_14);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
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
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
lean_dec(x_16);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_14);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_dec(x_15);
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
lean_dec(x_16);
x_37 = 1;
x_38 = lean_usize_add(x_5, x_37);
x_5 = x_38;
x_6 = x_36;
x_10 = x_35;
x_11 = x_34;
x_12 = x_14;
goto _start;
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_13, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_14);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_13, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_13);
lean_ctor_set(x_47, 1, x_14);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_dec(x_13);
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_51 = x_15;
} else {
 lean_dec_ref(x_15);
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
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_14);
return x_54;
}
}
}
block_100:
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_56, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_58, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_58, 0, x_66);
x_13 = x_56;
x_14 = x_57;
goto block_55;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_60);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_58, 0, x_70);
x_13 = x_56;
x_14 = x_57;
goto block_55;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_58, 1);
lean_inc(x_71);
lean_dec(x_58);
x_72 = lean_ctor_get(x_60, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_60, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_74 = x_60;
} else {
 lean_dec_ref(x_60);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
lean_ctor_set(x_56, 0, x_77);
x_13 = x_56;
x_14 = x_57;
goto block_55;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_56, 1);
lean_inc(x_78);
lean_dec(x_56);
x_79 = lean_ctor_get(x_58, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_80 = x_58;
} else {
 lean_dec_ref(x_58);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_60, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_60, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_83 = x_60;
} else {
 lean_dec_ref(x_60);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
if (lean_is_scalar(x_80)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_80;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_79);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_78);
x_13 = x_87;
x_14 = x_57;
goto block_55;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_56);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_56, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_58);
if (x_90 == 0)
{
x_13 = x_56;
x_14 = x_57;
goto block_55;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_58, 0);
x_92 = lean_ctor_get(x_58, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_58);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_56, 0, x_93);
x_13 = x_56;
x_14 = x_57;
goto block_55;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_56, 1);
lean_inc(x_94);
lean_dec(x_56);
x_95 = lean_ctor_get(x_58, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_58, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_97 = x_58;
} else {
 lean_dec_ref(x_58);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
x_13 = x_99;
x_14 = x_57;
goto block_55;
}
}
}
}
}
static lean_object* _init_l_Lake_collectImportsAux___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_collectImportsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_38; lean_object* x_39; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_array_get_size(x_7);
x_38 = l_Lake_collectImportsAux___closed__1;
x_39 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3(x_1, x_3, x_2, x_11, x_12, x_38, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_40, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_41, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
lean_ctor_set(x_41, 0, x_51);
x_14 = x_40;
x_15 = x_45;
goto block_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_dec(x_41);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_dec(x_42);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_40, 0, x_55);
x_14 = x_40;
x_15 = x_45;
goto block_37;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
lean_dec(x_40);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_58 = x_41;
} else {
 lean_dec_ref(x_41);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_dec(x_42);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
x_14 = x_62;
x_15 = x_45;
goto block_37;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_dec(x_42);
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_dec(x_39);
x_64 = !lean_is_exclusive(x_40);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_40, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_41);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_41, 1);
x_68 = lean_ctor_get(x_41, 0);
lean_dec(x_68);
x_69 = lean_array_get_size(x_67);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_69);
x_14 = x_40;
x_15 = x_63;
goto block_37;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_41, 1);
lean_inc(x_70);
lean_dec(x_41);
x_71 = lean_array_get_size(x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_40, 0, x_72);
x_14 = x_40;
x_15 = x_63;
goto block_37;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_40, 1);
lean_inc(x_73);
lean_dec(x_40);
x_74 = lean_ctor_get(x_41, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_75 = x_41;
} else {
 lean_dec_ref(x_41);
 x_75 = lean_box(0);
}
x_76 = lean_array_get_size(x_74);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_75;
 lean_ctor_set_tag(x_77, 1);
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
x_14 = x_78;
x_15 = x_63;
goto block_37;
}
}
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_39, 1);
lean_inc(x_79);
lean_dec(x_39);
x_80 = !lean_is_exclusive(x_40);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_40, 0);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_41);
if (x_82 == 0)
{
x_14 = x_40;
x_15 = x_79;
goto block_37;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_41, 0);
x_84 = lean_ctor_get(x_41, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_41);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_40, 0, x_85);
x_14 = x_40;
x_15 = x_79;
goto block_37;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_40, 1);
lean_inc(x_86);
lean_dec(x_40);
x_87 = lean_ctor_get(x_41, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_41, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_89 = x_41;
} else {
 lean_dec_ref(x_41);
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
x_14 = x_91;
x_15 = x_79;
goto block_37;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_13);
x_92 = !lean_is_exclusive(x_39);
if (x_92 == 0)
{
return x_39;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_39, 0);
x_94 = lean_ctor_get(x_39, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_39);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
block_37:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
lean_ctor_set(x_16, 0, x_13);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_14, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_15);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_33 = x_16;
} else {
 lean_dec_ref(x_16);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_15);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_collectImportsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_collectImportsAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("transImports", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_recParseImports___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_55; lean_object* x_56; uint8_t x_100; 
x_100 = lean_usize_dec_lt(x_4, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_5);
lean_ctor_set(x_101, 1, x_9);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_10);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_11);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_184; lean_object* x_185; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_104 = lean_array_uget(x_2, x_4);
x_105 = lean_ctor_get(x_5, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_5, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_107 = x_5;
} else {
 lean_dec_ref(x_5);
 x_107 = lean_box(0);
}
x_246 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_104);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_104);
lean_ctor_set(x_247, 1, x_246);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_7);
x_248 = lean_apply_6(x_6, x_247, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; uint8_t x_252; 
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
lean_dec(x_248);
x_252 = !lean_is_exclusive(x_249);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_253 = lean_ctor_get(x_249, 1);
x_254 = lean_ctor_get(x_249, 0);
lean_dec(x_254);
x_255 = !lean_is_exclusive(x_250);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_250, 0);
x_257 = 1;
x_258 = lean_box(x_257);
lean_ctor_set(x_249, 1, x_256);
lean_ctor_set(x_249, 0, x_258);
lean_ctor_set(x_250, 0, x_249);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_250);
lean_ctor_set(x_259, 1, x_253);
x_184 = x_259;
x_185 = x_251;
goto block_245;
}
else
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_260 = lean_ctor_get(x_250, 0);
x_261 = lean_ctor_get(x_250, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_250);
x_262 = 1;
x_263 = lean_box(x_262);
lean_ctor_set(x_249, 1, x_260);
lean_ctor_set(x_249, 0, x_263);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_249);
lean_ctor_set(x_264, 1, x_261);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_253);
x_184 = x_265;
x_185 = x_251;
goto block_245;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_266 = lean_ctor_get(x_249, 1);
lean_inc(x_266);
lean_dec(x_249);
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
x_270 = 1;
x_271 = lean_box(x_270);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_267);
if (lean_is_scalar(x_269)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_269;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_268);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_266);
x_184 = x_274;
x_185 = x_251;
goto block_245;
}
}
else
{
lean_object* x_275; uint8_t x_276; 
x_275 = lean_ctor_get(x_248, 1);
lean_inc(x_275);
lean_dec(x_248);
x_276 = !lean_is_exclusive(x_249);
if (x_276 == 0)
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_ctor_get(x_249, 0);
lean_dec(x_277);
x_278 = !lean_is_exclusive(x_250);
if (x_278 == 0)
{
x_184 = x_249;
x_185 = x_275;
goto block_245;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_250, 0);
x_280 = lean_ctor_get(x_250, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_250);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set(x_249, 0, x_281);
x_184 = x_249;
x_185 = x_275;
goto block_245;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_249, 1);
lean_inc(x_282);
lean_dec(x_249);
x_283 = lean_ctor_get(x_250, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_250, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_285 = x_250;
} else {
 lean_dec_ref(x_250);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_282);
x_184 = x_287;
x_185 = x_275;
goto block_245;
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_288 = !lean_is_exclusive(x_248);
if (x_288 == 0)
{
return x_248;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_248, 0);
x_290 = lean_ctor_get(x_248, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_248);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
block_183:
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_108, 0);
lean_dec(x_112);
x_55 = x_108;
x_56 = x_109;
goto block_99;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_55 = x_114;
x_56 = x_109;
goto block_99;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_108);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_108, 0);
lean_dec(x_116);
x_117 = !lean_is_exclusive(x_110);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_118 = lean_ctor_get(x_110, 0);
x_119 = lean_ctor_get(x_110, 1);
x_120 = l_Array_shrink___rarg(x_119, x_118);
lean_dec(x_118);
x_121 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_122 = lean_string_append(x_121, x_1);
x_123 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_ctor_get(x_104, 1);
lean_inc(x_125);
lean_dec(x_104);
x_126 = 1;
x_127 = l_Lean_Name_toString(x_125, x_126);
x_128 = lean_string_append(x_124, x_127);
lean_dec(x_127);
x_129 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_130 = lean_string_append(x_128, x_129);
x_131 = 3;
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_131);
x_133 = lean_array_push(x_120, x_132);
x_134 = lean_box(x_126);
if (lean_is_scalar(x_107)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_107;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_106);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set_tag(x_110, 0);
lean_ctor_set(x_110, 1, x_133);
lean_ctor_set(x_110, 0, x_137);
x_55 = x_108;
x_56 = x_109;
goto block_99;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_138 = lean_ctor_get(x_110, 0);
x_139 = lean_ctor_get(x_110, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_110);
x_140 = l_Array_shrink___rarg(x_139, x_138);
lean_dec(x_138);
x_141 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_142 = lean_string_append(x_141, x_1);
x_143 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_ctor_get(x_104, 1);
lean_inc(x_145);
lean_dec(x_104);
x_146 = 1;
x_147 = l_Lean_Name_toString(x_145, x_146);
x_148 = lean_string_append(x_144, x_147);
lean_dec(x_147);
x_149 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_150 = lean_string_append(x_148, x_149);
x_151 = 3;
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_151);
x_153 = lean_array_push(x_140, x_152);
x_154 = lean_box(x_146);
if (lean_is_scalar(x_107)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_107;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_106);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set(x_108, 0, x_158);
x_55 = x_108;
x_56 = x_109;
goto block_99;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_159 = lean_ctor_get(x_108, 1);
lean_inc(x_159);
lean_dec(x_108);
x_160 = lean_ctor_get(x_110, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_110, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_162 = x_110;
} else {
 lean_dec_ref(x_110);
 x_162 = lean_box(0);
}
x_163 = l_Array_shrink___rarg(x_161, x_160);
lean_dec(x_160);
x_164 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_165 = lean_string_append(x_164, x_1);
x_166 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_167 = lean_string_append(x_165, x_166);
x_168 = lean_ctor_get(x_104, 1);
lean_inc(x_168);
lean_dec(x_104);
x_169 = 1;
x_170 = l_Lean_Name_toString(x_168, x_169);
x_171 = lean_string_append(x_167, x_170);
lean_dec(x_170);
x_172 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_173 = lean_string_append(x_171, x_172);
x_174 = 3;
x_175 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_174);
x_176 = lean_array_push(x_163, x_175);
x_177 = lean_box(x_169);
if (lean_is_scalar(x_107)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_107;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_106);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
if (lean_is_scalar(x_162)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_162;
 lean_ctor_set_tag(x_181, 0);
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_176);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_159);
x_55 = x_182;
x_56 = x_109;
goto block_99;
}
}
}
block_245:
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
lean_dec(x_184);
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_186, 0);
lean_dec(x_190);
x_191 = !lean_is_exclusive(x_187);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_192 = lean_ctor_get(x_187, 0);
x_193 = lean_ctor_get(x_187, 1);
lean_inc(x_106);
x_194 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_106, x_193);
lean_dec(x_193);
x_195 = lean_unbox(x_192);
lean_dec(x_192);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_105);
lean_ctor_set(x_196, 1, x_194);
x_197 = lean_box(0);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
lean_ctor_set(x_186, 0, x_198);
lean_ctor_set(x_187, 1, x_188);
lean_ctor_set(x_187, 0, x_186);
x_108 = x_187;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_inc(x_104);
x_199 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_194, x_104);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_105);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_186, 0, x_202);
lean_ctor_set(x_187, 1, x_188);
lean_ctor_set(x_187, 0, x_186);
x_108 = x_187;
x_109 = x_185;
goto block_183;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_203 = lean_ctor_get(x_187, 0);
x_204 = lean_ctor_get(x_187, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_187);
lean_inc(x_106);
x_205 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_106, x_204);
lean_dec(x_204);
x_206 = lean_unbox(x_203);
lean_dec(x_203);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_105);
lean_ctor_set(x_207, 1, x_205);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
lean_ctor_set(x_186, 0, x_209);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_186);
lean_ctor_set(x_210, 1, x_188);
x_108 = x_210;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_inc(x_104);
x_211 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_205, x_104);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_105);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_box(0);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
lean_ctor_set(x_186, 0, x_214);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_186);
lean_ctor_set(x_215, 1, x_188);
x_108 = x_215;
x_109 = x_185;
goto block_183;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_216 = lean_ctor_get(x_186, 1);
lean_inc(x_216);
lean_dec(x_186);
x_217 = lean_ctor_get(x_187, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_187, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_219 = x_187;
} else {
 lean_dec_ref(x_187);
 x_219 = lean_box(0);
}
lean_inc(x_106);
x_220 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_106, x_218);
lean_dec(x_218);
x_221 = lean_unbox(x_217);
lean_dec(x_217);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_105);
lean_ctor_set(x_222, 1, x_220);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_216);
if (lean_is_scalar(x_219)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_219;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_188);
x_108 = x_226;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_inc(x_104);
x_227 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_220, x_104);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_105);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_216);
if (lean_is_scalar(x_219)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_219;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_188);
x_108 = x_232;
x_109 = x_185;
goto block_183;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_105);
x_233 = !lean_is_exclusive(x_184);
if (x_233 == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_184, 0);
lean_dec(x_234);
x_235 = !lean_is_exclusive(x_186);
if (x_235 == 0)
{
x_108 = x_184;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_186, 0);
x_237 = lean_ctor_get(x_186, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_186);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_184, 0, x_238);
x_108 = x_184;
x_109 = x_185;
goto block_183;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_184, 1);
lean_inc(x_239);
lean_dec(x_184);
x_240 = lean_ctor_get(x_186, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_186, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_242 = x_186;
} else {
 lean_dec_ref(x_186);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_239);
x_108 = x_244;
x_109 = x_185;
goto block_183;
}
}
}
}
block_54:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_28 = x_14;
} else {
 lean_dec_ref(x_14);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
x_4 = x_37;
x_5 = x_35;
x_9 = x_34;
x_10 = x_33;
x_11 = x_13;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_12, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_13);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_12, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_13);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_ctor_get(x_14, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_50 = x_14;
} else {
 lean_dec_ref(x_14);
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
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_13);
return x_53;
}
}
}
block_99:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_57, 0, x_65);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_59, 0);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_59);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_57, 0, x_69);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_dec(x_57);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_73 = x_59;
} else {
 lean_dec_ref(x_59);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_55, 0, x_76);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
lean_dec(x_55);
x_78 = lean_ctor_get(x_57, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_79 = x_57;
} else {
 lean_dec_ref(x_57);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_59, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_59, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_82 = x_59;
} else {
 lean_dec_ref(x_59);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_79)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_79;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
x_12 = x_86;
x_13 = x_56;
goto block_54;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_55);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_55, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_57);
if (x_89 == 0)
{
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_57, 0);
x_91 = lean_ctor_get(x_57, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_57);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_55, 0, x_92);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_55, 1);
lean_inc(x_93);
lean_dec(x_55);
x_94 = lean_ctor_get(x_57, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_57, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_96 = x_57;
} else {
 lean_dec_ref(x_57);
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
x_12 = x_98;
x_13 = x_56;
goto block_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recComputeTransImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_importsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_58; lean_object* x_59; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_21, 7);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_System_FilePath_join(x_20, x_22);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_System_FilePath_join(x_23, x_25);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_Module_recParseImports___closed__1;
x_29 = l_Lean_modToFilePath(x_26, x_27, x_28);
lean_dec(x_26);
x_30 = lean_array_get_size(x_16);
x_31 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_32 = 0;
x_33 = lean_array_get_size(x_17);
x_58 = l_Lake_collectImportsAux___closed__1;
x_59 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1(x_29, x_16, x_31, x_32, x_58, x_2, x_3, x_4, x_17, x_15, x_13);
lean_dec(x_16);
lean_dec(x_29);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_60, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_61);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_61, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_ctor_set(x_61, 0, x_71);
x_34 = x_60;
x_35 = x_65;
goto block_57;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
lean_dec(x_61);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
lean_dec(x_62);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
lean_ctor_set(x_60, 0, x_75);
x_34 = x_60;
x_35 = x_65;
goto block_57;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_dec(x_60);
x_77 = lean_ctor_get(x_61, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_78 = x_61;
} else {
 lean_dec_ref(x_61);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_62, 1);
lean_inc(x_79);
lean_dec(x_62);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
x_34 = x_82;
x_35 = x_65;
goto block_57;
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_62);
x_83 = lean_ctor_get(x_59, 1);
lean_inc(x_83);
lean_dec(x_59);
x_84 = !lean_is_exclusive(x_60);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_60, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_61);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_61, 1);
x_88 = lean_ctor_get(x_61, 0);
lean_dec(x_88);
x_89 = lean_array_get_size(x_87);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_89);
x_34 = x_60;
x_35 = x_83;
goto block_57;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_61, 1);
lean_inc(x_90);
lean_dec(x_61);
x_91 = lean_array_get_size(x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_60, 0, x_92);
x_34 = x_60;
x_35 = x_83;
goto block_57;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_60, 1);
lean_inc(x_93);
lean_dec(x_60);
x_94 = lean_ctor_get(x_61, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_95 = x_61;
} else {
 lean_dec_ref(x_61);
 x_95 = lean_box(0);
}
x_96 = lean_array_get_size(x_94);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_95;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
x_34 = x_98;
x_35 = x_83;
goto block_57;
}
}
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_59, 1);
lean_inc(x_99);
lean_dec(x_59);
x_100 = !lean_is_exclusive(x_60);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_60, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_61);
if (x_102 == 0)
{
x_34 = x_60;
x_35 = x_99;
goto block_57;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_61, 0);
x_104 = lean_ctor_get(x_61, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_61);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_60, 0, x_105);
x_34 = x_60;
x_35 = x_99;
goto block_57;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_60, 1);
lean_inc(x_106);
lean_dec(x_60);
x_107 = lean_ctor_get(x_61, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_61, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_109 = x_61;
} else {
 lean_dec_ref(x_61);
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
x_34 = x_111;
x_35 = x_99;
goto block_57;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_33);
lean_dec(x_14);
x_112 = !lean_is_exclusive(x_59);
if (x_112 == 0)
{
return x_59;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_59, 0);
x_114 = lean_ctor_get(x_59, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_59);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
block_57:
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
if (lean_is_scalar(x_14)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_14;
}
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
if (lean_is_scalar(x_14)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_14;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_34, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_36, 0);
lean_dec(x_46);
lean_ctor_set(x_36, 0, x_33);
if (lean_is_scalar(x_14)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_14;
}
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_35);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_dec(x_36);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_34, 0, x_49);
if (lean_is_scalar(x_14)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_14;
}
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_35);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_dec(x_34);
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_53 = x_36;
} else {
 lean_dec_ref(x_36);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_33);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
if (lean_is_scalar(x_14)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_14;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_35);
return x_56;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_10);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_10, 0);
lean_dec(x_117);
x_118 = !lean_is_exclusive(x_11);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_11, 0);
lean_dec(x_119);
x_120 = !lean_is_exclusive(x_12);
if (x_120 == 0)
{
return x_10;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_12, 0);
x_122 = lean_ctor_get(x_12, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_12);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_11, 0, x_123);
return x_10;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_11, 1);
lean_inc(x_124);
lean_dec(x_11);
x_125 = lean_ctor_get(x_12, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_12, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_127 = x_12;
} else {
 lean_dec_ref(x_12);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
lean_ctor_set(x_10, 0, x_129);
return x_10;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_130 = lean_ctor_get(x_10, 1);
lean_inc(x_130);
lean_dec(x_10);
x_131 = lean_ctor_get(x_11, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_132 = x_11;
} else {
 lean_dec_ref(x_11);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_12, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_12, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_135 = x_12;
} else {
 lean_dec_ref(x_12);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
if (lean_is_scalar(x_132)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_132;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_131);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_130);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_10);
if (x_139 == 0)
{
return x_10;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_10, 0);
x_141 = lean_ctor_get(x_10, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_10);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Module_recComputeTransImports(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_Module_transImportsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_transImportsFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_transImportsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_transImportsFacetConfig___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_transImportsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_transImportsFacetConfig___closed__2;
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precompileImports", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_recParseImports___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_55; lean_object* x_56; uint8_t x_100; 
x_100 = lean_usize_dec_lt(x_4, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_5);
lean_ctor_set(x_101, 1, x_9);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_10);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_11);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_184; lean_object* x_185; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_104 = lean_array_uget(x_2, x_4);
x_105 = lean_ctor_get(x_5, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_5, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_107 = x_5;
} else {
 lean_dec_ref(x_5);
 x_107 = lean_box(0);
}
x_246 = lean_ctor_get(x_104, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_247, 2);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_ctor_get_uint8(x_248, sizeof(void*)*21);
lean_dec(x_248);
if (x_249 == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_dec(x_246);
x_251 = lean_ctor_get_uint8(x_250, sizeof(void*)*9);
lean_dec(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
lean_inc(x_104);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_104);
lean_ctor_set(x_253, 1, x_252);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_7);
x_254 = lean_apply_6(x_6, x_253, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
x_258 = !lean_is_exclusive(x_255);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = lean_ctor_get(x_255, 1);
x_260 = lean_ctor_get(x_255, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_256);
if (x_261 == 0)
{
lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_256, 0);
x_263 = 0;
x_264 = lean_box(x_263);
lean_ctor_set(x_255, 1, x_262);
lean_ctor_set(x_255, 0, x_264);
lean_ctor_set(x_256, 0, x_255);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_256);
lean_ctor_set(x_265, 1, x_259);
x_184 = x_265;
x_185 = x_257;
goto block_245;
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_256, 0);
x_267 = lean_ctor_get(x_256, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_256);
x_268 = 0;
x_269 = lean_box(x_268);
lean_ctor_set(x_255, 1, x_266);
lean_ctor_set(x_255, 0, x_269);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_255);
lean_ctor_set(x_270, 1, x_267);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_259);
x_184 = x_271;
x_185 = x_257;
goto block_245;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_272 = lean_ctor_get(x_255, 1);
lean_inc(x_272);
lean_dec(x_255);
x_273 = lean_ctor_get(x_256, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_256, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_275 = x_256;
} else {
 lean_dec_ref(x_256);
 x_275 = lean_box(0);
}
x_276 = 0;
x_277 = lean_box(x_276);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_273);
if (lean_is_scalar(x_275)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_275;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_274);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_272);
x_184 = x_280;
x_185 = x_257;
goto block_245;
}
}
else
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_254, 1);
lean_inc(x_281);
lean_dec(x_254);
x_282 = !lean_is_exclusive(x_255);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_255, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_256);
if (x_284 == 0)
{
x_184 = x_255;
x_185 = x_281;
goto block_245;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_256, 0);
x_286 = lean_ctor_get(x_256, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_256);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
lean_ctor_set(x_255, 0, x_287);
x_184 = x_255;
x_185 = x_281;
goto block_245;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_288 = lean_ctor_get(x_255, 1);
lean_inc(x_288);
lean_dec(x_255);
x_289 = lean_ctor_get(x_256, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_256, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_291 = x_256;
} else {
 lean_dec_ref(x_256);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_288);
x_184 = x_293;
x_185 = x_281;
goto block_245;
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_294 = !lean_is_exclusive(x_254);
if (x_294 == 0)
{
return x_254;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_254, 0);
x_296 = lean_ctor_get(x_254, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_254);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_104);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_104);
lean_ctor_set(x_299, 1, x_298);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_7);
x_300 = lean_apply_6(x_6, x_299, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; uint8_t x_304; 
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_304 = !lean_is_exclusive(x_301);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_305 = lean_ctor_get(x_301, 1);
x_306 = lean_ctor_get(x_301, 0);
lean_dec(x_306);
x_307 = !lean_is_exclusive(x_302);
if (x_307 == 0)
{
lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_302, 0);
x_309 = 1;
x_310 = lean_box(x_309);
lean_ctor_set(x_301, 1, x_308);
lean_ctor_set(x_301, 0, x_310);
lean_ctor_set(x_302, 0, x_301);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_302);
lean_ctor_set(x_311, 1, x_305);
x_184 = x_311;
x_185 = x_303;
goto block_245;
}
else
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_312 = lean_ctor_get(x_302, 0);
x_313 = lean_ctor_get(x_302, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_302);
x_314 = 1;
x_315 = lean_box(x_314);
lean_ctor_set(x_301, 1, x_312);
lean_ctor_set(x_301, 0, x_315);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_301);
lean_ctor_set(x_316, 1, x_313);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_305);
x_184 = x_317;
x_185 = x_303;
goto block_245;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_318 = lean_ctor_get(x_301, 1);
lean_inc(x_318);
lean_dec(x_301);
x_319 = lean_ctor_get(x_302, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_302, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_321 = x_302;
} else {
 lean_dec_ref(x_302);
 x_321 = lean_box(0);
}
x_322 = 1;
x_323 = lean_box(x_322);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_319);
if (lean_is_scalar(x_321)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_321;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_320);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_318);
x_184 = x_326;
x_185 = x_303;
goto block_245;
}
}
else
{
lean_object* x_327; uint8_t x_328; 
x_327 = lean_ctor_get(x_300, 1);
lean_inc(x_327);
lean_dec(x_300);
x_328 = !lean_is_exclusive(x_301);
if (x_328 == 0)
{
lean_object* x_329; uint8_t x_330; 
x_329 = lean_ctor_get(x_301, 0);
lean_dec(x_329);
x_330 = !lean_is_exclusive(x_302);
if (x_330 == 0)
{
x_184 = x_301;
x_185 = x_327;
goto block_245;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_302, 0);
x_332 = lean_ctor_get(x_302, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_302);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
lean_ctor_set(x_301, 0, x_333);
x_184 = x_301;
x_185 = x_327;
goto block_245;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_334 = lean_ctor_get(x_301, 1);
lean_inc(x_334);
lean_dec(x_301);
x_335 = lean_ctor_get(x_302, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_302, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_337 = x_302;
} else {
 lean_dec_ref(x_302);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_334);
x_184 = x_339;
x_185 = x_327;
goto block_245;
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_340 = !lean_is_exclusive(x_300);
if (x_340 == 0)
{
return x_300;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_300, 0);
x_342 = lean_ctor_get(x_300, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_300);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_246);
x_344 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_104);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_104);
lean_ctor_set(x_345, 1, x_344);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_7);
x_346 = lean_apply_6(x_6, x_345, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; uint8_t x_350; 
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
lean_dec(x_346);
x_350 = !lean_is_exclusive(x_347);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_351 = lean_ctor_get(x_347, 1);
x_352 = lean_ctor_get(x_347, 0);
lean_dec(x_352);
x_353 = !lean_is_exclusive(x_348);
if (x_353 == 0)
{
lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; 
x_354 = lean_ctor_get(x_348, 0);
x_355 = 1;
x_356 = lean_box(x_355);
lean_ctor_set(x_347, 1, x_354);
lean_ctor_set(x_347, 0, x_356);
lean_ctor_set(x_348, 0, x_347);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_348);
lean_ctor_set(x_357, 1, x_351);
x_184 = x_357;
x_185 = x_349;
goto block_245;
}
else
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_358 = lean_ctor_get(x_348, 0);
x_359 = lean_ctor_get(x_348, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_348);
x_360 = 1;
x_361 = lean_box(x_360);
lean_ctor_set(x_347, 1, x_358);
lean_ctor_set(x_347, 0, x_361);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_347);
lean_ctor_set(x_362, 1, x_359);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_351);
x_184 = x_363;
x_185 = x_349;
goto block_245;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_364 = lean_ctor_get(x_347, 1);
lean_inc(x_364);
lean_dec(x_347);
x_365 = lean_ctor_get(x_348, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_348, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_367 = x_348;
} else {
 lean_dec_ref(x_348);
 x_367 = lean_box(0);
}
x_368 = 1;
x_369 = lean_box(x_368);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_365);
if (lean_is_scalar(x_367)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_367;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_366);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_364);
x_184 = x_372;
x_185 = x_349;
goto block_245;
}
}
else
{
lean_object* x_373; uint8_t x_374; 
x_373 = lean_ctor_get(x_346, 1);
lean_inc(x_373);
lean_dec(x_346);
x_374 = !lean_is_exclusive(x_347);
if (x_374 == 0)
{
lean_object* x_375; uint8_t x_376; 
x_375 = lean_ctor_get(x_347, 0);
lean_dec(x_375);
x_376 = !lean_is_exclusive(x_348);
if (x_376 == 0)
{
x_184 = x_347;
x_185 = x_373;
goto block_245;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_348, 0);
x_378 = lean_ctor_get(x_348, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_348);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
lean_ctor_set(x_347, 0, x_379);
x_184 = x_347;
x_185 = x_373;
goto block_245;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_380 = lean_ctor_get(x_347, 1);
lean_inc(x_380);
lean_dec(x_347);
x_381 = lean_ctor_get(x_348, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_348, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_383 = x_348;
} else {
 lean_dec_ref(x_348);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_380);
x_184 = x_385;
x_185 = x_373;
goto block_245;
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_386 = !lean_is_exclusive(x_346);
if (x_386 == 0)
{
return x_346;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_346, 0);
x_388 = lean_ctor_get(x_346, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_346);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
block_183:
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_108, 0);
lean_dec(x_112);
x_55 = x_108;
x_56 = x_109;
goto block_99;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_55 = x_114;
x_56 = x_109;
goto block_99;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_108);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_108, 0);
lean_dec(x_116);
x_117 = !lean_is_exclusive(x_110);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_118 = lean_ctor_get(x_110, 0);
x_119 = lean_ctor_get(x_110, 1);
x_120 = l_Array_shrink___rarg(x_119, x_118);
lean_dec(x_118);
x_121 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_122 = lean_string_append(x_121, x_1);
x_123 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_ctor_get(x_104, 1);
lean_inc(x_125);
lean_dec(x_104);
x_126 = 1;
x_127 = l_Lean_Name_toString(x_125, x_126);
x_128 = lean_string_append(x_124, x_127);
lean_dec(x_127);
x_129 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_130 = lean_string_append(x_128, x_129);
x_131 = 3;
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_131);
x_133 = lean_array_push(x_120, x_132);
x_134 = lean_box(x_126);
if (lean_is_scalar(x_107)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_107;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_106);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set_tag(x_110, 0);
lean_ctor_set(x_110, 1, x_133);
lean_ctor_set(x_110, 0, x_137);
x_55 = x_108;
x_56 = x_109;
goto block_99;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_138 = lean_ctor_get(x_110, 0);
x_139 = lean_ctor_get(x_110, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_110);
x_140 = l_Array_shrink___rarg(x_139, x_138);
lean_dec(x_138);
x_141 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_142 = lean_string_append(x_141, x_1);
x_143 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_ctor_get(x_104, 1);
lean_inc(x_145);
lean_dec(x_104);
x_146 = 1;
x_147 = l_Lean_Name_toString(x_145, x_146);
x_148 = lean_string_append(x_144, x_147);
lean_dec(x_147);
x_149 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_150 = lean_string_append(x_148, x_149);
x_151 = 3;
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_151);
x_153 = lean_array_push(x_140, x_152);
x_154 = lean_box(x_146);
if (lean_is_scalar(x_107)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_107;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_106);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set(x_108, 0, x_158);
x_55 = x_108;
x_56 = x_109;
goto block_99;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_159 = lean_ctor_get(x_108, 1);
lean_inc(x_159);
lean_dec(x_108);
x_160 = lean_ctor_get(x_110, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_110, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_162 = x_110;
} else {
 lean_dec_ref(x_110);
 x_162 = lean_box(0);
}
x_163 = l_Array_shrink___rarg(x_161, x_160);
lean_dec(x_160);
x_164 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_165 = lean_string_append(x_164, x_1);
x_166 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_167 = lean_string_append(x_165, x_166);
x_168 = lean_ctor_get(x_104, 1);
lean_inc(x_168);
lean_dec(x_104);
x_169 = 1;
x_170 = l_Lean_Name_toString(x_168, x_169);
x_171 = lean_string_append(x_167, x_170);
lean_dec(x_170);
x_172 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_173 = lean_string_append(x_171, x_172);
x_174 = 3;
x_175 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_174);
x_176 = lean_array_push(x_163, x_175);
x_177 = lean_box(x_169);
if (lean_is_scalar(x_107)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_107;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_106);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
if (lean_is_scalar(x_162)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_162;
 lean_ctor_set_tag(x_181, 0);
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_176);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_159);
x_55 = x_182;
x_56 = x_109;
goto block_99;
}
}
}
block_245:
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
lean_dec(x_184);
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_186, 0);
lean_dec(x_190);
x_191 = !lean_is_exclusive(x_187);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_192 = lean_ctor_get(x_187, 0);
x_193 = lean_ctor_get(x_187, 1);
lean_inc(x_106);
x_194 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_106, x_193);
lean_dec(x_193);
x_195 = lean_unbox(x_192);
lean_dec(x_192);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_105);
lean_ctor_set(x_196, 1, x_194);
x_197 = lean_box(0);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
lean_ctor_set(x_186, 0, x_198);
lean_ctor_set(x_187, 1, x_188);
lean_ctor_set(x_187, 0, x_186);
x_108 = x_187;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_inc(x_104);
x_199 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_194, x_104);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_105);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_186, 0, x_202);
lean_ctor_set(x_187, 1, x_188);
lean_ctor_set(x_187, 0, x_186);
x_108 = x_187;
x_109 = x_185;
goto block_183;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_203 = lean_ctor_get(x_187, 0);
x_204 = lean_ctor_get(x_187, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_187);
lean_inc(x_106);
x_205 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_106, x_204);
lean_dec(x_204);
x_206 = lean_unbox(x_203);
lean_dec(x_203);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_105);
lean_ctor_set(x_207, 1, x_205);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
lean_ctor_set(x_186, 0, x_209);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_186);
lean_ctor_set(x_210, 1, x_188);
x_108 = x_210;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_inc(x_104);
x_211 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_205, x_104);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_105);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_box(0);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
lean_ctor_set(x_186, 0, x_214);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_186);
lean_ctor_set(x_215, 1, x_188);
x_108 = x_215;
x_109 = x_185;
goto block_183;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_216 = lean_ctor_get(x_186, 1);
lean_inc(x_216);
lean_dec(x_186);
x_217 = lean_ctor_get(x_187, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_187, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_219 = x_187;
} else {
 lean_dec_ref(x_187);
 x_219 = lean_box(0);
}
lean_inc(x_106);
x_220 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_106, x_218);
lean_dec(x_218);
x_221 = lean_unbox(x_217);
lean_dec(x_217);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_105);
lean_ctor_set(x_222, 1, x_220);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_216);
if (lean_is_scalar(x_219)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_219;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_188);
x_108 = x_226;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_inc(x_104);
x_227 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_220, x_104);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_105);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_216);
if (lean_is_scalar(x_219)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_219;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_188);
x_108 = x_232;
x_109 = x_185;
goto block_183;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_105);
x_233 = !lean_is_exclusive(x_184);
if (x_233 == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_184, 0);
lean_dec(x_234);
x_235 = !lean_is_exclusive(x_186);
if (x_235 == 0)
{
x_108 = x_184;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_186, 0);
x_237 = lean_ctor_get(x_186, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_186);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_184, 0, x_238);
x_108 = x_184;
x_109 = x_185;
goto block_183;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_184, 1);
lean_inc(x_239);
lean_dec(x_184);
x_240 = lean_ctor_get(x_186, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_186, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_242 = x_186;
} else {
 lean_dec_ref(x_186);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_239);
x_108 = x_244;
x_109 = x_185;
goto block_183;
}
}
}
}
block_54:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_28 = x_14;
} else {
 lean_dec_ref(x_14);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
x_4 = x_37;
x_5 = x_35;
x_9 = x_34;
x_10 = x_33;
x_11 = x_13;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_12, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_13);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_12, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_13);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_ctor_get(x_14, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_50 = x_14;
} else {
 lean_dec_ref(x_14);
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
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_13);
return x_53;
}
}
}
block_99:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_57, 0, x_65);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_59, 0);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_59);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_57, 0, x_69);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_dec(x_57);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_73 = x_59;
} else {
 lean_dec_ref(x_59);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_55, 0, x_76);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
lean_dec(x_55);
x_78 = lean_ctor_get(x_57, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_79 = x_57;
} else {
 lean_dec_ref(x_57);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_59, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_59, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_82 = x_59;
} else {
 lean_dec_ref(x_59);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_79)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_79;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
x_12 = x_86;
x_13 = x_56;
goto block_54;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_55);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_55, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_57);
if (x_89 == 0)
{
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_57, 0);
x_91 = lean_ctor_get(x_57, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_57);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_55, 0, x_92);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_55, 1);
lean_inc(x_93);
lean_dec(x_55);
x_94 = lean_ctor_get(x_57, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_57, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_96 = x_57;
} else {
 lean_dec_ref(x_57);
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
x_12 = x_98;
x_13 = x_56;
goto block_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computePrecompileImportsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_37; lean_object* x_38; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_array_get_size(x_6);
x_37 = l_Lake_collectImportsAux___closed__1;
x_38 = l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1(x_1, x_2, x_10, x_11, x_37, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_39, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_ctor_set(x_40, 0, x_50);
x_13 = x_39;
x_14 = x_44;
goto block_36;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
lean_dec(x_40);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_dec(x_41);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_39, 0, x_54);
x_13 = x_39;
x_14 = x_44;
goto block_36;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
lean_dec(x_39);
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_57 = x_40;
} else {
 lean_dec_ref(x_40);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_dec(x_41);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
x_13 = x_61;
x_14 = x_44;
goto block_36;
}
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_41);
x_62 = lean_ctor_get(x_38, 1);
lean_inc(x_62);
lean_dec(x_38);
x_63 = !lean_is_exclusive(x_39);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_39, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_40);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_40, 1);
x_67 = lean_ctor_get(x_40, 0);
lean_dec(x_67);
x_68 = lean_array_get_size(x_66);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_68);
x_13 = x_39;
x_14 = x_62;
goto block_36;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_40, 1);
lean_inc(x_69);
lean_dec(x_40);
x_70 = lean_array_get_size(x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_39, 0, x_71);
x_13 = x_39;
x_14 = x_62;
goto block_36;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_39, 1);
lean_inc(x_72);
lean_dec(x_39);
x_73 = lean_ctor_get(x_40, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_74 = x_40;
} else {
 lean_dec_ref(x_40);
 x_74 = lean_box(0);
}
x_75 = lean_array_get_size(x_73);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_74;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_72);
x_13 = x_77;
x_14 = x_62;
goto block_36;
}
}
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_38, 1);
lean_inc(x_78);
lean_dec(x_38);
x_79 = !lean_is_exclusive(x_39);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_39, 0);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_40);
if (x_81 == 0)
{
x_13 = x_39;
x_14 = x_78;
goto block_36;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_40, 0);
x_83 = lean_ctor_get(x_40, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_40);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_39, 0, x_84);
x_13 = x_39;
x_14 = x_78;
goto block_36;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_39, 1);
lean_inc(x_85);
lean_dec(x_39);
x_86 = lean_ctor_get(x_40, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_40, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_88 = x_40;
} else {
 lean_dec_ref(x_40);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
x_13 = x_90;
x_14 = x_78;
goto block_36;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_12);
x_91 = !lean_is_exclusive(x_38);
if (x_91 == 0)
{
return x_38;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_38, 0);
x_93 = lean_ctor_get(x_38, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_38);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
block_36:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
lean_ctor_set(x_15, 0, x_12);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_14);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_13, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_14);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
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
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_14);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_computePrecompileImportsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_computePrecompileImportsAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_55; lean_object* x_56; uint8_t x_100; 
x_100 = lean_usize_dec_lt(x_4, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_5);
lean_ctor_set(x_101, 1, x_9);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_10);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_11);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_184; lean_object* x_185; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_104 = lean_array_uget(x_2, x_4);
x_105 = lean_ctor_get(x_5, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_5, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_107 = x_5;
} else {
 lean_dec_ref(x_5);
 x_107 = lean_box(0);
}
x_246 = lean_ctor_get(x_104, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_247, 2);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_ctor_get_uint8(x_248, sizeof(void*)*21);
lean_dec(x_248);
if (x_249 == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_dec(x_246);
x_251 = lean_ctor_get_uint8(x_250, sizeof(void*)*9);
lean_dec(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
lean_inc(x_104);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_104);
lean_ctor_set(x_253, 1, x_252);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_7);
x_254 = lean_apply_6(x_6, x_253, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
x_258 = !lean_is_exclusive(x_255);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = lean_ctor_get(x_255, 1);
x_260 = lean_ctor_get(x_255, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_256);
if (x_261 == 0)
{
lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_256, 0);
x_263 = 0;
x_264 = lean_box(x_263);
lean_ctor_set(x_255, 1, x_262);
lean_ctor_set(x_255, 0, x_264);
lean_ctor_set(x_256, 0, x_255);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_256);
lean_ctor_set(x_265, 1, x_259);
x_184 = x_265;
x_185 = x_257;
goto block_245;
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_256, 0);
x_267 = lean_ctor_get(x_256, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_256);
x_268 = 0;
x_269 = lean_box(x_268);
lean_ctor_set(x_255, 1, x_266);
lean_ctor_set(x_255, 0, x_269);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_255);
lean_ctor_set(x_270, 1, x_267);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_259);
x_184 = x_271;
x_185 = x_257;
goto block_245;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_272 = lean_ctor_get(x_255, 1);
lean_inc(x_272);
lean_dec(x_255);
x_273 = lean_ctor_get(x_256, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_256, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_275 = x_256;
} else {
 lean_dec_ref(x_256);
 x_275 = lean_box(0);
}
x_276 = 0;
x_277 = lean_box(x_276);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_273);
if (lean_is_scalar(x_275)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_275;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_274);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_272);
x_184 = x_280;
x_185 = x_257;
goto block_245;
}
}
else
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_254, 1);
lean_inc(x_281);
lean_dec(x_254);
x_282 = !lean_is_exclusive(x_255);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_255, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_256);
if (x_284 == 0)
{
x_184 = x_255;
x_185 = x_281;
goto block_245;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_256, 0);
x_286 = lean_ctor_get(x_256, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_256);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
lean_ctor_set(x_255, 0, x_287);
x_184 = x_255;
x_185 = x_281;
goto block_245;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_288 = lean_ctor_get(x_255, 1);
lean_inc(x_288);
lean_dec(x_255);
x_289 = lean_ctor_get(x_256, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_256, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_291 = x_256;
} else {
 lean_dec_ref(x_256);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_288);
x_184 = x_293;
x_185 = x_281;
goto block_245;
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_294 = !lean_is_exclusive(x_254);
if (x_294 == 0)
{
return x_254;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_254, 0);
x_296 = lean_ctor_get(x_254, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_254);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_104);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_104);
lean_ctor_set(x_299, 1, x_298);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_7);
x_300 = lean_apply_6(x_6, x_299, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; uint8_t x_304; 
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_304 = !lean_is_exclusive(x_301);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_305 = lean_ctor_get(x_301, 1);
x_306 = lean_ctor_get(x_301, 0);
lean_dec(x_306);
x_307 = !lean_is_exclusive(x_302);
if (x_307 == 0)
{
lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_302, 0);
x_309 = 1;
x_310 = lean_box(x_309);
lean_ctor_set(x_301, 1, x_308);
lean_ctor_set(x_301, 0, x_310);
lean_ctor_set(x_302, 0, x_301);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_302);
lean_ctor_set(x_311, 1, x_305);
x_184 = x_311;
x_185 = x_303;
goto block_245;
}
else
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_312 = lean_ctor_get(x_302, 0);
x_313 = lean_ctor_get(x_302, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_302);
x_314 = 1;
x_315 = lean_box(x_314);
lean_ctor_set(x_301, 1, x_312);
lean_ctor_set(x_301, 0, x_315);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_301);
lean_ctor_set(x_316, 1, x_313);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_305);
x_184 = x_317;
x_185 = x_303;
goto block_245;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_318 = lean_ctor_get(x_301, 1);
lean_inc(x_318);
lean_dec(x_301);
x_319 = lean_ctor_get(x_302, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_302, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_321 = x_302;
} else {
 lean_dec_ref(x_302);
 x_321 = lean_box(0);
}
x_322 = 1;
x_323 = lean_box(x_322);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_319);
if (lean_is_scalar(x_321)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_321;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_320);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_318);
x_184 = x_326;
x_185 = x_303;
goto block_245;
}
}
else
{
lean_object* x_327; uint8_t x_328; 
x_327 = lean_ctor_get(x_300, 1);
lean_inc(x_327);
lean_dec(x_300);
x_328 = !lean_is_exclusive(x_301);
if (x_328 == 0)
{
lean_object* x_329; uint8_t x_330; 
x_329 = lean_ctor_get(x_301, 0);
lean_dec(x_329);
x_330 = !lean_is_exclusive(x_302);
if (x_330 == 0)
{
x_184 = x_301;
x_185 = x_327;
goto block_245;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_302, 0);
x_332 = lean_ctor_get(x_302, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_302);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
lean_ctor_set(x_301, 0, x_333);
x_184 = x_301;
x_185 = x_327;
goto block_245;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_334 = lean_ctor_get(x_301, 1);
lean_inc(x_334);
lean_dec(x_301);
x_335 = lean_ctor_get(x_302, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_302, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_337 = x_302;
} else {
 lean_dec_ref(x_302);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_334);
x_184 = x_339;
x_185 = x_327;
goto block_245;
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_340 = !lean_is_exclusive(x_300);
if (x_340 == 0)
{
return x_300;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_300, 0);
x_342 = lean_ctor_get(x_300, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_300);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_246);
x_344 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_104);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_104);
lean_ctor_set(x_345, 1, x_344);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_7);
x_346 = lean_apply_6(x_6, x_345, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; uint8_t x_350; 
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
lean_dec(x_346);
x_350 = !lean_is_exclusive(x_347);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_351 = lean_ctor_get(x_347, 1);
x_352 = lean_ctor_get(x_347, 0);
lean_dec(x_352);
x_353 = !lean_is_exclusive(x_348);
if (x_353 == 0)
{
lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; 
x_354 = lean_ctor_get(x_348, 0);
x_355 = 1;
x_356 = lean_box(x_355);
lean_ctor_set(x_347, 1, x_354);
lean_ctor_set(x_347, 0, x_356);
lean_ctor_set(x_348, 0, x_347);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_348);
lean_ctor_set(x_357, 1, x_351);
x_184 = x_357;
x_185 = x_349;
goto block_245;
}
else
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_358 = lean_ctor_get(x_348, 0);
x_359 = lean_ctor_get(x_348, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_348);
x_360 = 1;
x_361 = lean_box(x_360);
lean_ctor_set(x_347, 1, x_358);
lean_ctor_set(x_347, 0, x_361);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_347);
lean_ctor_set(x_362, 1, x_359);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_351);
x_184 = x_363;
x_185 = x_349;
goto block_245;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_364 = lean_ctor_get(x_347, 1);
lean_inc(x_364);
lean_dec(x_347);
x_365 = lean_ctor_get(x_348, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_348, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_367 = x_348;
} else {
 lean_dec_ref(x_348);
 x_367 = lean_box(0);
}
x_368 = 1;
x_369 = lean_box(x_368);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_365);
if (lean_is_scalar(x_367)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_367;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_366);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_364);
x_184 = x_372;
x_185 = x_349;
goto block_245;
}
}
else
{
lean_object* x_373; uint8_t x_374; 
x_373 = lean_ctor_get(x_346, 1);
lean_inc(x_373);
lean_dec(x_346);
x_374 = !lean_is_exclusive(x_347);
if (x_374 == 0)
{
lean_object* x_375; uint8_t x_376; 
x_375 = lean_ctor_get(x_347, 0);
lean_dec(x_375);
x_376 = !lean_is_exclusive(x_348);
if (x_376 == 0)
{
x_184 = x_347;
x_185 = x_373;
goto block_245;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_348, 0);
x_378 = lean_ctor_get(x_348, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_348);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
lean_ctor_set(x_347, 0, x_379);
x_184 = x_347;
x_185 = x_373;
goto block_245;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_380 = lean_ctor_get(x_347, 1);
lean_inc(x_380);
lean_dec(x_347);
x_381 = lean_ctor_get(x_348, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_348, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_383 = x_348;
} else {
 lean_dec_ref(x_348);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_380);
x_184 = x_385;
x_185 = x_373;
goto block_245;
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_386 = !lean_is_exclusive(x_346);
if (x_386 == 0)
{
return x_346;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_346, 0);
x_388 = lean_ctor_get(x_346, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_346);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
block_183:
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_108, 0);
lean_dec(x_112);
x_55 = x_108;
x_56 = x_109;
goto block_99;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_55 = x_114;
x_56 = x_109;
goto block_99;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_108);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_108, 0);
lean_dec(x_116);
x_117 = !lean_is_exclusive(x_110);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_118 = lean_ctor_get(x_110, 0);
x_119 = lean_ctor_get(x_110, 1);
x_120 = l_Array_shrink___rarg(x_119, x_118);
lean_dec(x_118);
x_121 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_122 = lean_string_append(x_121, x_1);
x_123 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_ctor_get(x_104, 1);
lean_inc(x_125);
lean_dec(x_104);
x_126 = 1;
x_127 = l_Lean_Name_toString(x_125, x_126);
x_128 = lean_string_append(x_124, x_127);
lean_dec(x_127);
x_129 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_130 = lean_string_append(x_128, x_129);
x_131 = 3;
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_131);
x_133 = lean_array_push(x_120, x_132);
x_134 = lean_box(x_126);
if (lean_is_scalar(x_107)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_107;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_106);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set_tag(x_110, 0);
lean_ctor_set(x_110, 1, x_133);
lean_ctor_set(x_110, 0, x_137);
x_55 = x_108;
x_56 = x_109;
goto block_99;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_138 = lean_ctor_get(x_110, 0);
x_139 = lean_ctor_get(x_110, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_110);
x_140 = l_Array_shrink___rarg(x_139, x_138);
lean_dec(x_138);
x_141 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_142 = lean_string_append(x_141, x_1);
x_143 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_ctor_get(x_104, 1);
lean_inc(x_145);
lean_dec(x_104);
x_146 = 1;
x_147 = l_Lean_Name_toString(x_145, x_146);
x_148 = lean_string_append(x_144, x_147);
lean_dec(x_147);
x_149 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_150 = lean_string_append(x_148, x_149);
x_151 = 3;
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_151);
x_153 = lean_array_push(x_140, x_152);
x_154 = lean_box(x_146);
if (lean_is_scalar(x_107)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_107;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_106);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set(x_108, 0, x_158);
x_55 = x_108;
x_56 = x_109;
goto block_99;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_159 = lean_ctor_get(x_108, 1);
lean_inc(x_159);
lean_dec(x_108);
x_160 = lean_ctor_get(x_110, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_110, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_162 = x_110;
} else {
 lean_dec_ref(x_110);
 x_162 = lean_box(0);
}
x_163 = l_Array_shrink___rarg(x_161, x_160);
lean_dec(x_160);
x_164 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_165 = lean_string_append(x_164, x_1);
x_166 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_167 = lean_string_append(x_165, x_166);
x_168 = lean_ctor_get(x_104, 1);
lean_inc(x_168);
lean_dec(x_104);
x_169 = 1;
x_170 = l_Lean_Name_toString(x_168, x_169);
x_171 = lean_string_append(x_167, x_170);
lean_dec(x_170);
x_172 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_173 = lean_string_append(x_171, x_172);
x_174 = 3;
x_175 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_174);
x_176 = lean_array_push(x_163, x_175);
x_177 = lean_box(x_169);
if (lean_is_scalar(x_107)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_107;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_106);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
if (lean_is_scalar(x_162)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_162;
 lean_ctor_set_tag(x_181, 0);
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_176);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_159);
x_55 = x_182;
x_56 = x_109;
goto block_99;
}
}
}
block_245:
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
lean_dec(x_184);
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_186, 0);
lean_dec(x_190);
x_191 = !lean_is_exclusive(x_187);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_192 = lean_ctor_get(x_187, 0);
x_193 = lean_ctor_get(x_187, 1);
lean_inc(x_106);
x_194 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_106, x_193);
lean_dec(x_193);
x_195 = lean_unbox(x_192);
lean_dec(x_192);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_105);
lean_ctor_set(x_196, 1, x_194);
x_197 = lean_box(0);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
lean_ctor_set(x_186, 0, x_198);
lean_ctor_set(x_187, 1, x_188);
lean_ctor_set(x_187, 0, x_186);
x_108 = x_187;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_inc(x_104);
x_199 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_194, x_104);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_105);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_186, 0, x_202);
lean_ctor_set(x_187, 1, x_188);
lean_ctor_set(x_187, 0, x_186);
x_108 = x_187;
x_109 = x_185;
goto block_183;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_203 = lean_ctor_get(x_187, 0);
x_204 = lean_ctor_get(x_187, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_187);
lean_inc(x_106);
x_205 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_106, x_204);
lean_dec(x_204);
x_206 = lean_unbox(x_203);
lean_dec(x_203);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_105);
lean_ctor_set(x_207, 1, x_205);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
lean_ctor_set(x_186, 0, x_209);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_186);
lean_ctor_set(x_210, 1, x_188);
x_108 = x_210;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_inc(x_104);
x_211 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_205, x_104);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_105);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_box(0);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
lean_ctor_set(x_186, 0, x_214);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_186);
lean_ctor_set(x_215, 1, x_188);
x_108 = x_215;
x_109 = x_185;
goto block_183;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_216 = lean_ctor_get(x_186, 1);
lean_inc(x_216);
lean_dec(x_186);
x_217 = lean_ctor_get(x_187, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_187, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_219 = x_187;
} else {
 lean_dec_ref(x_187);
 x_219 = lean_box(0);
}
lean_inc(x_106);
x_220 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_106, x_218);
lean_dec(x_218);
x_221 = lean_unbox(x_217);
lean_dec(x_217);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_105);
lean_ctor_set(x_222, 1, x_220);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_216);
if (lean_is_scalar(x_219)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_219;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_188);
x_108 = x_226;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_inc(x_104);
x_227 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_220, x_104);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_105);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_216);
if (lean_is_scalar(x_219)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_219;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_188);
x_108 = x_232;
x_109 = x_185;
goto block_183;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_105);
x_233 = !lean_is_exclusive(x_184);
if (x_233 == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_184, 0);
lean_dec(x_234);
x_235 = !lean_is_exclusive(x_186);
if (x_235 == 0)
{
x_108 = x_184;
x_109 = x_185;
goto block_183;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_186, 0);
x_237 = lean_ctor_get(x_186, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_186);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_184, 0, x_238);
x_108 = x_184;
x_109 = x_185;
goto block_183;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_184, 1);
lean_inc(x_239);
lean_dec(x_184);
x_240 = lean_ctor_get(x_186, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_186, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_242 = x_186;
} else {
 lean_dec_ref(x_186);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_239);
x_108 = x_244;
x_109 = x_185;
goto block_183;
}
}
}
}
block_54:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_28 = x_14;
} else {
 lean_dec_ref(x_14);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
x_4 = x_37;
x_5 = x_35;
x_9 = x_34;
x_10 = x_33;
x_11 = x_13;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_12, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_13);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_12, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_13);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_ctor_get(x_14, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_50 = x_14;
} else {
 lean_dec_ref(x_14);
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
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_13);
return x_53;
}
}
}
block_99:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_57, 0, x_65);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_59, 0);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_59);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_57, 0, x_69);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_dec(x_57);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_73 = x_59;
} else {
 lean_dec_ref(x_59);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_55, 0, x_76);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
lean_dec(x_55);
x_78 = lean_ctor_get(x_57, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_79 = x_57;
} else {
 lean_dec_ref(x_57);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_59, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_59, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_82 = x_59;
} else {
 lean_dec_ref(x_59);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_79)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_79;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
x_12 = x_86;
x_13 = x_56;
goto block_54;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_55);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_55, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_57);
if (x_89 == 0)
{
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_57, 0);
x_91 = lean_ctor_get(x_57, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_57);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_55, 0, x_92);
x_12 = x_55;
x_13 = x_56;
goto block_54;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_55, 1);
lean_inc(x_93);
lean_dec(x_55);
x_94 = lean_ctor_get(x_57, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_57, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_96 = x_57;
} else {
 lean_dec_ref(x_57);
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
x_12 = x_98;
x_13 = x_56;
goto block_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recComputePrecompileImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_importsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_58; lean_object* x_59; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_21, 7);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_System_FilePath_join(x_20, x_22);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_System_FilePath_join(x_23, x_25);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_Module_recParseImports___closed__1;
x_29 = l_Lean_modToFilePath(x_26, x_27, x_28);
lean_dec(x_26);
x_30 = lean_array_get_size(x_16);
x_31 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_32 = 0;
x_33 = lean_array_get_size(x_17);
x_58 = l_Lake_collectImportsAux___closed__1;
x_59 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1(x_29, x_16, x_31, x_32, x_58, x_2, x_3, x_4, x_17, x_15, x_13);
lean_dec(x_16);
lean_dec(x_29);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_60, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_61);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_61, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_ctor_set(x_61, 0, x_71);
x_34 = x_60;
x_35 = x_65;
goto block_57;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
lean_dec(x_61);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
lean_dec(x_62);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
lean_ctor_set(x_60, 0, x_75);
x_34 = x_60;
x_35 = x_65;
goto block_57;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_dec(x_60);
x_77 = lean_ctor_get(x_61, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_78 = x_61;
} else {
 lean_dec_ref(x_61);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_62, 1);
lean_inc(x_79);
lean_dec(x_62);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
x_34 = x_82;
x_35 = x_65;
goto block_57;
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_62);
x_83 = lean_ctor_get(x_59, 1);
lean_inc(x_83);
lean_dec(x_59);
x_84 = !lean_is_exclusive(x_60);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_60, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_61);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_61, 1);
x_88 = lean_ctor_get(x_61, 0);
lean_dec(x_88);
x_89 = lean_array_get_size(x_87);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_89);
x_34 = x_60;
x_35 = x_83;
goto block_57;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_61, 1);
lean_inc(x_90);
lean_dec(x_61);
x_91 = lean_array_get_size(x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_60, 0, x_92);
x_34 = x_60;
x_35 = x_83;
goto block_57;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_60, 1);
lean_inc(x_93);
lean_dec(x_60);
x_94 = lean_ctor_get(x_61, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_95 = x_61;
} else {
 lean_dec_ref(x_61);
 x_95 = lean_box(0);
}
x_96 = lean_array_get_size(x_94);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_95;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
x_34 = x_98;
x_35 = x_83;
goto block_57;
}
}
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_59, 1);
lean_inc(x_99);
lean_dec(x_59);
x_100 = !lean_is_exclusive(x_60);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_60, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_61);
if (x_102 == 0)
{
x_34 = x_60;
x_35 = x_99;
goto block_57;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_61, 0);
x_104 = lean_ctor_get(x_61, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_61);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_60, 0, x_105);
x_34 = x_60;
x_35 = x_99;
goto block_57;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_60, 1);
lean_inc(x_106);
lean_dec(x_60);
x_107 = lean_ctor_get(x_61, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_61, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_109 = x_61;
} else {
 lean_dec_ref(x_61);
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
x_34 = x_111;
x_35 = x_99;
goto block_57;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_33);
lean_dec(x_14);
x_112 = !lean_is_exclusive(x_59);
if (x_112 == 0)
{
return x_59;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_59, 0);
x_114 = lean_ctor_get(x_59, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_59);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
block_57:
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
if (lean_is_scalar(x_14)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_14;
}
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
if (lean_is_scalar(x_14)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_14;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_34, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_36, 0);
lean_dec(x_46);
lean_ctor_set(x_36, 0, x_33);
if (lean_is_scalar(x_14)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_14;
}
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_35);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_dec(x_36);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_34, 0, x_49);
if (lean_is_scalar(x_14)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_14;
}
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_35);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_dec(x_34);
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_53 = x_36;
} else {
 lean_dec_ref(x_36);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_33);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
if (lean_is_scalar(x_14)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_14;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_35);
return x_56;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_10);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_10, 0);
lean_dec(x_117);
x_118 = !lean_is_exclusive(x_11);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_11, 0);
lean_dec(x_119);
x_120 = !lean_is_exclusive(x_12);
if (x_120 == 0)
{
return x_10;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_12, 0);
x_122 = lean_ctor_get(x_12, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_12);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_11, 0, x_123);
return x_10;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_11, 1);
lean_inc(x_124);
lean_dec(x_11);
x_125 = lean_ctor_get(x_12, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_12, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_127 = x_12;
} else {
 lean_dec_ref(x_12);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
lean_ctor_set(x_10, 0, x_129);
return x_10;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_130 = lean_ctor_get(x_10, 1);
lean_inc(x_130);
lean_dec(x_10);
x_131 = lean_ctor_get(x_11, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_132 = x_11;
} else {
 lean_dec_ref(x_11);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_12, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_12, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_135 = x_12;
} else {
 lean_dec_ref(x_12);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
if (lean_is_scalar(x_132)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_132;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_131);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_130);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_10);
if (x_139 == 0)
{
return x_10;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_10, 0);
x_141 = lean_ctor_get(x_10, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_10);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Module_recComputePrecompileImports(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_Module_precompileImportsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_precompileImportsFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_precompileImportsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_precompileImportsFacetConfig___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_precompileImportsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_precompileImportsFacetConfig___closed__2;
return x_1;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_array_uget(x_5, x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_5, x_4, x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_name_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
x_22 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1(x_16, x_22, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_32 = lean_array_uset(x_18, x_4, x_28);
x_4 = x_31;
x_5 = x_32;
x_9 = x_29;
x_10 = x_27;
x_11 = x_26;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_23, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_24, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_24, 0, x_41);
return x_23;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_25, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_45 = x_25;
} else {
 lean_dec_ref(x_25);
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
lean_ctor_set(x_23, 0, x_47);
return x_23;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_dec(x_23);
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
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_25, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_53 = x_25;
} else {
 lean_dec_ref(x_25);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_48);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_23);
if (x_57 == 0)
{
return x_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_23, 0);
x_59 = lean_ctor_get(x_23, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_23);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 2);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_63, 7);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_System_FilePath_join(x_62, x_64);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 2);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_System_FilePath_join(x_65, x_67);
x_69 = l_Lake_Module_recParseImports___closed__1;
x_70 = l_Lean_modToFilePath(x_68, x_20, x_69);
lean_dec(x_68);
x_71 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___closed__1;
x_74 = lean_string_append(x_72, x_73);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_array_push(x_9, x_76);
x_78 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_79 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1(x_16, x_78, x_6, x_7, x_8, x_77, x_10, x_11);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = 1;
x_87 = lean_usize_add(x_4, x_86);
x_88 = lean_array_uset(x_18, x_4, x_84);
x_4 = x_87;
x_5 = x_88;
x_9 = x_85;
x_10 = x_83;
x_11 = x_82;
goto _start;
}
else
{
uint8_t x_90; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_79);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_79, 0);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_80);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_80, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_81);
if (x_94 == 0)
{
return x_79;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_81, 0);
x_96 = lean_ctor_get(x_81, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_81);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_80, 0, x_97);
return x_79;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_80, 1);
lean_inc(x_98);
lean_dec(x_80);
x_99 = lean_ctor_get(x_81, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_81, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_101 = x_81;
} else {
 lean_dec_ref(x_81);
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
lean_ctor_set(x_79, 0, x_103);
return x_79;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_104 = lean_ctor_get(x_79, 1);
lean_inc(x_104);
lean_dec(x_79);
x_105 = lean_ctor_get(x_80, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_106 = x_80;
} else {
 lean_dec_ref(x_80);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_81, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_81, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_109 = x_81;
} else {
 lean_dec_ref(x_81);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
if (lean_is_scalar(x_106)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_106;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_79);
if (x_113 == 0)
{
return x_79;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_79, 0);
x_115 = lean_ctor_get(x_79, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_79);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_5);
x_19 = lean_apply_6(x_4, x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = 1;
x_27 = lean_usize_add(x_2, x_26);
x_28 = lean_array_uset(x_16, x_2, x_24);
x_2 = x_27;
x_3 = x_28;
x_7 = x_25;
x_8 = x_23;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_19, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_20, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_20, 0, x_37);
return x_19;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_41 = x_21;
} else {
 lean_dec_ref(x_21);
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
lean_ctor_set(x_19, 0, x_43);
return x_19;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_dec(x_19);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_46 = x_20;
} else {
 lean_dec_ref(x_20);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_21, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_49 = x_21;
} else {
 lean_dec_ref(x_21);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_46;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_19);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_19, 0);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_19);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_Dynlib_dir_x3f(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
if (lean_obj_tag(x_7) == 0)
{
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_array_push(x_4, x_11);
x_2 = x_9;
x_4 = x_12;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__4(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l_List_elem___at_Lake_Module_recBuildDeps___spec__8(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_6, 2);
x_8 = lean_ctor_get(x_4, 2);
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
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_Module_recBuildDeps___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_5, 2);
x_7 = l_Lean_Name_hash___override(x_6);
x_8 = lean_hashset_mk_idx(x_4, x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_List_elem___at_Lake_Module_recBuildDeps___spec__8(x_2, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Module_recBuildDeps___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_17 = lean_apply_1(x_1, x_14);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_19 = lean_hashset_mk_idx(x_16, x_18);
x_20 = lean_array_uget(x_2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_uset(x_2, x_19, x_21);
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_Module_recBuildDeps___spec__12___at_Lake_Module_recBuildDeps___spec__13(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_6, x_9);
x_11 = lean_array_uget(x_1, x_10);
lean_ctor_set(x_2, 1, x_11);
x_12 = lean_array_uset(x_1, x_10, x_2);
x_1 = x_12;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Name_hash___override(x_18);
lean_dec(x_18);
x_20 = lean_hashset_mk_idx(x_16, x_19);
x_21 = lean_array_uget(x_1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_Module_recBuildDeps___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lake_Module_recBuildDeps___spec__12___at_Lake_Module_recBuildDeps___spec__13(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_Module_recBuildDeps___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashSetImp_moveEntries___at_Lake_Module_recBuildDeps___spec__11(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Module_recBuildDeps___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_8, 2);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_9, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_List_replace___at_Lake_Module_recBuildDeps___spec__14(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_13);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_16, 2);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_name_eq(x_17, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_List_replace___at_Lake_Module_recBuildDeps___spec__14(x_15, x_2, x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_Module_recBuildDeps___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
lean_inc(x_6);
x_10 = lean_hashset_mk_idx(x_6, x_9);
x_11 = lean_array_uget(x_5, x_10);
x_12 = l_List_elem___at_Lake_Module_recBuildDeps___spec__8(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_array_uset(x_5, x_10, x_15);
x_17 = lean_nat_dec_le(x_14, x_6);
lean_dec(x_6);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashSetImp_expand___at_Lake_Module_recBuildDeps___spec__10(x_14, x_16);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_5, x_10, x_19);
lean_inc(x_2);
x_21 = l_List_replace___at_Lake_Module_recBuildDeps___spec__14(x_11, x_2, x_2);
lean_dec(x_2);
x_22 = lean_array_uset(x_20, x_10, x_21);
lean_ctor_set(x_1, 1, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_array_get_size(x_24);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Name_hash___override(x_27);
lean_dec(x_27);
lean_inc(x_25);
x_29 = lean_hashset_mk_idx(x_25, x_28);
x_30 = lean_array_uget(x_24, x_29);
x_31 = l_List_elem___at_Lake_Module_recBuildDeps___spec__8(x_2, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_23, x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_array_uset(x_24, x_29, x_34);
x_36 = lean_nat_dec_le(x_33, x_25);
lean_dec(x_25);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_HashSetImp_expand___at_Lake_Module_recBuildDeps___spec__10(x_33, x_35);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_25);
x_39 = lean_box(0);
x_40 = lean_array_uset(x_24, x_29, x_39);
lean_inc(x_2);
x_41 = l_List_replace___at_Lake_Module_recBuildDeps___spec__14(x_30, x_2, x_2);
lean_dec(x_2);
x_42 = lean_array_uset(x_40, x_29, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashablePackage___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqPackage___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_HashSetImp_contains___at_Lake_Module_recBuildDeps___spec__7(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = lean_array_push(x_5, x_2);
x_7 = l_Lean_HashSetImp_insert___at_Lake_Module_recBuildDeps___spec__9(x_3, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__15(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_9 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_4, x_8);
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
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
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
x_16 = lean_apply_7(x_2, x_14, x_3, x_4, x_5, x_15, x_13, x_12);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_10, 0, x_24);
return x_9;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_28 = x_11;
} else {
 lean_dec_ref(x_11);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_9, 0, x_30);
return x_9;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_33 = x_10;
} else {
 lean_dec_ref(x_10);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_36 = x_11;
} else {
 lean_dec_ref(x_11);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_33;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
return x_9;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16___rarg), 8, 0);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___lambda__1___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Module_recBuildDeps___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___lambda__1___closed__3___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lake_platformTrace;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
x_2 = l_Lake_Module_recBuildDeps___lambda__1___closed__3___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lake_BuildTrace_mix(x_1, x_2);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_14, 8);
x_16 = lean_array_get_size(x_10);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(x_10, x_17, x_16);
x_19 = l_Array_append___rarg(x_4, x_18);
lean_dec(x_18);
x_20 = lean_array_to_list(lean_box(0), x_19);
x_21 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_22 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_21, x_5, x_10);
x_23 = lean_array_get_size(x_6);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_24, x_5, x_6);
x_26 = l_Array_append___rarg(x_22, x_25);
lean_dec(x_25);
lean_ctor_set(x_8, 1, x_26);
lean_ctor_set(x_8, 0, x_20);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_27, 2);
x_29 = lean_ctor_get(x_28, 1);
x_30 = lean_ctor_get(x_29, 8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lake_BuildTrace_mix(x_7, x_11);
x_32 = l_Lake_BuildTrace_mix(x_12, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_unbox(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Lake_Module_recBuildDeps___lambda__1___closed__3;
x_37 = l_Lake_BuildTrace_mix(x_11, x_36);
x_38 = l_Lake_BuildTrace_mix(x_7, x_37);
x_39 = l_Lake_BuildTrace_mix(x_12, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_7);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = l_Lake_Module_recBuildDeps___lambda__1___closed__3;
x_45 = l_Lake_BuildTrace_mix(x_11, x_44);
x_46 = l_Lake_BuildTrace_mix(x_7, x_45);
x_47 = l_Lake_BuildTrace_mix(x_12, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_7);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_12);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; lean_object* x_62; lean_object* x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_52 = l_Lake_BuildTrace_mix(x_1, x_2);
x_53 = lean_ctor_get(x_3, 1);
x_54 = lean_ctor_get(x_53, 0);
x_55 = lean_ctor_get(x_54, 8);
x_56 = lean_array_get_size(x_50);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(x_50, x_57, x_56);
x_59 = l_Array_append___rarg(x_4, x_58);
lean_dec(x_58);
x_60 = lean_array_to_list(lean_box(0), x_59);
x_61 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_62 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_61, x_5, x_50);
x_63 = lean_array_get_size(x_6);
x_64 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_65 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_64, x_5, x_6);
x_66 = l_Array_append___rarg(x_62, x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_3, 0);
x_69 = lean_ctor_get(x_68, 2);
x_70 = lean_ctor_get(x_69, 1);
x_71 = lean_ctor_get(x_70, 8);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = l_Lake_BuildTrace_mix(x_7, x_51);
x_73 = l_Lake_BuildTrace_mix(x_52, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_unbox(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = l_Lake_Module_recBuildDeps___lambda__1___closed__3;
x_78 = l_Lake_BuildTrace_mix(x_51, x_77);
x_79 = l_Lake_BuildTrace_mix(x_7, x_78);
x_80 = l_Lake_BuildTrace_mix(x_52, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_67);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
else
{
lean_object* x_82; 
lean_dec(x_51);
lean_dec(x_7);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_67);
lean_ctor_set(x_82, 1, x_52);
return x_82;
}
}
}
else
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_55, 0);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = l_Lake_Module_recBuildDeps___lambda__1___closed__3;
x_86 = l_Lake_BuildTrace_mix(x_51, x_85);
x_87 = l_Lake_BuildTrace_mix(x_7, x_86);
x_88 = l_Lake_BuildTrace_mix(x_52, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_67);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec(x_51);
lean_dec(x_7);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_67);
lean_ctor_set(x_90, 1, x_52);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lake_JobState_merge(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = l_Lake_JobState_merge(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_nat_add(x_14, x_11);
lean_dec(x_11);
lean_dec(x_14);
x_16 = l_Lake_JobState_merge(x_1, x_12);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_15);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_nat_add(x_20, x_17);
lean_dec(x_17);
lean_dec(x_20);
x_22 = l_Lake_JobState_merge(x_1, x_18);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_box_usize(x_5);
x_15 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__1___boxed), 8, 7);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_14);
lean_closure_set(x_15, 5, x_12);
lean_closure_set(x_15, 6, x_13);
x_16 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l_Task_Priority_default;
x_19 = 0;
x_20 = lean_task_map(x_16, x_17, x_18, x_19);
x_21 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_21, 0, x_10);
x_22 = 1;
x_23 = lean_task_map(x_21, x_20, x_18, x_22);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 0, x_23);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_box_usize(x_5);
x_27 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__1___boxed), 8, 7);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_3);
lean_closure_set(x_27, 3, x_4);
lean_closure_set(x_27, 4, x_26);
lean_closure_set(x_27, 5, x_24);
lean_closure_set(x_27, 6, x_25);
x_28 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = l_Task_Priority_default;
x_31 = 0;
x_32 = lean_task_map(x_28, x_29, x_30, x_31);
x_33 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_33, 0, x_10);
x_34 = 1;
x_35 = lean_task_map(x_33, x_32, x_30, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_8);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_task_pure(x_7);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_7);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_task_pure(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_8);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box_usize(x_5);
x_14 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__3___boxed), 8, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_13);
lean_closure_set(x_14, 5, x_6);
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = lean_io_bind_task(x_12, x_14, x_15, x_16, x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_20, 0, x_10);
x_21 = 1;
x_22 = lean_task_map(x_20, x_19, x_15, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_25, 0, x_10);
x_26 = 1;
x_27 = lean_task_map(x_25, x_23, x_15, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_task_pure(x_7);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_task_pure(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box_usize(x_5);
x_14 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__4___boxed), 8, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_13);
lean_closure_set(x_14, 5, x_6);
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = lean_io_bind_task(x_12, x_14, x_15, x_16, x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_20, 0, x_10);
x_21 = 1;
x_22 = lean_task_map(x_20, x_19, x_15, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_25, 0, x_10);
x_26 = 1;
x_27 = lean_task_map(x_25, x_23, x_15, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_task_pure(x_7);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_task_pure(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_array_get_size(x_5);
x_13 = lean_usize_of_nat(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(x_13, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_145; uint8_t x_146; 
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
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_nat_dec_lt(x_145, x_12);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_12);
lean_dec(x_5);
x_147 = lean_ctor_get(x_4, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_147, 2);
lean_inc(x_148);
x_149 = lean_ctor_get_uint8(x_148, sizeof(void*)*21);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_4, 1);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_150, sizeof(void*)*9);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_147);
x_152 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_21 = x_152;
goto block_144;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_154 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_153, x_147);
x_21 = x_154;
goto block_144;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_156 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_155, x_147);
x_21 = x_156;
goto block_144;
}
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_4, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_157, 2);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_158, sizeof(void*)*21);
lean_dec(x_158);
x_160 = lean_nat_dec_le(x_12, x_12);
lean_dec(x_12);
if (x_160 == 0)
{
lean_dec(x_5);
if (x_159 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_4, 1);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_161, sizeof(void*)*9);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; 
lean_dec(x_157);
x_163 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_21 = x_163;
goto block_144;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_165 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_164, x_157);
x_21 = x_165;
goto block_144;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_167 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_166, x_157);
x_21 = x_167;
goto block_144;
}
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_169 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__15(x_5, x_1, x_13, x_168);
lean_dec(x_5);
if (x_159 == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_4, 1);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_170, sizeof(void*)*9);
lean_dec(x_170);
if (x_171 == 0)
{
lean_dec(x_157);
x_21 = x_169;
goto block_144;
}
else
{
lean_object* x_172; 
x_172 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_169, x_157);
x_21 = x_172;
goto block_144;
}
}
else
{
lean_object* x_173; 
x_173 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_169, x_157);
x_21 = x_173;
goto block_144;
}
}
}
block_144:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lake_recBuildExternDynlibs(x_22, x_6, x_7, x_8, x_20, x_18, x_17);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_25, 1);
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
x_35 = l_Lake_BuildJob_collectArray___rarg(x_33);
lean_dec(x_33);
x_36 = l_Lake_BuildJob_collectArray___rarg(x_19);
lean_dec(x_19);
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
x_40 = lean_box_usize(x_1);
x_41 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 8, 6);
lean_closure_set(x_41, 0, x_3);
lean_closure_set(x_41, 1, x_36);
lean_closure_set(x_41, 2, x_4);
lean_closure_set(x_41, 3, x_34);
lean_closure_set(x_41, 4, x_40);
lean_closure_set(x_41, 5, x_35);
x_42 = l_Task_Priority_default;
x_43 = 0;
x_44 = lean_io_bind_task(x_38, x_41, x_42, x_43, x_27);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_ctor_set(x_2, 0, x_46);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_26, 1, x_28);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_44, 0, x_26);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set(x_2, 0, x_47);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_26, 1, x_28);
lean_ctor_set(x_26, 0, x_25);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_26);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_free_object(x_2);
lean_dec(x_39);
lean_free_object(x_26);
lean_free_object(x_25);
lean_dec(x_30);
lean_dec(x_28);
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
return x_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_44);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_2);
x_56 = lean_box_usize(x_1);
x_57 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 8, 6);
lean_closure_set(x_57, 0, x_3);
lean_closure_set(x_57, 1, x_36);
lean_closure_set(x_57, 2, x_4);
lean_closure_set(x_57, 3, x_34);
lean_closure_set(x_57, 4, x_56);
lean_closure_set(x_57, 5, x_35);
x_58 = l_Task_Priority_default;
x_59 = 0;
x_60 = lean_io_bind_task(x_54, x_57, x_58, x_59, x_27);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_55);
lean_ctor_set(x_25, 0, x_64);
lean_ctor_set(x_26, 1, x_28);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_26);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_55);
lean_free_object(x_26);
lean_free_object(x_25);
lean_dec(x_30);
lean_dec(x_28);
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_68 = x_60;
} else {
 lean_dec_ref(x_60);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_70 = lean_ctor_get(x_26, 0);
x_71 = lean_ctor_get(x_26, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_26);
x_72 = l_Lake_BuildJob_collectArray___rarg(x_70);
lean_dec(x_70);
x_73 = l_Lake_BuildJob_collectArray___rarg(x_19);
lean_dec(x_19);
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_76 = x_2;
} else {
 lean_dec_ref(x_2);
 x_76 = lean_box(0);
}
x_77 = lean_box_usize(x_1);
x_78 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 8, 6);
lean_closure_set(x_78, 0, x_3);
lean_closure_set(x_78, 1, x_73);
lean_closure_set(x_78, 2, x_4);
lean_closure_set(x_78, 3, x_71);
lean_closure_set(x_78, 4, x_77);
lean_closure_set(x_78, 5, x_72);
x_79 = l_Task_Priority_default;
x_80 = 0;
x_81 = lean_io_bind_task(x_74, x_78, x_79, x_80, x_27);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
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
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_75);
lean_ctor_set(x_25, 0, x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_25);
lean_ctor_set(x_86, 1, x_28);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_76);
lean_dec(x_75);
lean_free_object(x_25);
lean_dec(x_30);
lean_dec(x_28);
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_90 = x_81;
} else {
 lean_dec_ref(x_81);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; 
x_92 = lean_ctor_get(x_25, 1);
lean_inc(x_92);
lean_dec(x_25);
x_93 = lean_ctor_get(x_26, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_26, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_95 = x_26;
} else {
 lean_dec_ref(x_26);
 x_95 = lean_box(0);
}
x_96 = l_Lake_BuildJob_collectArray___rarg(x_93);
lean_dec(x_93);
x_97 = l_Lake_BuildJob_collectArray___rarg(x_19);
lean_dec(x_19);
x_98 = lean_ctor_get(x_2, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_100 = x_2;
} else {
 lean_dec_ref(x_2);
 x_100 = lean_box(0);
}
x_101 = lean_box_usize(x_1);
x_102 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 8, 6);
lean_closure_set(x_102, 0, x_3);
lean_closure_set(x_102, 1, x_97);
lean_closure_set(x_102, 2, x_4);
lean_closure_set(x_102, 3, x_94);
lean_closure_set(x_102, 4, x_101);
lean_closure_set(x_102, 5, x_96);
x_103 = l_Task_Priority_default;
x_104 = 0;
x_105 = lean_io_bind_task(x_98, x_102, x_103, x_104, x_27);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_100;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_99);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_92);
if (lean_is_scalar(x_95)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_95;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_28);
if (lean_is_scalar(x_108)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_108;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_28);
x_113 = lean_ctor_get(x_105, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_105, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_115 = x_105;
} else {
 lean_dec_ref(x_105);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_23);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_23, 0);
lean_dec(x_118);
x_119 = !lean_is_exclusive(x_24);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_24, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_25);
if (x_121 == 0)
{
return x_23;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_25, 0);
x_123 = lean_ctor_get(x_25, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_25);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_24, 0, x_124);
return x_23;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_24, 1);
lean_inc(x_125);
lean_dec(x_24);
x_126 = lean_ctor_get(x_25, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_25, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_128 = x_25;
} else {
 lean_dec_ref(x_25);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
lean_ctor_set(x_23, 0, x_130);
return x_23;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_131 = lean_ctor_get(x_23, 1);
lean_inc(x_131);
lean_dec(x_23);
x_132 = lean_ctor_get(x_24, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_133 = x_24;
} else {
 lean_dec_ref(x_24);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_25, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_25, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_136 = x_25;
} else {
 lean_dec_ref(x_25);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
if (lean_is_scalar(x_133)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_133;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_132);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_131);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_23);
if (x_140 == 0)
{
return x_23;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_23, 0);
x_142 = lean_ctor_get(x_23, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_23);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = !lean_is_exclusive(x_14);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_14, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_15);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_ctor_get(x_15, 0);
lean_dec(x_177);
x_178 = !lean_is_exclusive(x_16);
if (x_178 == 0)
{
return x_14;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_16, 0);
x_180 = lean_ctor_get(x_16, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_16);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_15, 0, x_181);
return x_14;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_182 = lean_ctor_get(x_15, 1);
lean_inc(x_182);
lean_dec(x_15);
x_183 = lean_ctor_get(x_16, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_16, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_185 = x_16;
} else {
 lean_dec_ref(x_16);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_182);
lean_ctor_set(x_14, 0, x_187);
return x_14;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_188 = lean_ctor_get(x_14, 1);
lean_inc(x_188);
lean_dec(x_14);
x_189 = lean_ctor_get(x_15, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_190 = x_15;
} else {
 lean_dec_ref(x_15);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_16, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_16, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_193 = x_16;
} else {
 lean_dec_ref(x_16);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
if (lean_is_scalar(x_190)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_190;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_189);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_188);
return x_196;
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = !lean_is_exclusive(x_14);
if (x_197 == 0)
{
return x_14;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_14, 0);
x_199 = lean_ctor_get(x_14, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_14);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lake_Module_importsFacetConfig___closed__2;
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_apply_6(x_4, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_array_get_size(x_17);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(x_1, x_2, x_20, x_21, x_17, x_4, x_5, x_6, x_18, x_16, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lake_BuildJob_mixArray___rarg(x_27);
lean_dec(x_27);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*21);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*9);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_5);
x_37 = lean_apply_6(x_4, x_36, x_5, x_6, x_28, x_26, x_25);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lake_Module_recBuildDeps___lambda__6(x_21, x_3, x_29, x_2, x_42, x_4, x_5, x_6, x_43, x_41, x_40);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_37, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
return x_37;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_38, 0, x_52);
return x_37;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_dec(x_38);
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_56 = x_39;
} else {
 lean_dec_ref(x_39);
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
lean_ctor_set(x_37, 0, x_58);
return x_37;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_37, 1);
lean_inc(x_59);
lean_dec(x_37);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_61 = x_38;
} else {
 lean_dec_ref(x_38);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_39, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_64 = x_39;
} else {
 lean_dec_ref(x_39);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_59);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_37);
if (x_68 == 0)
{
return x_37;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_37, 0);
x_70 = lean_ctor_get(x_37, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_37);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_5);
x_74 = lean_apply_6(x_4, x_73, x_5, x_6, x_28, x_26, x_25);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = l_Lake_Module_recBuildDeps___lambda__6(x_21, x_3, x_29, x_2, x_79, x_4, x_5, x_6, x_80, x_78, x_77);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_74);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_74, 0);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_75);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_75, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_76);
if (x_86 == 0)
{
return x_74;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_76, 0);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_76);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_75, 0, x_89);
return x_74;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_75, 1);
lean_inc(x_90);
lean_dec(x_75);
x_91 = lean_ctor_get(x_76, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_76, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_93 = x_76;
} else {
 lean_dec_ref(x_76);
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
lean_ctor_set(x_74, 0, x_95);
return x_74;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_74, 1);
lean_inc(x_96);
lean_dec(x_74);
x_97 = lean_ctor_get(x_75, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_98 = x_75;
} else {
 lean_dec_ref(x_75);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_76, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_76, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_101 = x_76;
} else {
 lean_dec_ref(x_76);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
if (lean_is_scalar(x_98)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_98;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_97);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_96);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_74);
if (x_105 == 0)
{
return x_74;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_74, 0);
x_107 = lean_ctor_get(x_74, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_74);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_109);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_5);
x_111 = lean_apply_6(x_4, x_110, x_5, x_6, x_28, x_26, x_25);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
lean_dec(x_113);
x_118 = l_Lake_Module_recBuildDeps___lambda__6(x_21, x_3, x_29, x_2, x_116, x_4, x_5, x_6, x_117, x_115, x_114);
return x_118;
}
else
{
uint8_t x_119; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_111);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_111, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_112);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_112, 0);
lean_dec(x_122);
x_123 = !lean_is_exclusive(x_113);
if (x_123 == 0)
{
return x_111;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_113, 0);
x_125 = lean_ctor_get(x_113, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_113);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_112, 0, x_126);
return x_111;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_127 = lean_ctor_get(x_112, 1);
lean_inc(x_127);
lean_dec(x_112);
x_128 = lean_ctor_get(x_113, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_113, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_130 = x_113;
} else {
 lean_dec_ref(x_113);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_127);
lean_ctor_set(x_111, 0, x_132);
return x_111;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_111, 1);
lean_inc(x_133);
lean_dec(x_111);
x_134 = lean_ctor_get(x_112, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_135 = x_112;
} else {
 lean_dec_ref(x_112);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_113, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_113, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_138 = x_113;
} else {
 lean_dec_ref(x_113);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
if (lean_is_scalar(x_135)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_135;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_134);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_133);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = !lean_is_exclusive(x_111);
if (x_142 == 0)
{
return x_111;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_111, 0);
x_144 = lean_ctor_get(x_111, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_111);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_22);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_22, 0);
lean_dec(x_147);
x_148 = !lean_is_exclusive(x_23);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_23, 0);
lean_dec(x_149);
x_150 = !lean_is_exclusive(x_24);
if (x_150 == 0)
{
return x_22;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_24, 0);
x_152 = lean_ctor_get(x_24, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_24);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_23, 0, x_153);
return x_22;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_23, 1);
lean_inc(x_154);
lean_dec(x_23);
x_155 = lean_ctor_get(x_24, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_24, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_157 = x_24;
} else {
 lean_dec_ref(x_24);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_154);
lean_ctor_set(x_22, 0, x_159);
return x_22;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_160 = lean_ctor_get(x_22, 1);
lean_inc(x_160);
lean_dec(x_22);
x_161 = lean_ctor_get(x_23, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_162 = x_23;
} else {
 lean_dec_ref(x_23);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_24, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_24, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_165 = x_24;
} else {
 lean_dec_ref(x_24);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
if (lean_is_scalar(x_162)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_162;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_161);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_160);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_22);
if (x_169 == 0)
{
return x_22;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_22, 0);
x_171 = lean_ctor_get(x_22, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_22);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_12);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_12, 0);
lean_dec(x_174);
x_175 = !lean_is_exclusive(x_13);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_13, 0);
lean_dec(x_176);
x_177 = !lean_is_exclusive(x_14);
if (x_177 == 0)
{
return x_12;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_14, 0);
x_179 = lean_ctor_get(x_14, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_14);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_13, 0, x_180);
return x_12;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_181 = lean_ctor_get(x_13, 1);
lean_inc(x_181);
lean_dec(x_13);
x_182 = lean_ctor_get(x_14, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_14, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_184 = x_14;
} else {
 lean_dec_ref(x_14);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_181);
lean_ctor_set(x_12, 0, x_186);
return x_12;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_187 = lean_ctor_get(x_12, 1);
lean_inc(x_187);
lean_dec(x_12);
x_188 = lean_ctor_get(x_13, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_189 = x_13;
} else {
 lean_dec_ref(x_13);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_14, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_14, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_192 = x_14;
} else {
 lean_dec_ref(x_14);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
if (lean_is_scalar(x_189)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_189;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_188);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_187);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_12);
if (x_196 == 0)
{
return x_12;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_12, 0);
x_198 = lean_ctor_get(x_12, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_12);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
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
x_12 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__7), 9, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_8);
x_13 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16___rarg), 8, 2);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lake_Module_recBuildDeps___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lake_Module_recBuildDeps___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_Module_recBuildDeps___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lake_Module_recBuildDeps___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_Module_recBuildDeps___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lake_Module_recBuildDeps___spec__14(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__15(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Lake_Module_recBuildDeps___lambda__3(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Lake_Module_recBuildDeps___lambda__4(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Lake_Module_recBuildDeps___lambda__5(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; lean_object* x_13; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = l_Lake_Module_recBuildDeps___lambda__6(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Module_recBuildDeps(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
static lean_object* _init_l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_task_map(x_4, x_3, x_5, x_6);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_task_map(x_10, x_8, x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Module_depsFacetConfig___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("deps", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_depsFacetConfig___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_depsFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_depsFacetConfig___closed__5;
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_depsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_depsFacetConfig___closed__6;
return x_1;
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
x_9 = lean_ctor_get(x_6, 9);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_System_FilePath_join(x_8, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
lean_inc(x_11);
x_13 = l_Lean_modToFilePath(x_10, x_11, x_12);
x_14 = l_Lake_clearFileHash(x_13, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lake_Module_clearOutputHashes___closed__1;
lean_inc(x_11);
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
x_22 = l_Lake_Module_clearOutputHashes___closed__2;
lean_inc(x_11);
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
x_9 = lean_ctor_get(x_6, 9);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_System_FilePath_join(x_8, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
lean_inc(x_11);
x_13 = l_Lean_modToFilePath(x_10, x_11, x_12);
x_14 = l_Lake_cacheFileHash(x_13, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lake_Module_clearOutputHashes___closed__1;
lean_inc(x_11);
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
x_22 = l_Lake_Module_clearOutputHashes___closed__2;
lean_inc(x_11);
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
x_8 = l_instDecidableRelLt___rarg(x_7, x_2, x_6);
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
x_13 = l_instDecidableRelLt___rarg(x_12, x_2, x_10);
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
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec(x_1);
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
x_19 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_1, x_4, x_7);
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
x_27 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_1, x_4, x_7);
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
x_34 = l_Lake_Module_checkExists(x_1, x_7);
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
x_42 = l_Lake_Module_checkExists(x_1, x_7);
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
lean_dec(x_1);
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
x_60 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_1, x_4, x_7);
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
x_70 = l_Lake_Module_checkExists(x_1, x_7);
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
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lake_Workspace_leanPath(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_92 = lean_ctor_get(x_14, 1);
lean_inc(x_92);
lean_dec(x_14);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_94, 7);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
lean_inc(x_2);
x_97 = l_Lean_modToFilePath(x_1, x_2, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Lake_Module_clearOutputHashes___closed__1;
lean_inc(x_2);
x_100 = l_Lean_modToFilePath(x_1, x_2, x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_ctor_get(x_3, 12);
lean_inc(x_102);
lean_dec(x_3);
x_103 = l_System_FilePath_join(x_4, x_102);
x_104 = l_Lake_Module_clearOutputHashes___closed__2;
x_105 = l_Lean_modToFilePath(x_103, x_2, x_104);
lean_dec(x_103);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_inc(x_5);
x_107 = l_Lake_Module_bcFile_x3f(x_5);
x_108 = lean_ctor_get(x_6, 2);
lean_inc(x_108);
lean_dec(x_6);
x_109 = lean_ctor_get(x_7, 2);
x_110 = l_Array_append___rarg(x_108, x_109);
x_111 = l_Array_append___rarg(x_110, x_8);
x_112 = !lean_is_exclusive(x_15);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_15, 0);
x_114 = l_Lake_compileLeanModule(x_9, x_98, x_101, x_106, x_107, x_13, x_10, x_11, x_12, x_111, x_95, x_113, x_16);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_115, 1);
lean_ctor_set(x_15, 0, x_118);
lean_ctor_set(x_115, 1, x_15);
x_17 = x_115;
x_18 = x_116;
goto block_91;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_115);
lean_ctor_set(x_15, 0, x_120);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_15);
x_17 = x_121;
x_18 = x_116;
goto block_91;
}
}
else
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_114, 1);
lean_inc(x_122);
lean_dec(x_114);
x_123 = !lean_is_exclusive(x_115);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_115, 1);
lean_ctor_set(x_15, 0, x_124);
lean_ctor_set(x_115, 1, x_15);
x_17 = x_115;
x_18 = x_122;
goto block_91;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
lean_ctor_set(x_15, 0, x_126);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_15);
x_17 = x_127;
x_18 = x_122;
goto block_91;
}
}
}
else
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_15, 0);
x_129 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_inc(x_128);
lean_dec(x_15);
x_130 = l_Lake_compileLeanModule(x_9, x_98, x_101, x_106, x_107, x_13, x_10, x_11, x_12, x_111, x_95, x_128, x_16);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_135 = x_131;
} else {
 lean_dec_ref(x_131);
 x_135 = lean_box(0);
}
x_136 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_129);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_136);
x_17 = x_137;
x_18 = x_132;
goto block_91;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_138 = lean_ctor_get(x_130, 1);
lean_inc(x_138);
lean_dec(x_130);
x_139 = lean_ctor_get(x_131, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_131, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_141 = x_131;
} else {
 lean_dec_ref(x_131);
 x_141 = lean_box(0);
}
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_129);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_142);
x_17 = x_143;
x_18 = x_138;
goto block_91;
}
}
block_91:
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = l_Lake_Module_clearOutputHashes(x_5, x_18);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_17, 0, x_26);
lean_ctor_set(x_24, 0, x_17);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_17, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_io_error_to_string(x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_23);
x_36 = lean_array_push(x_23, x_34);
lean_ctor_set(x_20, 0, x_36);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_35);
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 0, x_17);
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
x_39 = lean_io_error_to_string(x_37);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_23);
x_43 = lean_array_push(x_23, x_41);
lean_ctor_set(x_20, 0, x_43);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_inc(x_45);
lean_dec(x_20);
x_47 = l_Lake_Module_clearOutputHashes(x_5, x_18);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
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
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_46);
lean_ctor_set(x_17, 1, x_51);
lean_ctor_set(x_17, 0, x_48);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_17);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_55 = x_47;
} else {
 lean_dec_ref(x_47);
 x_55 = lean_box(0);
}
x_56 = lean_io_error_to_string(x_53);
x_57 = 3;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = lean_array_get_size(x_45);
x_60 = lean_array_push(x_45, x_58);
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_46);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_61);
lean_ctor_set(x_17, 0, x_59);
if (lean_is_scalar(x_55)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_55;
 lean_ctor_set_tag(x_62, 0);
}
lean_ctor_set(x_62, 0, x_17);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_17, 1);
lean_inc(x_63);
lean_dec(x_17);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_63, sizeof(void*)*1);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = l_Lake_Module_clearOutputHashes(x_5, x_18);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 1, 1);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_65);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_67, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_76 = x_67;
} else {
 lean_dec_ref(x_67);
 x_76 = lean_box(0);
}
x_77 = lean_io_error_to_string(x_74);
x_78 = 3;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = lean_array_get_size(x_64);
x_81 = lean_array_push(x_64, x_79);
if (lean_is_scalar(x_66)) {
 x_82 = lean_alloc_ctor(0, 1, 1);
} else {
 x_82 = x_66;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_65);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_76)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_76;
 lean_ctor_set_tag(x_84, 0);
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_75);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_17);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_17);
lean_ctor_set(x_86, 1, x_18);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_17, 0);
x_88 = lean_ctor_get(x_17, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_17);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_18);
return x_90;
}
}
}
}
}
static lean_object* _init_l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_288; 
x_21 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__2___boxed), 16, 12);
lean_closure_set(x_21, 0, x_12);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_5);
lean_closure_set(x_21, 3, x_11);
lean_closure_set(x_21, 4, x_1);
lean_closure_set(x_21, 5, x_6);
lean_closure_set(x_21, 6, x_7);
lean_closure_set(x_21, 7, x_8);
lean_closure_set(x_21, 8, x_10);
lean_closure_set(x_21, 9, x_9);
lean_closure_set(x_21, 10, x_4);
lean_closure_set(x_21, 11, x_3);
x_22 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__1;
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
x_288 = !lean_is_exclusive(x_19);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_289 = lean_ctor_get(x_19, 0);
x_290 = l_System_FilePath_pathExists(x_15, x_20);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_unbox(x_291);
lean_dec(x_291);
if (x_292 == 0)
{
uint8_t x_293; 
lean_dec(x_17);
x_293 = !lean_is_exclusive(x_290);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_290, 1);
x_295 = lean_ctor_get(x_290, 0);
lean_dec(x_295);
x_296 = lean_ctor_get(x_14, 1);
lean_inc(x_296);
x_297 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_296, x_294);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_ctor_get(x_297, 1);
x_301 = lean_unbox(x_299);
lean_dec(x_299);
if (x_301 == 0)
{
lean_object* x_302; 
lean_free_object(x_297);
lean_free_object(x_290);
x_302 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_19, x_300);
return x_302;
}
else
{
uint8_t x_303; lean_object* x_304; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_303 = 1;
x_304 = lean_box(x_303);
lean_ctor_set(x_290, 1, x_19);
lean_ctor_set(x_290, 0, x_304);
lean_ctor_set(x_297, 0, x_290);
return x_297;
}
}
else
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_305 = lean_ctor_get(x_297, 0);
x_306 = lean_ctor_get(x_297, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_297);
x_307 = lean_unbox(x_305);
lean_dec(x_305);
if (x_307 == 0)
{
lean_object* x_308; 
lean_free_object(x_290);
x_308 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_19, x_306);
return x_308;
}
else
{
uint8_t x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_309 = 1;
x_310 = lean_box(x_309);
lean_ctor_set(x_290, 1, x_19);
lean_ctor_set(x_290, 0, x_310);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_290);
lean_ctor_set(x_311, 1, x_306);
return x_311;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_312 = lean_ctor_get(x_290, 1);
lean_inc(x_312);
lean_dec(x_290);
x_313 = lean_ctor_get(x_14, 1);
lean_inc(x_313);
x_314 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_313, x_312);
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
x_318 = lean_unbox(x_315);
lean_dec(x_315);
if (x_318 == 0)
{
lean_object* x_319; 
lean_dec(x_317);
x_319 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_19, x_316);
return x_319;
}
else
{
uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_320 = 1;
x_321 = lean_box(x_320);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_19);
if (lean_is_scalar(x_317)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_317;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_316);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_324 = lean_ctor_get(x_290, 1);
lean_inc(x_324);
lean_dec(x_290);
x_325 = l_Lake_readTraceFile_x3f(x_15, x_289, x_324);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_328 = !lean_is_exclusive(x_326);
if (x_328 == 0)
{
lean_object* x_329; 
x_329 = lean_ctor_get(x_326, 1);
lean_ctor_set(x_19, 0, x_329);
lean_ctor_set(x_326, 1, x_19);
x_24 = x_326;
x_25 = x_327;
goto block_287;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_326, 0);
x_331 = lean_ctor_get(x_326, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_326);
lean_ctor_set(x_19, 0, x_331);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_19);
x_24 = x_332;
x_25 = x_327;
goto block_287;
}
}
}
else
{
lean_object* x_333; uint8_t x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_333 = lean_ctor_get(x_19, 0);
x_334 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_inc(x_333);
lean_dec(x_19);
x_335 = l_System_FilePath_pathExists(x_15, x_20);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_unbox(x_336);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
lean_dec(x_17);
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_339 = x_335;
} else {
 lean_dec_ref(x_335);
 x_339 = lean_box(0);
}
x_340 = lean_ctor_get(x_14, 1);
lean_inc(x_340);
x_341 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_340, x_338);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_344 = x_341;
} else {
 lean_dec_ref(x_341);
 x_344 = lean_box(0);
}
x_345 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_345, 0, x_333);
lean_ctor_set_uint8(x_345, sizeof(void*)*1, x_334);
x_346 = lean_unbox(x_342);
lean_dec(x_342);
if (x_346 == 0)
{
lean_object* x_347; 
lean_dec(x_344);
lean_dec(x_339);
x_347 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_345, x_343);
return x_347;
}
else
{
uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_348 = 1;
x_349 = lean_box(x_348);
if (lean_is_scalar(x_339)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_339;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_345);
if (lean_is_scalar(x_344)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_344;
}
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_343);
return x_351;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_352 = lean_ctor_get(x_335, 1);
lean_inc(x_352);
lean_dec(x_335);
x_353 = l_Lake_readTraceFile_x3f(x_15, x_333, x_352);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_358 = x_354;
} else {
 lean_dec_ref(x_354);
 x_358 = lean_box(0);
}
x_359 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set_uint8(x_359, sizeof(void*)*1, x_334);
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_356);
lean_ctor_set(x_360, 1, x_359);
x_24 = x_360;
x_25 = x_355;
goto block_287;
}
}
block_287:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_24, 1);
x_29 = lean_ctor_get(x_24, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
lean_dec(x_30);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_17, x_25);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
if (x_31 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_free_object(x_33);
lean_dec(x_35);
lean_free_object(x_24);
x_37 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_28, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
x_40 = lean_unbox(x_38);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_free_object(x_33);
lean_free_object(x_24);
x_41 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_28, x_39);
return x_41;
}
else
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_42 = 1;
x_43 = lean_box(x_42);
lean_ctor_set(x_24, 0, x_43);
lean_ctor_set(x_33, 0, x_24);
return x_33;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
if (x_31 == 0)
{
lean_object* x_46; 
lean_dec(x_44);
lean_free_object(x_24);
x_46 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_28, x_45);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = lean_unbox(x_44);
lean_dec(x_44);
if (x_47 == 0)
{
lean_object* x_48; 
lean_free_object(x_24);
x_48 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_28, x_45);
return x_48;
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_49 = 1;
x_50 = lean_box(x_49);
lean_ctor_set(x_24, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_24);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_inc(x_52);
lean_dec(x_28);
x_54 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_17, x_25);
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
if (x_31 == 0)
{
lean_object* x_59; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_24);
x_59 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_58, x_56);
return x_59;
}
else
{
uint8_t x_60; 
x_60 = lean_unbox(x_55);
lean_dec(x_55);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_57);
lean_free_object(x_24);
x_61 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_58, x_56);
return x_61;
}
else
{
uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_62 = 1;
x_63 = lean_box(x_62);
lean_ctor_set(x_24, 1, x_58);
lean_ctor_set(x_24, 0, x_63);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_57;
}
lean_ctor_set(x_64, 0, x_24);
lean_ctor_set(x_64, 1, x_56);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_24, 1);
lean_inc(x_65);
lean_dec(x_24);
x_66 = lean_ctor_get(x_18, 0);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
lean_dec(x_66);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_65, sizeof(void*)*1);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
x_71 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_17, x_25);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
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
if (lean_is_scalar(x_70)) {
 x_75 = lean_alloc_ctor(0, 1, 1);
} else {
 x_75 = x_70;
}
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_69);
if (x_67 == 0)
{
lean_object* x_76; 
lean_dec(x_74);
lean_dec(x_72);
x_76 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_75, x_73);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = lean_unbox(x_72);
lean_dec(x_72);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_74);
x_78 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_75, x_73);
return x_78;
}
else
{
uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_79 = 1;
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
if (lean_is_scalar(x_74)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_74;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_26);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_84 = lean_ctor_get(x_26, 0);
x_85 = lean_ctor_get(x_24, 1);
lean_inc(x_85);
lean_dec(x_24);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
lean_ctor_set(x_26, 0, x_86);
lean_inc(x_14);
x_88 = l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(x_13, x_14, x_26, x_17, x_18, x_85, x_25);
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
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_159; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
x_159 = lean_unbox(x_93);
lean_dec(x_93);
if (x_159 == 0)
{
lean_object* x_160; 
lean_free_object(x_89);
lean_dec(x_91);
lean_dec(x_87);
x_160 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_94, x_90);
return x_160;
}
else
{
uint8_t x_161; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
x_161 = !lean_is_exclusive(x_94);
if (x_161 == 0)
{
uint8_t x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_162 = lean_ctor_get_uint8(x_94, sizeof(void*)*1);
x_163 = l_Lake_instOrdJobAction;
x_164 = 1;
x_165 = lean_box(x_162);
x_166 = lean_box(x_164);
x_167 = l_instDecidableRelLe___rarg(x_163, x_165, x_166);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_box(0);
lean_ctor_set(x_89, 0, x_168);
x_95 = x_89;
x_96 = x_90;
goto block_158;
}
else
{
lean_object* x_169; 
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_164);
x_169 = lean_box(0);
lean_ctor_set(x_89, 0, x_169);
x_95 = x_89;
x_96 = x_90;
goto block_158;
}
}
else
{
lean_object* x_170; uint8_t x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_170 = lean_ctor_get(x_94, 0);
x_171 = lean_ctor_get_uint8(x_94, sizeof(void*)*1);
lean_inc(x_170);
lean_dec(x_94);
x_172 = l_Lake_instOrdJobAction;
x_173 = 1;
x_174 = lean_box(x_171);
x_175 = lean_box(x_173);
x_176 = l_instDecidableRelLe___rarg(x_172, x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_177, 0, x_170);
lean_ctor_set_uint8(x_177, sizeof(void*)*1, x_171);
x_178 = lean_box(0);
lean_ctor_set(x_89, 1, x_177);
lean_ctor_set(x_89, 0, x_178);
x_95 = x_89;
x_96 = x_90;
goto block_158;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_179, 0, x_170);
lean_ctor_set_uint8(x_179, sizeof(void*)*1, x_173);
x_180 = lean_box(0);
lean_ctor_set(x_89, 1, x_179);
lean_ctor_set(x_89, 0, x_180);
x_95 = x_89;
x_96 = x_90;
goto block_158;
}
}
}
block_158:
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = lean_ctor_get(x_95, 1);
x_99 = lean_ctor_get(x_95, 0);
lean_dec(x_99);
x_100 = lean_array_get_size(x_87);
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_nat_dec_lt(x_101, x_100);
if (x_102 == 0)
{
uint8_t x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_100);
lean_dec(x_87);
lean_dec(x_18);
x_103 = 1;
x_104 = lean_box(x_103);
lean_ctor_set(x_95, 0, x_104);
if (lean_is_scalar(x_91)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_91;
}
lean_ctor_set(x_105, 0, x_95);
lean_ctor_set(x_105, 1, x_96);
return x_105;
}
else
{
uint8_t x_106; 
x_106 = lean_nat_dec_le(x_100, x_100);
if (x_106 == 0)
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_100);
lean_dec(x_87);
lean_dec(x_18);
x_107 = 1;
x_108 = lean_box(x_107);
lean_ctor_set(x_95, 0, x_108);
if (lean_is_scalar(x_91)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_91;
}
lean_ctor_set(x_109, 0, x_95);
lean_ctor_set(x_109, 1, x_96);
return x_109;
}
else
{
size_t x_110; size_t x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_free_object(x_95);
lean_dec(x_91);
x_110 = 0;
x_111 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_112 = lean_box(0);
x_113 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_87, x_110, x_111, x_112, x_18, x_98, x_96);
lean_dec(x_18);
lean_dec(x_87);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
x_118 = 1;
x_119 = lean_box(x_118);
lean_ctor_set(x_115, 0, x_119);
return x_113;
}
else
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_dec(x_115);
x_121 = 1;
x_122 = lean_box(x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
lean_ctor_set(x_113, 0, x_123);
return x_113;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_124 = lean_ctor_get(x_113, 0);
x_125 = lean_ctor_get(x_113, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_113);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = 1;
x_129 = lean_box(x_128);
if (lean_is_scalar(x_127)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_127;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_126);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_125);
return x_131;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = lean_ctor_get(x_95, 1);
lean_inc(x_132);
lean_dec(x_95);
x_133 = lean_array_get_size(x_87);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_nat_dec_lt(x_134, x_133);
if (x_135 == 0)
{
uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_133);
lean_dec(x_87);
lean_dec(x_18);
x_136 = 1;
x_137 = lean_box(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_132);
if (lean_is_scalar(x_91)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_91;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_96);
return x_139;
}
else
{
uint8_t x_140; 
x_140 = lean_nat_dec_le(x_133, x_133);
if (x_140 == 0)
{
uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_133);
lean_dec(x_87);
lean_dec(x_18);
x_141 = 1;
x_142 = lean_box(x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_132);
if (lean_is_scalar(x_91)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_91;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_96);
return x_144;
}
else
{
size_t x_145; size_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_91);
x_145 = 0;
x_146 = lean_usize_of_nat(x_133);
lean_dec(x_133);
x_147 = lean_box(0);
x_148 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_87, x_145, x_146, x_147, x_18, x_132, x_96);
lean_dec(x_18);
lean_dec(x_87);
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
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = 1;
x_155 = lean_box(x_154);
if (lean_is_scalar(x_153)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_153;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_152);
if (lean_is_scalar(x_151)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_151;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_150);
return x_157;
}
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_213; 
x_181 = lean_ctor_get(x_89, 0);
x_182 = lean_ctor_get(x_89, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_89);
x_213 = lean_unbox(x_181);
lean_dec(x_181);
if (x_213 == 0)
{
lean_object* x_214; 
lean_dec(x_91);
lean_dec(x_87);
x_214 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_182, x_90);
return x_214;
}
else
{
lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
x_215 = lean_ctor_get(x_182, 0);
lean_inc(x_215);
x_216 = lean_ctor_get_uint8(x_182, sizeof(void*)*1);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_217 = x_182;
} else {
 lean_dec_ref(x_182);
 x_217 = lean_box(0);
}
x_218 = l_Lake_instOrdJobAction;
x_219 = 1;
x_220 = lean_box(x_216);
x_221 = lean_box(x_219);
x_222 = l_instDecidableRelLe___rarg(x_218, x_220, x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
if (lean_is_scalar(x_217)) {
 x_223 = lean_alloc_ctor(0, 1, 1);
} else {
 x_223 = x_217;
}
lean_ctor_set(x_223, 0, x_215);
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_216);
x_224 = lean_box(0);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_223);
x_183 = x_225;
x_184 = x_90;
goto block_212;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
if (lean_is_scalar(x_217)) {
 x_226 = lean_alloc_ctor(0, 1, 1);
} else {
 x_226 = x_217;
}
lean_ctor_set(x_226, 0, x_215);
lean_ctor_set_uint8(x_226, sizeof(void*)*1, x_219);
x_227 = lean_box(0);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_183 = x_228;
x_184 = x_90;
goto block_212;
}
}
block_212:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = lean_array_get_size(x_87);
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_nat_dec_lt(x_188, x_187);
if (x_189 == 0)
{
uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_187);
lean_dec(x_87);
lean_dec(x_18);
x_190 = 1;
x_191 = lean_box(x_190);
if (lean_is_scalar(x_186)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_186;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_185);
if (lean_is_scalar(x_91)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_91;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_184);
return x_193;
}
else
{
uint8_t x_194; 
x_194 = lean_nat_dec_le(x_187, x_187);
if (x_194 == 0)
{
uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_187);
lean_dec(x_87);
lean_dec(x_18);
x_195 = 1;
x_196 = lean_box(x_195);
if (lean_is_scalar(x_186)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_186;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_185);
if (lean_is_scalar(x_91)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_91;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_184);
return x_198;
}
else
{
size_t x_199; size_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_186);
lean_dec(x_91);
x_199 = 0;
x_200 = lean_usize_of_nat(x_187);
lean_dec(x_187);
x_201 = lean_box(0);
x_202 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_87, x_199, x_200, x_201, x_18, x_185, x_184);
lean_dec(x_18);
lean_dec(x_87);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_207 = x_203;
} else {
 lean_dec_ref(x_203);
 x_207 = lean_box(0);
}
x_208 = 1;
x_209 = lean_box(x_208);
if (lean_is_scalar(x_207)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_207;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_206);
if (lean_is_scalar(x_205)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_205;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_204);
return x_211;
}
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_271; 
x_229 = lean_ctor_get(x_26, 0);
lean_inc(x_229);
lean_dec(x_26);
x_230 = lean_ctor_get(x_24, 1);
lean_inc(x_230);
lean_dec(x_24);
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec(x_229);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_231);
lean_inc(x_14);
x_234 = l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(x_13, x_14, x_233, x_17, x_18, x_230, x_25);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_240 = x_235;
} else {
 lean_dec_ref(x_235);
 x_240 = lean_box(0);
}
x_271 = lean_unbox(x_238);
lean_dec(x_238);
if (x_271 == 0)
{
lean_object* x_272; 
lean_dec(x_240);
lean_dec(x_237);
lean_dec(x_232);
x_272 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_239, x_236);
return x_272;
}
else
{
lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
x_273 = lean_ctor_get(x_239, 0);
lean_inc(x_273);
x_274 = lean_ctor_get_uint8(x_239, sizeof(void*)*1);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_275 = x_239;
} else {
 lean_dec_ref(x_239);
 x_275 = lean_box(0);
}
x_276 = l_Lake_instOrdJobAction;
x_277 = 1;
x_278 = lean_box(x_274);
x_279 = lean_box(x_277);
x_280 = l_instDecidableRelLe___rarg(x_276, x_278, x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
if (lean_is_scalar(x_275)) {
 x_281 = lean_alloc_ctor(0, 1, 1);
} else {
 x_281 = x_275;
}
lean_ctor_set(x_281, 0, x_273);
lean_ctor_set_uint8(x_281, sizeof(void*)*1, x_274);
x_282 = lean_box(0);
if (lean_is_scalar(x_240)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_240;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_281);
x_241 = x_283;
x_242 = x_236;
goto block_270;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
if (lean_is_scalar(x_275)) {
 x_284 = lean_alloc_ctor(0, 1, 1);
} else {
 x_284 = x_275;
}
lean_ctor_set(x_284, 0, x_273);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_277);
x_285 = lean_box(0);
if (lean_is_scalar(x_240)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_240;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_284);
x_241 = x_286;
x_242 = x_236;
goto block_270;
}
}
block_270:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_244 = x_241;
} else {
 lean_dec_ref(x_241);
 x_244 = lean_box(0);
}
x_245 = lean_array_get_size(x_232);
x_246 = lean_unsigned_to_nat(0u);
x_247 = lean_nat_dec_lt(x_246, x_245);
if (x_247 == 0)
{
uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_245);
lean_dec(x_232);
lean_dec(x_18);
x_248 = 1;
x_249 = lean_box(x_248);
if (lean_is_scalar(x_244)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_244;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_243);
if (lean_is_scalar(x_237)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_237;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_242);
return x_251;
}
else
{
uint8_t x_252; 
x_252 = lean_nat_dec_le(x_245, x_245);
if (x_252 == 0)
{
uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_245);
lean_dec(x_232);
lean_dec(x_18);
x_253 = 1;
x_254 = lean_box(x_253);
if (lean_is_scalar(x_244)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_244;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_243);
if (lean_is_scalar(x_237)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_237;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_242);
return x_256;
}
else
{
size_t x_257; size_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_244);
lean_dec(x_237);
x_257 = 0;
x_258 = lean_usize_of_nat(x_245);
lean_dec(x_245);
x_259 = lean_box(0);
x_260 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_232, x_257, x_258, x_259, x_18, x_243, x_242);
lean_dec(x_18);
lean_dec(x_232);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_263 = x_260;
} else {
 lean_dec_ref(x_260);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_265 = x_261;
} else {
 lean_dec_ref(x_261);
 x_265 = lean_box(0);
}
x_266 = 1;
x_267 = lean_box(x_266);
if (lean_is_scalar(x_265)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_265;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_264);
if (lean_is_scalar(x_263)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_263;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_262);
return x_269;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Module_recBuildLean___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Module_recBuildLean___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Module_recBuildLean___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__1() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__3;
x_3 = lean_unsigned_to_nat(92u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__1;
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
x_17 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Module_recBuildLean___spec__5), 5, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
x_18 = l_IO_withStdin___at_Lake_Module_recBuildLean___spec__6(x_15, x_17, x_3, x_4, x_14);
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
x_32 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
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
x_41 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
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
x_61 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
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
x_83 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
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
x_112 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Module_recBuildLean___spec__7), 5, 2);
lean_closure_set(x_112, 0, x_16);
lean_closure_set(x_112, 1, x_1);
x_113 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Module_recBuildLean___spec__5), 5, 2);
lean_closure_set(x_113, 0, x_16);
lean_closure_set(x_113, 1, x_112);
x_114 = l_IO_withStdin___at_Lake_Module_recBuildLean___spec__6(x_15, x_113, x_3, x_4, x_14);
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
x_128 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
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
x_137 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
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
x_157 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
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
x_179 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
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
x_218 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__1;
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
x_228 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Module_recBuildLean___spec__5), 5, 2);
lean_closure_set(x_228, 0, x_227);
lean_closure_set(x_228, 1, x_1);
x_229 = l_IO_withStdin___at_Lake_Module_recBuildLean___spec__6(x_226, x_228, x_3, x_225, x_224);
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
x_245 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
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
x_269 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Module_recBuildLean___spec__7), 5, 2);
lean_closure_set(x_269, 0, x_227);
lean_closure_set(x_269, 1, x_1);
x_270 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Module_recBuildLean___spec__5), 5, 2);
lean_closure_set(x_270, 0, x_227);
lean_closure_set(x_270, 1, x_269);
x_271 = l_IO_withStdin___at_Lake_Module_recBuildLean___spec__6(x_226, x_270, x_3, x_225, x_224);
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
x_287 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5;
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_io_error_to_string(x_16);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_6);
x_21 = lean_array_push(x_6, x_19);
lean_ctor_set(x_3, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_io_error_to_string(x_23);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_get_size(x_6);
x_29 = lean_array_push(x_6, x_27);
lean_ctor_set(x_3, 0, x_29);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_32);
lean_dec(x_3);
x_34 = l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(x_1, x_4);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_43 = x_34;
} else {
 lean_dec_ref(x_34);
 x_43 = lean_box(0);
}
x_44 = lean_io_error_to_string(x_41);
x_45 = 3;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = lean_array_get_size(x_32);
x_48 = lean_array_push(x_32, x_46);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_33);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_43)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_43;
 lean_ctor_set_tag(x_51, 0);
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
lean_inc(x_1);
lean_inc(x_14);
x_19 = l_Lake_BuildTrace_mix(x_14, x_1);
x_20 = l_Lake_BuildTrace_mix(x_2, x_19);
x_21 = l_Lake_BuildTrace_mix(x_18, x_20);
x_22 = lean_ctor_get(x_3, 8);
lean_inc(x_22);
x_23 = l_System_FilePath_join(x_4, x_22);
x_24 = lean_ctor_get(x_3, 9);
lean_inc(x_24);
lean_inc(x_23);
x_25 = l_System_FilePath_join(x_23, x_24);
x_26 = l_Lake_Module_recBuildLean___lambda__3___closed__1;
lean_inc(x_5);
x_27 = l_Lean_modToFilePath(x_25, x_5, x_26);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = 3;
lean_inc(x_15);
lean_inc_n(x_6, 2);
x_30 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(x_6, x_5, x_7, x_8, x_3, x_9, x_10, x_11, x_12, x_13, x_23, x_25, x_6, x_21, x_27, x_29, x_28, x_15, x_16, x_17);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_31, 1);
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = l_Lake_Module_cacheOutputHashes(x_6, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_free_object(x_31);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lake_Module_recBuildLean___lambda__2(x_1, x_41, x_15, x_35, x_42);
lean_dec(x_15);
lean_dec(x_41);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_io_error_to_string(x_45);
x_47 = 3;
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_49 = lean_array_get_size(x_39);
x_50 = lean_array_push(x_39, x_48);
lean_ctor_set(x_35, 0, x_50);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_49);
lean_ctor_set_tag(x_40, 0);
lean_ctor_set(x_40, 0, x_31);
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_40, 0);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_40);
x_53 = lean_io_error_to_string(x_51);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_39);
x_57 = lean_array_push(x_39, x_55);
lean_ctor_set(x_35, 0, x_57);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_31);
lean_ctor_set(x_58, 1, x_52);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_35, 0);
x_60 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_inc(x_59);
lean_dec(x_35);
x_61 = l_Lake_Module_cacheOutputHashes(x_6, x_37);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_31);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_60);
x_65 = l_Lake_Module_recBuildLean___lambda__2(x_1, x_62, x_15, x_64, x_63);
lean_dec(x_15);
lean_dec(x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_15);
lean_dec(x_1);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
x_69 = lean_io_error_to_string(x_66);
x_70 = 3;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_get_size(x_59);
x_73 = lean_array_push(x_59, x_71);
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_60);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_74);
lean_ctor_set(x_31, 0, x_72);
if (lean_is_scalar(x_68)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_68;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_31);
lean_ctor_set(x_75, 1, x_67);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_31, 1);
lean_inc(x_76);
lean_dec(x_31);
x_77 = lean_ctor_get(x_30, 1);
lean_inc(x_77);
lean_dec(x_30);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_76, sizeof(void*)*1);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_80 = x_76;
} else {
 lean_dec_ref(x_76);
 x_80 = lean_box(0);
}
x_81 = l_Lake_Module_cacheOutputHashes(x_6, x_77);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 1, 1);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_79);
x_85 = l_Lake_Module_recBuildLean___lambda__2(x_1, x_82, x_15, x_84, x_83);
lean_dec(x_15);
lean_dec(x_82);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_15);
lean_dec(x_1);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
x_89 = lean_io_error_to_string(x_86);
x_90 = 3;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_get_size(x_78);
x_93 = lean_array_push(x_78, x_91);
if (lean_is_scalar(x_80)) {
 x_94 = lean_alloc_ctor(0, 1, 1);
} else {
 x_94 = x_80;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_79);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
if (lean_is_scalar(x_88)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_88;
 lean_ctor_set_tag(x_96, 0);
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_87);
return x_96;
}
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_15, 0);
lean_inc(x_97);
x_98 = lean_ctor_get_uint8(x_97, sizeof(void*)*1 + 1);
lean_dec(x_97);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_31);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_31, 1);
x_101 = lean_ctor_get(x_31, 0);
lean_dec(x_101);
x_102 = lean_ctor_get(x_30, 1);
lean_inc(x_102);
lean_dec(x_30);
x_103 = !lean_is_exclusive(x_100);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = l_Lake_Module_cacheOutputHashes(x_6, x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_free_object(x_31);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lake_Module_recBuildLean___lambda__2(x_1, x_106, x_15, x_100, x_107);
lean_dec(x_15);
lean_dec(x_106);
return x_108;
}
else
{
uint8_t x_109; 
lean_dec(x_15);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_105);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_105, 0);
x_111 = lean_io_error_to_string(x_110);
x_112 = 3;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
x_114 = lean_array_get_size(x_104);
x_115 = lean_array_push(x_104, x_113);
lean_ctor_set(x_100, 0, x_115);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_114);
lean_ctor_set_tag(x_105, 0);
lean_ctor_set(x_105, 0, x_31);
return x_105;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_105, 0);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_105);
x_118 = lean_io_error_to_string(x_116);
x_119 = 3;
x_120 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
x_121 = lean_array_get_size(x_104);
x_122 = lean_array_push(x_104, x_120);
lean_ctor_set(x_100, 0, x_122);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_31);
lean_ctor_set(x_123, 1, x_117);
return x_123;
}
}
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_100, 0);
x_125 = lean_ctor_get_uint8(x_100, sizeof(void*)*1);
lean_inc(x_124);
lean_dec(x_100);
x_126 = l_Lake_Module_cacheOutputHashes(x_6, x_102);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_free_object(x_31);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_125);
x_130 = l_Lake_Module_recBuildLean___lambda__2(x_1, x_127, x_15, x_129, x_128);
lean_dec(x_15);
lean_dec(x_127);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_15);
lean_dec(x_1);
x_131 = lean_ctor_get(x_126, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_126, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_133 = x_126;
} else {
 lean_dec_ref(x_126);
 x_133 = lean_box(0);
}
x_134 = lean_io_error_to_string(x_131);
x_135 = 3;
x_136 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_135);
x_137 = lean_array_get_size(x_124);
x_138 = lean_array_push(x_124, x_136);
x_139 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_125);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_139);
lean_ctor_set(x_31, 0, x_137);
if (lean_is_scalar(x_133)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_133;
 lean_ctor_set_tag(x_140, 0);
}
lean_ctor_set(x_140, 0, x_31);
lean_ctor_set(x_140, 1, x_132);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_31, 1);
lean_inc(x_141);
lean_dec(x_31);
x_142 = lean_ctor_get(x_30, 1);
lean_inc(x_142);
lean_dec(x_30);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_145 = x_141;
} else {
 lean_dec_ref(x_141);
 x_145 = lean_box(0);
}
x_146 = l_Lake_Module_cacheOutputHashes(x_6, x_142);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
if (lean_is_scalar(x_145)) {
 x_149 = lean_alloc_ctor(0, 1, 1);
} else {
 x_149 = x_145;
}
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_144);
x_150 = l_Lake_Module_recBuildLean___lambda__2(x_1, x_147, x_15, x_149, x_148);
lean_dec(x_15);
lean_dec(x_147);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_15);
lean_dec(x_1);
x_151 = lean_ctor_get(x_146, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_153 = x_146;
} else {
 lean_dec_ref(x_146);
 x_153 = lean_box(0);
}
x_154 = lean_io_error_to_string(x_151);
x_155 = 3;
x_156 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_155);
x_157 = lean_array_get_size(x_143);
x_158 = lean_array_push(x_143, x_156);
if (lean_is_scalar(x_145)) {
 x_159 = lean_alloc_ctor(0, 1, 1);
} else {
 x_159 = x_145;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_144);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
if (lean_is_scalar(x_153)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_153;
 lean_ctor_set_tag(x_161, 0);
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_152);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_6);
x_162 = lean_ctor_get(x_30, 1);
lean_inc(x_162);
lean_dec(x_30);
x_163 = lean_ctor_get(x_31, 1);
lean_inc(x_163);
lean_dec(x_31);
x_164 = lean_box(0);
x_165 = l_Lake_Module_recBuildLean___lambda__2(x_1, x_164, x_15, x_163, x_162);
lean_dec(x_15);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_30);
if (x_166 == 0)
{
lean_object* x_167; uint8_t x_168; 
x_167 = lean_ctor_get(x_30, 0);
lean_dec(x_167);
x_168 = !lean_is_exclusive(x_31);
if (x_168 == 0)
{
return x_30;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_31, 0);
x_170 = lean_ctor_get(x_31, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_31);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_30, 0, x_171);
return x_30;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_172 = lean_ctor_get(x_30, 1);
lean_inc(x_172);
lean_dec(x_30);
x_173 = lean_ctor_get(x_31, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_31, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_175 = x_31;
} else {
 lean_dec_ref(x_31);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_172);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_30);
if (x_178 == 0)
{
return x_30;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_30, 0);
x_180 = lean_ctor_get(x_30, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_30);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Lake_Module_recBuildLean___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_19, x_20, x_17);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
x_23 = l_Array_append___rarg(x_21, x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_array_get_size(x_26);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_28, x_20, x_26);
x_30 = l_Array_append___rarg(x_23, x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
x_32 = l_Array_append___rarg(x_30, x_31);
lean_dec(x_31);
x_33 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_32);
x_34 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
x_35 = lean_box_uint64(x_33);
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_35);
x_36 = lean_ctor_get(x_14, 0);
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_ctor_get(x_15, 7);
lean_inc(x_37);
lean_inc(x_36);
x_38 = l_System_FilePath_join(x_36, x_37);
x_39 = lean_ctor_get(x_24, 2);
lean_inc(x_39);
lean_dec(x_24);
x_40 = l_System_FilePath_join(x_38, x_39);
x_41 = l_Lake_Module_recParseImports___closed__1;
lean_inc(x_2);
x_42 = l_Lean_modToFilePath(x_40, x_2, x_41);
lean_inc(x_42);
x_43 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__1___boxed), 4, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__3___boxed), 17, 13);
lean_closure_set(x_44, 0, x_9);
lean_closure_set(x_44, 1, x_7);
lean_closure_set(x_44, 2, x_15);
lean_closure_set(x_44, 3, x_36);
lean_closure_set(x_44, 4, x_2);
lean_closure_set(x_44, 5, x_1);
lean_closure_set(x_44, 6, x_11);
lean_closure_set(x_44, 7, x_12);
lean_closure_set(x_44, 8, x_16);
lean_closure_set(x_44, 9, x_25);
lean_closure_set(x_44, 10, x_32);
lean_closure_set(x_44, 11, x_40);
lean_closure_set(x_44, 12, x_42);
x_45 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_45, 0, x_43);
lean_closure_set(x_45, 1, x_44);
x_46 = 1;
lean_inc(x_3);
x_47 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4(x_45, x_46, x_3, x_8, x_5);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
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
x_54 = l_String_isEmpty(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; 
x_55 = l_Lake_Module_recBuildLean___lambda__5___closed__1;
x_56 = lean_string_append(x_55, x_52);
lean_dec(x_52);
x_57 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = 1;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = !lean_is_exclusive(x_51);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_array_push(x_62, x_60);
lean_ctor_set(x_51, 0, x_63);
x_64 = lean_box(0);
x_65 = l_Lake_Module_recBuildLean___lambda__4(x_53, x_64, x_3, x_51, x_50);
lean_dec(x_3);
return x_65;
}
else
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_51, 0);
x_67 = lean_ctor_get_uint8(x_51, sizeof(void*)*1);
lean_inc(x_66);
lean_dec(x_51);
x_68 = lean_array_push(x_66, x_60);
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_67);
x_70 = lean_box(0);
x_71 = l_Lake_Module_recBuildLean___lambda__4(x_53, x_70, x_3, x_69, x_50);
lean_dec(x_3);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_52);
x_72 = lean_box(0);
x_73 = l_Lake_Module_recBuildLean___lambda__4(x_53, x_72, x_3, x_51, x_50);
lean_dec(x_3);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_47);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_47, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_48);
if (x_76 == 0)
{
return x_47;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_48, 0);
x_78 = lean_ctor_get(x_48, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_48);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_47, 0, x_79);
return x_47;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_47, 1);
lean_inc(x_80);
lean_dec(x_47);
x_81 = lean_ctor_get(x_48, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_83 = x_48;
} else {
 lean_dec_ref(x_48);
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
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_47);
if (x_86 == 0)
{
return x_47;
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
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint64_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; 
x_90 = lean_ctor_get(x_7, 0);
x_91 = lean_ctor_get(x_7, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_7);
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_array_get_size(x_96);
x_98 = lean_usize_of_nat(x_97);
lean_dec(x_97);
x_99 = 0;
x_100 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_98, x_99, x_96);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
x_102 = l_Array_append___rarg(x_100, x_101);
lean_dec(x_101);
x_103 = lean_ctor_get(x_92, 1);
lean_inc(x_103);
lean_dec(x_92);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_array_get_size(x_105);
x_107 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_108 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_107, x_99, x_105);
x_109 = l_Array_append___rarg(x_102, x_108);
lean_dec(x_108);
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
x_111 = l_Array_append___rarg(x_109, x_110);
lean_dec(x_110);
x_112 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_111);
x_113 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
x_114 = lean_box_uint64(x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_ctor_get(x_93, 0);
lean_inc(x_116);
lean_dec(x_93);
x_117 = lean_ctor_get(x_94, 7);
lean_inc(x_117);
lean_inc(x_116);
x_118 = l_System_FilePath_join(x_116, x_117);
x_119 = lean_ctor_get(x_103, 2);
lean_inc(x_119);
lean_dec(x_103);
x_120 = l_System_FilePath_join(x_118, x_119);
x_121 = l_Lake_Module_recParseImports___closed__1;
lean_inc(x_2);
x_122 = l_Lean_modToFilePath(x_120, x_2, x_121);
lean_inc(x_122);
x_123 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__1___boxed), 4, 1);
lean_closure_set(x_123, 0, x_122);
x_124 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__3___boxed), 17, 13);
lean_closure_set(x_124, 0, x_9);
lean_closure_set(x_124, 1, x_115);
lean_closure_set(x_124, 2, x_94);
lean_closure_set(x_124, 3, x_116);
lean_closure_set(x_124, 4, x_2);
lean_closure_set(x_124, 5, x_1);
lean_closure_set(x_124, 6, x_90);
lean_closure_set(x_124, 7, x_91);
lean_closure_set(x_124, 8, x_95);
lean_closure_set(x_124, 9, x_104);
lean_closure_set(x_124, 10, x_111);
lean_closure_set(x_124, 11, x_120);
lean_closure_set(x_124, 12, x_122);
x_125 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_125, 0, x_123);
lean_closure_set(x_125, 1, x_124);
x_126 = 1;
lean_inc(x_3);
x_127 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4(x_125, x_126, x_3, x_8, x_5);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_dec(x_129);
x_134 = l_String_isEmpty(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_135 = l_Lake_Module_recBuildLean___lambda__5___closed__1;
x_136 = lean_string_append(x_135, x_132);
lean_dec(x_132);
x_137 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_138 = lean_string_append(x_136, x_137);
x_139 = 1;
x_140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_139);
x_141 = lean_ctor_get(x_131, 0);
lean_inc(x_141);
x_142 = lean_ctor_get_uint8(x_131, sizeof(void*)*1);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_143 = x_131;
} else {
 lean_dec_ref(x_131);
 x_143 = lean_box(0);
}
x_144 = lean_array_push(x_141, x_140);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 1, 1);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_142);
x_146 = lean_box(0);
x_147 = l_Lake_Module_recBuildLean___lambda__4(x_133, x_146, x_3, x_145, x_130);
lean_dec(x_3);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_132);
x_148 = lean_box(0);
x_149 = l_Lake_Module_recBuildLean___lambda__4(x_133, x_148, x_3, x_131, x_130);
lean_dec(x_3);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_3);
x_150 = lean_ctor_get(x_127, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_151 = x_127;
} else {
 lean_dec_ref(x_127);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_128, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_128, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_154 = x_128;
} else {
 lean_dec_ref(x_128);
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
lean_dec(x_3);
x_157 = lean_ctor_get(x_127, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_127, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_159 = x_127;
} else {
 lean_dec_ref(x_127);
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
else
{
uint8_t x_161; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_4);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_4);
lean_ctor_set(x_162, 1, x_5);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_4, 0);
x_164 = lean_ctor_get(x_4, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_4);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_5);
return x_166;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__5), 5, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_6);
x_14 = l_Task_Priority_default;
x_15 = 0;
x_16 = lean_io_map_task(x_13, x_11, x_14, x_15, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_3, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
lean_ctor_set(x_3, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_3);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_32 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__5), 5, 3);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_2);
lean_closure_set(x_32, 2, x_6);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = lean_io_map_task(x_32, x_30, x_33, x_34, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_8);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_45 = x_35;
} else {
 lean_dec_ref(x_35);
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = l_Lake_Module_depsFacetConfig___closed__4;
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, lean_box(0));
x_14 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__6___boxed), 9, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_8);
x_15 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16___rarg), 8, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lake_withRegisterJob___rarg(x_10, x_15, x_2, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_17;
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
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_16);
lean_dec(x_16);
x_22 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21, x_17, x_18, x_19, x_20);
return x_22;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Module_recBuildLean___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Module_recBuildLean___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__3___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Lake_Module_recBuildLean___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Module_recBuildLean___lambda__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Module_recBuildLean___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Module_recBuildLean(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_leanArtsFacetConfig___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_task_map(x_4, x_3, x_5, x_6);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_task_map(x_10, x_8, x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Module_leanArtsFacetConfig___spec__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Module_leanArtsFacetConfig___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanArts", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_leanArtsFacetConfig___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_leanArtsFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_leanArtsFacetConfig___closed__5;
x_2 = l_Lake_Module_leanArtsFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_leanArtsFacetConfig___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lake_BuildTrace_mix(x_3, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 8);
lean_inc(x_12);
x_13 = l_System_FilePath_join(x_10, x_12);
x_14 = lean_ctor_get(x_11, 9);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_System_FilePath_join(x_13, x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
x_18 = l_Lean_modToFilePath(x_15, x_16, x_17);
lean_dec(x_15);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lake_fetchFileTrace___boxed), 4, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed), 6, 2);
lean_closure_set(x_20, 0, x_7);
lean_closure_set(x_20, 1, x_18);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = 1;
lean_inc(x_2);
x_23 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_21, x_22, x_2, x_6, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_String_isEmpty(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; 
x_31 = l_Lake_Module_recBuildLean___lambda__5___closed__1;
x_32 = lean_string_append(x_31, x_28);
lean_dec(x_28);
x_33 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = 1;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_array_push(x_38, x_36);
lean_ctor_set(x_27, 0, x_39);
x_40 = lean_box(0);
x_41 = l_Lake_Module_recBuildLean___lambda__4(x_29, x_40, x_2, x_27, x_26);
lean_dec(x_2);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
lean_inc(x_42);
lean_dec(x_27);
x_44 = lean_array_push(x_42, x_36);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_43);
x_46 = lean_box(0);
x_47 = l_Lake_Module_recBuildLean___lambda__4(x_29, x_46, x_2, x_45, x_26);
lean_dec(x_2);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_28);
x_48 = lean_box(0);
x_49 = l_Lake_Module_recBuildLean___lambda__4(x_29, x_48, x_2, x_27, x_26);
lean_dec(x_2);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_23, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
return x_23;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_24, 0);
x_54 = lean_ctor_get(x_24, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_24);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_23, 0, x_55);
return x_23;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_23, 1);
lean_inc(x_56);
lean_dec(x_23);
x_57 = lean_ctor_get(x_24, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_24, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_59 = x_24;
} else {
 lean_dec_ref(x_24);
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
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_23);
if (x_62 == 0)
{
return x_23;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_23, 0);
x_64 = lean_ctor_get(x_23, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_23);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_3);
lean_ctor_set(x_67, 1, x_4);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_3, 0);
x_69 = lean_ctor_get(x_3, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_3);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_4);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__4;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_4);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
x_24 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__2), 4, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_4);
x_25 = l_Task_Priority_default;
x_26 = 0;
x_27 = lean_io_map_task(x_24, x_22, x_25, x_26, x_14);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_13, 0, x_29);
lean_ctor_set(x_27, 0, x_11);
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
lean_ctor_set(x_13, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_13);
lean_dec(x_23);
lean_free_object(x_12);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_16);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__2), 4, 2);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_4);
x_40 = l_Task_Priority_default;
x_41 = 0;
x_42 = lean_io_map_task(x_39, x_37, x_40, x_41, x_14);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
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
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_12, 0, x_46);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_16);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_55 = x_13;
} else {
 lean_dec_ref(x_13);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__2), 4, 2);
lean_closure_set(x_56, 0, x_1);
lean_closure_set(x_56, 1, x_4);
x_57 = l_Task_Priority_default;
x_58 = 0;
x_59 = lean_io_map_task(x_56, x_53, x_57, x_58, x_14);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
if (lean_is_scalar(x_55)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_55;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_54);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_52);
lean_ctor_set(x_11, 0, x_64);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_11);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_11);
lean_dec(x_16);
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
lean_dec(x_11);
x_71 = lean_ctor_get(x_12, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_72 = x_12;
} else {
 lean_dec_ref(x_12);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_13, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_75 = x_13;
} else {
 lean_dec_ref(x_13);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__2), 4, 2);
lean_closure_set(x_76, 0, x_1);
lean_closure_set(x_76, 1, x_4);
x_77 = l_Task_Priority_default;
x_78 = 0;
x_79 = lean_io_map_task(x_76, x_73, x_77, x_78, x_14);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
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
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_75;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_74);
if (lean_is_scalar(x_72)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_72;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_71);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_70);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
x_87 = lean_ctor_get(x_79, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_89 = x_79;
} else {
 lean_dec_ref(x_79);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_4);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_10);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_10, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_11);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_11, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_12);
if (x_95 == 0)
{
return x_10;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_12, 0);
x_97 = lean_ctor_get(x_12, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_12);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_11, 0, x_98);
return x_10;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_11, 1);
lean_inc(x_99);
lean_dec(x_11);
x_100 = lean_ctor_get(x_12, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_12, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_102 = x_12;
} else {
 lean_dec_ref(x_12);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_99);
lean_ctor_set(x_10, 0, x_104);
return x_10;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_10, 1);
lean_inc(x_105);
lean_dec(x_10);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_107 = x_11;
} else {
 lean_dec_ref(x_11);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_12, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_12, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_110 = x_12;
} else {
 lean_dec_ref(x_12);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_106);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_105);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_4);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_10);
if (x_114 == 0)
{
return x_10;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_10, 0);
x_116 = lean_ctor_get(x_10, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_10);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_oleanFacetConfig___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_task_map(x_4, x_3, x_5, x_6);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_task_map(x_10, x_8, x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
static lean_object* _init_l_Lake_Module_oleanFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Module_oleanFacetConfig___spec__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oleanFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Module_oleanFacetConfig___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_oleanFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oleanFacetConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_oleanFacetConfig___closed__3;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oleanFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_oleanFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 8);
lean_inc(x_12);
x_13 = l_System_FilePath_join(x_10, x_12);
x_14 = lean_ctor_get(x_11, 9);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_System_FilePath_join(x_13, x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lake_Module_clearOutputHashes___closed__1;
x_18 = l_Lean_modToFilePath(x_15, x_16, x_17);
lean_dec(x_15);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lake_fetchFileTrace___boxed), 4, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed), 6, 2);
lean_closure_set(x_20, 0, x_7);
lean_closure_set(x_20, 1, x_18);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = 1;
lean_inc(x_2);
x_23 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_21, x_22, x_2, x_6, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_String_isEmpty(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; 
x_31 = l_Lake_Module_recBuildLean___lambda__5___closed__1;
x_32 = lean_string_append(x_31, x_28);
lean_dec(x_28);
x_33 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = 1;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_array_push(x_38, x_36);
lean_ctor_set(x_27, 0, x_39);
x_40 = lean_box(0);
x_41 = l_Lake_Module_recBuildLean___lambda__4(x_29, x_40, x_2, x_27, x_26);
lean_dec(x_2);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
lean_inc(x_42);
lean_dec(x_27);
x_44 = lean_array_push(x_42, x_36);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_43);
x_46 = lean_box(0);
x_47 = l_Lake_Module_recBuildLean___lambda__4(x_29, x_46, x_2, x_45, x_26);
lean_dec(x_2);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_28);
x_48 = lean_box(0);
x_49 = l_Lake_Module_recBuildLean___lambda__4(x_29, x_48, x_2, x_27, x_26);
lean_dec(x_2);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_23, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
return x_23;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_24, 0);
x_54 = lean_ctor_get(x_24, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_24);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_23, 0, x_55);
return x_23;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_23, 1);
lean_inc(x_56);
lean_dec(x_23);
x_57 = lean_ctor_get(x_24, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_24, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_59 = x_24;
} else {
 lean_dec_ref(x_24);
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
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_23);
if (x_62 == 0)
{
return x_23;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_23, 0);
x_64 = lean_ctor_get(x_23, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_23);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_3);
lean_ctor_set(x_67, 1, x_4);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_3, 0);
x_69 = lean_ctor_get(x_3, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_3);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_4);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__4;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_4);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
x_24 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1), 4, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_4);
x_25 = l_Task_Priority_default;
x_26 = 0;
x_27 = lean_io_map_task(x_24, x_22, x_25, x_26, x_14);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_13, 0, x_29);
lean_ctor_set(x_27, 0, x_11);
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
lean_ctor_set(x_13, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_13);
lean_dec(x_23);
lean_free_object(x_12);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_16);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1), 4, 2);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_4);
x_40 = l_Task_Priority_default;
x_41 = 0;
x_42 = lean_io_map_task(x_39, x_37, x_40, x_41, x_14);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
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
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_12, 0, x_46);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_16);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_55 = x_13;
} else {
 lean_dec_ref(x_13);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1), 4, 2);
lean_closure_set(x_56, 0, x_1);
lean_closure_set(x_56, 1, x_4);
x_57 = l_Task_Priority_default;
x_58 = 0;
x_59 = lean_io_map_task(x_56, x_53, x_57, x_58, x_14);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
if (lean_is_scalar(x_55)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_55;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_54);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_52);
lean_ctor_set(x_11, 0, x_64);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_11);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_11);
lean_dec(x_16);
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
lean_dec(x_11);
x_71 = lean_ctor_get(x_12, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_72 = x_12;
} else {
 lean_dec_ref(x_12);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_13, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_75 = x_13;
} else {
 lean_dec_ref(x_13);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1), 4, 2);
lean_closure_set(x_76, 0, x_1);
lean_closure_set(x_76, 1, x_4);
x_77 = l_Task_Priority_default;
x_78 = 0;
x_79 = lean_io_map_task(x_76, x_73, x_77, x_78, x_14);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
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
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_75;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_74);
if (lean_is_scalar(x_72)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_72;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_71);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_70);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
x_87 = lean_ctor_get(x_79, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_89 = x_79;
} else {
 lean_dec_ref(x_79);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_4);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_10);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_10, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_11);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_11, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_12);
if (x_95 == 0)
{
return x_10;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_12, 0);
x_97 = lean_ctor_get(x_12, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_12);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_11, 0, x_98);
return x_10;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_11, 1);
lean_inc(x_99);
lean_dec(x_11);
x_100 = lean_ctor_get(x_12, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_12, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_102 = x_12;
} else {
 lean_dec_ref(x_12);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_99);
lean_ctor_set(x_10, 0, x_104);
return x_10;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_10, 1);
lean_inc(x_105);
lean_dec(x_10);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_107 = x_11;
} else {
 lean_dec_ref(x_11);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_12, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_12, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_110 = x_12;
} else {
 lean_dec_ref(x_12);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_106);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_105);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_4);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_10);
if (x_114 == 0)
{
return x_10;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_10, 0);
x_116 = lean_ctor_get(x_10, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_10);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_ileanFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_ileanFacetConfig___closed__2;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_ileanFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_ileanFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 8);
lean_inc(x_10);
x_11 = l_System_FilePath_join(x_8, x_10);
x_12 = lean_ctor_get(x_9, 12);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_System_FilePath_join(x_11, x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_Module_clearOutputHashes___closed__2;
x_16 = l_Lean_modToFilePath(x_13, x_14, x_15);
lean_dec(x_13);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lake_fetchFileTrace___boxed), 4, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed), 5, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = 1;
lean_inc(x_2);
x_21 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_19, x_20, x_2, x_5, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_String_isEmpty(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; 
x_29 = l_Lake_Module_recBuildLean___lambda__5___closed__1;
x_30 = lean_string_append(x_29, x_26);
lean_dec(x_26);
x_31 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_array_push(x_36, x_34);
lean_ctor_set(x_25, 0, x_37);
x_38 = lean_box(0);
x_39 = l_Lake_Module_recBuildLean___lambda__4(x_27, x_38, x_2, x_25, x_24);
lean_dec(x_2);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_25, 0);
x_41 = lean_ctor_get_uint8(x_25, sizeof(void*)*1);
lean_inc(x_40);
lean_dec(x_25);
x_42 = lean_array_push(x_40, x_34);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_41);
x_44 = lean_box(0);
x_45 = l_Lake_Module_recBuildLean___lambda__4(x_27, x_44, x_2, x_43, x_24);
lean_dec(x_2);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_26);
x_46 = lean_box(0);
x_47 = l_Lake_Module_recBuildLean___lambda__4(x_27, x_46, x_2, x_25, x_24);
lean_dec(x_2);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_21, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_22);
if (x_50 == 0)
{
return x_21;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_22, 0);
x_52 = lean_ctor_get(x_22, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_22);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_21, 0, x_53);
return x_21;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_dec(x_21);
x_55 = lean_ctor_get(x_22, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_57 = x_22;
} else {
 lean_dec_ref(x_22);
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
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
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
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_3);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_3);
lean_ctor_set(x_65, 1, x_4);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_3);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_4);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__4;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_4);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
x_24 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__2), 4, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_4);
x_25 = l_Task_Priority_default;
x_26 = 0;
x_27 = lean_io_map_task(x_24, x_22, x_25, x_26, x_14);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_13, 0, x_29);
lean_ctor_set(x_27, 0, x_11);
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
lean_ctor_set(x_13, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_13);
lean_dec(x_23);
lean_free_object(x_12);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_16);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__2), 4, 2);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_4);
x_40 = l_Task_Priority_default;
x_41 = 0;
x_42 = lean_io_map_task(x_39, x_37, x_40, x_41, x_14);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
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
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_12, 0, x_46);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_16);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_55 = x_13;
} else {
 lean_dec_ref(x_13);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__2), 4, 2);
lean_closure_set(x_56, 0, x_1);
lean_closure_set(x_56, 1, x_4);
x_57 = l_Task_Priority_default;
x_58 = 0;
x_59 = lean_io_map_task(x_56, x_53, x_57, x_58, x_14);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
if (lean_is_scalar(x_55)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_55;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_54);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_52);
lean_ctor_set(x_11, 0, x_64);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_11);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_11);
lean_dec(x_16);
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
lean_dec(x_11);
x_71 = lean_ctor_get(x_12, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_72 = x_12;
} else {
 lean_dec_ref(x_12);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_13, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_75 = x_13;
} else {
 lean_dec_ref(x_13);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__2), 4, 2);
lean_closure_set(x_76, 0, x_1);
lean_closure_set(x_76, 1, x_4);
x_77 = l_Task_Priority_default;
x_78 = 0;
x_79 = lean_io_map_task(x_76, x_73, x_77, x_78, x_14);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
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
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_75;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_74);
if (lean_is_scalar(x_72)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_72;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_71);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_70);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
x_87 = lean_ctor_get(x_79, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_89 = x_79;
} else {
 lean_dec_ref(x_79);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_4);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_10);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_10, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_11);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_11, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_12);
if (x_95 == 0)
{
return x_10;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_12, 0);
x_97 = lean_ctor_get(x_12, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_12);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_11, 0, x_98);
return x_10;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_11, 1);
lean_inc(x_99);
lean_dec(x_11);
x_100 = lean_ctor_get(x_12, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_12, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_102 = x_12;
} else {
 lean_dec_ref(x_12);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_99);
lean_ctor_set(x_10, 0, x_104);
return x_10;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_10, 1);
lean_inc(x_105);
lean_dec(x_10);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_107 = x_11;
} else {
 lean_dec_ref(x_11);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_12, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_12, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_110 = x_12;
} else {
 lean_dec_ref(x_12);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_106);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_105);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_4);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_10);
if (x_114 == 0)
{
return x_10;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_10, 0);
x_116 = lean_ctor_get(x_10, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_10);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_cFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_cFacetConfig___closed__2;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_cFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_cFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Module_cFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 8);
lean_inc(x_10);
x_11 = l_System_FilePath_join(x_8, x_10);
x_12 = lean_ctor_get(x_9, 12);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_System_FilePath_join(x_11, x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_Module_clearOutputHashes___closed__4;
x_16 = l_Lean_modToFilePath(x_13, x_14, x_15);
lean_dec(x_13);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lake_fetchFileTrace___boxed), 4, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed), 5, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = 1;
lean_inc(x_2);
x_21 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_19, x_20, x_2, x_5, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_String_isEmpty(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; 
x_29 = l_Lake_Module_recBuildLean___lambda__5___closed__1;
x_30 = lean_string_append(x_29, x_26);
lean_dec(x_26);
x_31 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_array_push(x_36, x_34);
lean_ctor_set(x_25, 0, x_37);
x_38 = lean_box(0);
x_39 = l_Lake_Module_recBuildLean___lambda__4(x_27, x_38, x_2, x_25, x_24);
lean_dec(x_2);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_25, 0);
x_41 = lean_ctor_get_uint8(x_25, sizeof(void*)*1);
lean_inc(x_40);
lean_dec(x_25);
x_42 = lean_array_push(x_40, x_34);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_41);
x_44 = lean_box(0);
x_45 = l_Lake_Module_recBuildLean___lambda__4(x_27, x_44, x_2, x_43, x_24);
lean_dec(x_2);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_26);
x_46 = lean_box(0);
x_47 = l_Lake_Module_recBuildLean___lambda__4(x_27, x_46, x_2, x_25, x_24);
lean_dec(x_2);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_21, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_22);
if (x_50 == 0)
{
return x_21;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_22, 0);
x_52 = lean_ctor_get(x_22, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_22);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_21, 0, x_53);
return x_21;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_dec(x_21);
x_55 = lean_ctor_get(x_22, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_57 = x_22;
} else {
 lean_dec_ref(x_22);
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
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
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
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_3);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_3);
lean_ctor_set(x_65, 1, x_4);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_3);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_4);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__4;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_4);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
x_24 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1___lambda__1), 4, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_4);
x_25 = l_Task_Priority_default;
x_26 = 0;
x_27 = lean_io_map_task(x_24, x_22, x_25, x_26, x_14);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_13, 0, x_29);
lean_ctor_set(x_27, 0, x_11);
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
lean_ctor_set(x_13, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_13);
lean_dec(x_23);
lean_free_object(x_12);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_16);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1___lambda__1), 4, 2);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_4);
x_40 = l_Task_Priority_default;
x_41 = 0;
x_42 = lean_io_map_task(x_39, x_37, x_40, x_41, x_14);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
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
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_12, 0, x_46);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_16);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_55 = x_13;
} else {
 lean_dec_ref(x_13);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1___lambda__1), 4, 2);
lean_closure_set(x_56, 0, x_1);
lean_closure_set(x_56, 1, x_4);
x_57 = l_Task_Priority_default;
x_58 = 0;
x_59 = lean_io_map_task(x_56, x_53, x_57, x_58, x_14);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
if (lean_is_scalar(x_55)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_55;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_54);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_52);
lean_ctor_set(x_11, 0, x_64);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_11);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_free_object(x_11);
lean_dec(x_16);
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
lean_dec(x_11);
x_71 = lean_ctor_get(x_12, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_72 = x_12;
} else {
 lean_dec_ref(x_12);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_13, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_75 = x_13;
} else {
 lean_dec_ref(x_13);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1___lambda__1), 4, 2);
lean_closure_set(x_76, 0, x_1);
lean_closure_set(x_76, 1, x_4);
x_77 = l_Task_Priority_default;
x_78 = 0;
x_79 = lean_io_map_task(x_76, x_73, x_77, x_78, x_14);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
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
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_75;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_74);
if (lean_is_scalar(x_72)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_72;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_71);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_70);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
x_87 = lean_ctor_get(x_79, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_89 = x_79;
} else {
 lean_dec_ref(x_79);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_4);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_10);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_10, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_11);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_11, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_12);
if (x_95 == 0)
{
return x_10;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_12, 0);
x_97 = lean_ctor_get(x_12, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_12);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_11, 0, x_98);
return x_10;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_11, 1);
lean_inc(x_99);
lean_dec(x_11);
x_100 = lean_ctor_get(x_12, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_12, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_102 = x_12;
} else {
 lean_dec_ref(x_12);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_99);
lean_ctor_set(x_10, 0, x_104);
return x_10;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_10, 1);
lean_inc(x_105);
lean_dec(x_10);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_107 = x_11;
} else {
 lean_dec_ref(x_11);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_12, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_12, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_110 = x_12;
} else {
 lean_dec_ref(x_12);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_106);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_105);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_4);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_10);
if (x_114 == 0)
{
return x_10;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_10, 0);
x_116 = lean_ctor_get(x_10, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_10);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_bcFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_bcFacetConfig___closed__2;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_bcFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_bcFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_1);
x_7 = l_Lake_platformTrace;
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__3___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lake_BuildTrace_mix(x_1, x_6);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__4___boxed), 8, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l_Lake_Module_recBuildLeanCToOExport___lambda__5___closed__1;
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__5), 9, 5);
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
x_23 = l_Lake_Module_recBuildLean___lambda__5___closed__1;
x_24 = lean_string_append(x_23, x_20);
lean_dec(x_20);
x_25 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
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
x_33 = l_Lake_Module_recBuildLean___lambda__4(x_21, x_32, x_5, x_19, x_18);
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
x_39 = l_Lake_Module_recBuildLean___lambda__4(x_21, x_38, x_5, x_37, x_18);
lean_dec(x_5);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_20);
x_40 = lean_box(0);
x_41 = l_Lake_Module_recBuildLean___lambda__4(x_21, x_40, x_5, x_19, x_18);
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
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c.o.export", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 8);
lean_inc(x_15);
x_16 = l_System_FilePath_join(x_14, x_15);
x_17 = lean_ctor_get(x_2, 12);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_System_FilePath_join(x_16, x_17);
x_19 = l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__1;
x_20 = l_Lean_modToFilePath(x_18, x_3, x_19);
lean_dec(x_18);
x_21 = lean_ctor_get(x_4, 5);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_ctor_get(x_5, 5);
x_23 = l_Array_append___rarg(x_21, x_22);
lean_inc(x_6);
x_24 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__2___boxed), 5, 1);
lean_closure_set(x_24, 0, x_6);
x_25 = l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__2;
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_24);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
x_30 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__6), 7, 5);
lean_closure_set(x_30, 0, x_23);
lean_closure_set(x_30, 1, x_6);
lean_closure_set(x_30, 2, x_20);
lean_closure_set(x_30, 3, x_26);
lean_closure_set(x_30, 4, x_10);
x_31 = l_Task_Priority_default;
x_32 = 0;
x_33 = lean_io_map_task(x_30, x_28, x_31, x_32, x_13);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_7, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_11);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_12);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
lean_ctor_set(x_7, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_11);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_12);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_7);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_49 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__6), 7, 5);
lean_closure_set(x_49, 0, x_23);
lean_closure_set(x_49, 1, x_6);
lean_closure_set(x_49, 2, x_20);
lean_closure_set(x_49, 3, x_26);
lean_closure_set(x_49, 4, x_10);
x_50 = l_Task_Priority_default;
x_51 = 0;
x_52 = lean_io_map_task(x_49, x_47, x_50, x_51, x_13);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
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
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_48);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_11);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_12);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_11);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_62 = x_52;
} else {
 lean_dec_ref(x_52);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-DLEAN_EXPORTING", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_recBuildLeanCToOExport___closed__2;
x_2 = l_Lake_Module_recBuildLeanCToOExport___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
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
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
lean_dec(x_8);
x_10 = 2;
x_11 = l_Lake_instDecidableEqVerbosity(x_9, x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = 1;
lean_inc(x_12);
x_14 = l_Lean_Name_toString(x_12, x_13);
x_15 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lake_Module_recBuildLeanCToOExport___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*9);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*9);
x_27 = l_Lake_instOrdBuildType;
x_28 = lean_box(x_23);
x_29 = lean_box(x_26);
x_30 = l_instDecidableRelLe___rarg(x_27, x_28, x_29);
x_31 = lean_ctor_get(x_22, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 3);
lean_inc(x_32);
x_33 = l_Lake_Module_cFacetConfig___closed__1;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, lean_box(0));
if (x_11 == 0)
{
x_36 = x_15;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = l_Lake_Module_recBuildLeanCToOExport___closed__5;
x_36 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_string_append(x_18, x_36);
lean_dec(x_36);
x_38 = lean_string_append(x_37, x_15);
if (x_30 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lake_BuildType_leancArgs(x_26);
x_47 = l_Array_append___rarg(x_46, x_31);
lean_dec(x_31);
x_48 = l_Array_append___rarg(x_47, x_32);
lean_dec(x_32);
x_39 = x_48;
goto block_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_Lake_BuildType_leancArgs(x_23);
x_50 = l_Array_append___rarg(x_49, x_31);
lean_dec(x_31);
x_51 = l_Array_append___rarg(x_50, x_32);
lean_dec(x_32);
x_39 = x_51;
goto block_45;
}
block_45:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Lake_Module_recBuildLeanCToOExport___closed__4;
x_41 = l_Array_append___rarg(x_39, x_40);
x_42 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__7___boxed), 13, 6);
lean_closure_set(x_42, 0, x_20);
lean_closure_set(x_42, 1, x_21);
lean_closure_set(x_42, 2, x_12);
lean_closure_set(x_42, 3, x_22);
lean_closure_set(x_42, 4, x_25);
lean_closure_set(x_42, 5, x_41);
x_43 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16___rarg), 8, 2);
lean_closure_set(x_43, 0, x_35);
lean_closure_set(x_43, 1, x_42);
x_44 = l_Lake_withRegisterJob___rarg(x_38, x_43, x_2, x_3, x_4, x_5, x_6, x_7);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Module_recBuildLeanCToOExport___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Module_recBuildLeanCToOExport___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Module_recBuildLeanCToOExport___lambda__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Module_recBuildLeanCToOExport___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_Module_recBuildLeanCToOExport___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
return x_14;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_coExportFacetConfig___closed__4;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_coExportFacetConfig___closed__5;
return x_1;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_16 = lean_ctor_get(x_13, 12);
lean_inc(x_16);
x_17 = l_System_FilePath_join(x_15, x_16);
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
x_26 = lean_ctor_get_uint8(x_20, sizeof(void*)*9);
x_27 = lean_ctor_get_uint8(x_23, sizeof(void*)*9);
x_28 = l_Lake_instOrdBuildType;
x_29 = lean_box(x_26);
x_30 = lean_box(x_27);
x_31 = l_instDecidableRelLe___rarg(x_28, x_29, x_30);
x_32 = lean_ctor_get(x_20, 3);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_23, 3);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
if (x_31 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = l_Lake_BuildType_leancArgs(x_27);
x_68 = l_Array_append___rarg(x_67, x_32);
lean_dec(x_32);
x_69 = l_Array_append___rarg(x_68, x_33);
lean_dec(x_33);
x_35 = x_69;
goto block_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = l_Lake_BuildType_leancArgs(x_26);
x_71 = l_Array_append___rarg(x_70, x_32);
lean_dec(x_32);
x_72 = l_Array_append___rarg(x_71, x_33);
lean_dec(x_33);
x_35 = x_72;
goto block_66;
}
block_66:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__2___boxed), 5, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__2;
x_38 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_36);
x_39 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__6), 7, 5);
lean_closure_set(x_39, 0, x_25);
lean_closure_set(x_39, 1, x_35);
lean_closure_set(x_39, 2, x_19);
lean_closure_set(x_39, 3, x_38);
lean_closure_set(x_39, 4, x_6);
x_40 = l_Task_Priority_default;
x_41 = 0;
x_42 = lean_io_map_task(x_39, x_34, x_40, x_41, x_9);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_3);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_3, 0);
lean_dec(x_46);
lean_ctor_set(x_3, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_3);
lean_ctor_set(x_47, 1, x_7);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_8);
lean_ctor_set(x_42, 0, x_48);
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_dec(x_3);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_8);
lean_ctor_set(x_42, 0, x_53);
return x_42;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_42, 0);
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_42);
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_57 = x_3;
} else {
 lean_dec_ref(x_3);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_8);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
return x_42;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_42, 0);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_42);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
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
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
lean_dec(x_8);
x_10 = 2;
x_11 = l_Lake_instDecidableEqVerbosity(x_9, x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = 1;
lean_inc(x_12);
x_14 = l_Lean_Name_toString(x_12, x_13);
x_15 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lake_Module_recBuildLeanCToOExport___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Lake_Module_cFacetConfig___closed__1;
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, lean_box(0));
x_22 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToONoExport___lambda__1___boxed), 9, 2);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_12);
x_23 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16___rarg), 8, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
if (x_11 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_string_append(x_18, x_15);
x_25 = lean_string_append(x_24, x_15);
x_26 = l_Lake_withRegisterJob___rarg(x_25, x_23, x_2, x_3, x_4, x_5, x_6, x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lake_Module_recBuildLeanCToONoExport___closed__1;
x_28 = lean_string_append(x_18, x_27);
x_29 = lean_string_append(x_28, x_15);
x_30 = l_Lake_withRegisterJob___rarg(x_29, x_23, x_2, x_3, x_4, x_5, x_6, x_7);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Module_recBuildLeanCToONoExport___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_coNoExportFacetConfig___closed__3;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_coNoExportFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_coNoExportFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_coFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_coFacetConfig___closed__2;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_coFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_coFacetConfig___closed__3;
return x_1;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_16 = lean_ctor_get(x_13, 12);
lean_inc(x_16);
x_17 = l_System_FilePath_join(x_15, x_16);
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
x_26 = lean_ctor_get_uint8(x_20, sizeof(void*)*9);
x_27 = lean_ctor_get_uint8(x_23, sizeof(void*)*9);
x_28 = l_Lake_instOrdBuildType;
x_29 = lean_box(x_26);
x_30 = lean_box(x_27);
x_31 = l_instDecidableRelLe___rarg(x_28, x_29, x_30);
x_32 = lean_ctor_get(x_20, 3);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_23, 3);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
if (x_31 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = l_Lake_BuildType_leancArgs(x_27);
x_68 = l_Array_append___rarg(x_67, x_32);
lean_dec(x_32);
x_69 = l_Array_append___rarg(x_68, x_33);
lean_dec(x_33);
x_35 = x_69;
goto block_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = l_Lake_BuildType_leancArgs(x_26);
x_71 = l_Array_append___rarg(x_70, x_32);
lean_dec(x_32);
x_72 = l_Array_append___rarg(x_71, x_33);
lean_dec(x_33);
x_35 = x_72;
goto block_66;
}
block_66:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__2___boxed), 5, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__2;
x_38 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_36);
x_39 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__6), 7, 5);
lean_closure_set(x_39, 0, x_25);
lean_closure_set(x_39, 1, x_35);
lean_closure_set(x_39, 2, x_19);
lean_closure_set(x_39, 3, x_38);
lean_closure_set(x_39, 4, x_6);
x_40 = l_Task_Priority_default;
x_41 = 0;
x_42 = lean_io_map_task(x_39, x_34, x_40, x_41, x_9);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_3);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_3, 0);
lean_dec(x_46);
lean_ctor_set(x_3, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_3);
lean_ctor_set(x_47, 1, x_7);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_8);
lean_ctor_set(x_42, 0, x_48);
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_dec(x_3);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_8);
lean_ctor_set(x_42, 0, x_53);
return x_42;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_42, 0);
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_42);
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_57 = x_3;
} else {
 lean_dec_ref(x_3);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_8);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
return x_42;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_42, 0);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_42);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
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
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Module_recBuildLeanBcToO___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lake_Module_bcFacetConfig___closed__1;
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, lean_box(0));
x_18 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanBcToO___lambda__1___boxed), 9, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_8);
x_19 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16___rarg), 8, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lake_withRegisterJob___rarg(x_14, x_19, x_2, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Module_recBuildLeanBcToO___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_bcoFacetConfig___closed__2;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_bcoFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_bcoFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*9 + 1);
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
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*9 + 1);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oExportFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oExportFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_oExportFacetConfig___closed__2;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oExportFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_oExportFacetConfig___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the LLVM backend only supports exporting Lean symbols", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*9 + 1);
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
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*9 + 1);
lean_dec(x_14);
x_16 = l_Lake_Backend_orPreferLeft(x_11, x_15);
x_17 = lean_box(x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_array_get_size(x_5);
x_19 = l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__2;
x_20 = lean_array_push(x_5, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_24 = l_Lake_Module_coNoExportFacetConfig___closed__2;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_apply_6(x_2, x_25, x_3, x_4, x_5, x_6, x_7);
return x_26;
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oNoExportFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_oNoExportFacetConfig___closed__2;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_oNoExportFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*9 + 1);
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
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*9 + 1);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_oFacetConfig___closed__2;
x_2 = l_Lake_Module_oleanFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_oFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_15);
lean_inc(x_5);
lean_inc(x_7);
lean_inc(x_6);
x_19 = lean_apply_6(x_5, x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_28 = lean_array_uset(x_17, x_3, x_24);
x_3 = x_27;
x_4 = x_28;
x_8 = x_25;
x_9 = x_23;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_19, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_20, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_20, 0, x_37);
return x_19;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_41 = x_21;
} else {
 lean_dec_ref(x_21);
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
lean_ctor_set(x_19, 0, x_43);
return x_19;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_dec(x_19);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_46 = x_20;
} else {
 lean_dec_ref(x_20);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_21, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_49 = x_21;
} else {
 lean_dec_ref(x_21);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_46;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_19);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_19, 0);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_19);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
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
x_8 = lean_ctor_get(x_5, 1);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___closed__1;
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
x_10 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-l", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___closed__1;
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
x_10 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; lean_object* x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_18, 6);
x_20 = l_Array_append___rarg(x_17, x_19);
x_21 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_20);
x_22 = l_Lake_platformTrace;
x_23 = lean_uint64_mix_hash(x_21, x_22);
x_24 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
x_25 = lean_box_uint64(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lake_BuildTrace_mix(x_11, x_26);
x_28 = l_Lake_BuildTrace_mix(x_3, x_27);
x_29 = l_Lake_BuildTrace_mix(x_4, x_28);
x_30 = l_Lake_BuildTrace_mix(x_5, x_29);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_15, 8);
lean_inc(x_32);
x_33 = l_System_FilePath_join(x_31, x_32);
x_34 = lean_ctor_get(x_15, 10);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l_System_FilePath_join(x_33, x_34);
x_36 = l_Lake_Module_recBuildDynlib___lambda__2___closed__1;
x_37 = 1;
x_38 = l_Lean_Name_toStringWithSep(x_36, x_37, x_6);
x_39 = l_Lake_Module_dynlibSuffix;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_Lake_nameToSharedLib(x_40);
x_42 = l_System_FilePath_join(x_35, x_41);
x_43 = lean_array_get_size(x_7);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_45 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_44, x_8, x_7);
x_46 = lean_array_get_size(x_9);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3(x_47, x_8, x_9);
x_49 = l_Array_append___rarg(x_45, x_48);
lean_dec(x_48);
x_50 = lean_array_get_size(x_10);
x_51 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_52 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4(x_51, x_8, x_10);
x_53 = l_Array_append___rarg(x_49, x_52);
lean_dec(x_52);
x_54 = lean_ctor_get(x_16, 7);
lean_inc(x_54);
lean_dec(x_16);
x_55 = lean_ctor_get(x_18, 7);
x_56 = l_Array_append___rarg(x_54, x_55);
x_57 = l_Array_append___rarg(x_53, x_56);
lean_dec(x_56);
x_58 = l_Array_append___rarg(x_57, x_20);
lean_dec(x_20);
lean_inc(x_42);
x_59 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__1___boxed), 6, 2);
lean_closure_set(x_59, 0, x_42);
lean_closure_set(x_59, 1, x_58);
x_60 = l_Lake_Module_recBuildLeanCToOExport___lambda__5___closed__1;
x_61 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_61, 0, x_60);
lean_closure_set(x_61, 1, x_59);
lean_inc(x_42);
x_62 = l_Lake_buildFileUnlessUpToDate(x_42, x_30, x_61, x_12, x_13, x_14);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_40);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_63, 0, x_69);
return x_62;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_63, 0);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_63);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_42);
lean_ctor_set(x_72, 1, x_40);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_62, 0, x_74);
return x_62;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_62, 1);
lean_inc(x_75);
lean_dec(x_62);
x_76 = lean_ctor_get(x_63, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_63, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_78 = x_63;
} else {
 lean_dec_ref(x_63);
 x_78 = lean_box(0);
}
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_42);
lean_ctor_set(x_79, 1, x_40);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_75);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_42);
lean_dec(x_40);
x_83 = !lean_is_exclusive(x_62);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_62, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_63);
if (x_85 == 0)
{
return x_62;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_63, 0);
x_87 = lean_ctor_get(x_63, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_63);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_62, 0, x_88);
return x_62;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_62, 1);
lean_inc(x_89);
lean_dec(x_62);
x_90 = lean_ctor_get(x_63, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_63, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_92 = x_63;
} else {
 lean_dec_ref(x_63);
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
lean_dec(x_42);
lean_dec(x_40);
x_95 = !lean_is_exclusive(x_62);
if (x_95 == 0)
{
return x_62;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_62, 0);
x_97 = lean_ctor_get(x_62, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_62);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_array_get_size(x_1);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_18, x_2, x_1);
x_20 = lean_array_get_size(x_15);
x_21 = lean_usize_of_nat(x_20);
lean_inc(x_15);
x_22 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_21, x_2, x_15);
x_23 = l_Array_append___rarg(x_19, x_22);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(x_15, x_24, x_20);
lean_dec(x_20);
lean_dec(x_15);
x_26 = l_Array_append___rarg(x_3, x_25);
lean_dec(x_25);
x_27 = lean_box_usize(x_2);
x_28 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__2___boxed), 14, 10);
lean_closure_set(x_28, 0, x_4);
lean_closure_set(x_28, 1, x_5);
lean_closure_set(x_28, 2, x_16);
lean_closure_set(x_28, 3, x_6);
lean_closure_set(x_28, 4, x_7);
lean_closure_set(x_28, 5, x_8);
lean_closure_set(x_28, 6, x_9);
lean_closure_set(x_28, 7, x_27);
lean_closure_set(x_28, 8, x_26);
lean_closure_set(x_28, 9, x_23);
x_29 = l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__2;
x_30 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_28);
x_31 = 1;
lean_inc(x_10);
x_32 = l_IO_FS_withIsolatedStreams___at_Lake_computeDynlibOfShared___spec__1(x_30, x_31, x_10, x_14, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_String_isEmpty(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; 
x_40 = l_Lake_Module_recBuildLean___lambda__5___closed__1;
x_41 = lean_string_append(x_40, x_37);
lean_dec(x_37);
x_42 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = 1;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_array_push(x_47, x_45);
lean_ctor_set(x_36, 0, x_48);
x_49 = lean_box(0);
x_50 = l_Lake_Module_recBuildLean___lambda__4(x_38, x_49, x_10, x_36, x_35);
lean_dec(x_10);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_36, 0);
x_52 = lean_ctor_get_uint8(x_36, sizeof(void*)*1);
lean_inc(x_51);
lean_dec(x_36);
x_53 = lean_array_push(x_51, x_45);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_52);
x_55 = lean_box(0);
x_56 = l_Lake_Module_recBuildLean___lambda__4(x_38, x_55, x_10, x_54, x_35);
lean_dec(x_10);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_37);
x_57 = lean_box(0);
x_58 = l_Lake_Module_recBuildLean___lambda__4(x_38, x_57, x_10, x_36, x_35);
lean_dec(x_10);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_10);
x_59 = !lean_is_exclusive(x_32);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_32, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_33);
if (x_61 == 0)
{
return x_32;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_33, 0);
x_63 = lean_ctor_get(x_33, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_33);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_32, 0, x_64);
return x_32;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_32, 1);
lean_inc(x_65);
lean_dec(x_32);
x_66 = lean_ctor_get(x_33, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_68 = x_33;
} else {
 lean_dec_ref(x_33);
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
lean_dec(x_10);
x_71 = !lean_is_exclusive(x_32);
if (x_71 == 0)
{
return x_32;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_32, 0);
x_73 = lean_ctor_get(x_32, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_32);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_11);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_11);
lean_ctor_set(x_76, 1, x_12);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_11, 0);
x_78 = lean_ctor_get(x_11, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_12);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_box_usize(x_2);
x_18 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 12, 10);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_15);
lean_closure_set(x_18, 6, x_6);
lean_closure_set(x_18, 7, x_7);
lean_closure_set(x_18, 8, x_8);
lean_closure_set(x_18, 9, x_9);
x_19 = l_Task_Priority_default;
x_20 = 0;
x_21 = lean_io_map_task(x_18, x_16, x_19, x_20, x_11);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_24, 0, x_13);
x_25 = 1;
x_26 = lean_task_map(x_24, x_23, x_19, x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_29, 0, x_13);
x_30 = 1;
x_31 = lean_task_map(x_29, x_27, x_19, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_task_pure(x_10);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_11);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_task_pure(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_11);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_box_usize(x_3);
x_17 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__4___boxed), 11, 9);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_6);
lean_closure_set(x_17, 5, x_14);
lean_closure_set(x_17, 6, x_7);
lean_closure_set(x_17, 7, x_13);
lean_closure_set(x_17, 8, x_8);
x_18 = l_Task_Priority_default;
x_19 = 0;
x_20 = lean_io_bind_task(x_15, x_17, x_18, x_19, x_10);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_23, 0, x_12);
x_24 = 1;
x_25 = lean_task_map(x_23, x_22, x_18, x_24);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_28, 0, x_12);
x_29 = 1;
x_30 = lean_task_map(x_28, x_26, x_18, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_9);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_task_pure(x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_task_pure(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_usize_of_nat(x_10);
x_12 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_10);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (x_21 == 0)
{
lean_object* x_193; 
lean_dec(x_10);
lean_dec(x_3);
x_193 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_24 = x_193;
goto block_192;
}
else
{
uint8_t x_194; 
x_194 = lean_nat_dec_le(x_10, x_10);
lean_dec(x_10);
if (x_194 == 0)
{
lean_object* x_195; 
lean_dec(x_3);
x_195 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_24 = x_195;
goto block_192;
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_197 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__15(x_3, x_12, x_11, x_196);
lean_dec(x_3);
x_24 = x_197;
goto block_192;
}
}
block_192:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_23);
x_25 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_24, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lake_recBuildExternDynlibs(x_26, x_4, x_5, x_6, x_19, x_17, x_16);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_ctor_get(x_36, 8);
lean_inc(x_37);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_apply_1(x_37, x_39);
x_41 = lean_array_get_size(x_40);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
lean_inc(x_6);
x_43 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1(x_1, x_42, x_12, x_40, x_4, x_5, x_6, x_33, x_32, x_31);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_44, 1);
x_49 = lean_ctor_get(x_44, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
x_53 = l_Lake_BuildJob_collectArray___rarg(x_51);
lean_dec(x_51);
x_54 = l_Lake_BuildJob_collectArray___rarg(x_18);
lean_dec(x_18);
x_55 = l_Lake_BuildJob_collectArray___rarg(x_34);
lean_dec(x_34);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
x_59 = l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1;
x_60 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__5___boxed), 10, 8);
lean_closure_set(x_60, 0, x_54);
lean_closure_set(x_60, 1, x_55);
lean_closure_set(x_60, 2, x_59);
lean_closure_set(x_60, 3, x_35);
lean_closure_set(x_60, 4, x_23);
lean_closure_set(x_60, 5, x_36);
lean_closure_set(x_60, 6, x_2);
lean_closure_set(x_60, 7, x_6);
x_61 = l_Task_Priority_default;
x_62 = 0;
x_63 = lean_io_bind_task(x_57, x_60, x_61, x_62, x_46);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_ctor_set(x_53, 0, x_65);
lean_ctor_set(x_45, 0, x_53);
lean_ctor_set(x_63, 0, x_44);
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
lean_ctor_set(x_53, 0, x_66);
lean_ctor_set(x_45, 0, x_53);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_44);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_free_object(x_53);
lean_dec(x_58);
lean_free_object(x_45);
lean_dec(x_52);
lean_free_object(x_44);
lean_dec(x_48);
x_69 = !lean_is_exclusive(x_63);
if (x_69 == 0)
{
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_63, 0);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_63);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_53, 0);
x_74 = lean_ctor_get(x_53, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_53);
x_75 = l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1;
x_76 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__5___boxed), 10, 8);
lean_closure_set(x_76, 0, x_54);
lean_closure_set(x_76, 1, x_55);
lean_closure_set(x_76, 2, x_75);
lean_closure_set(x_76, 3, x_35);
lean_closure_set(x_76, 4, x_23);
lean_closure_set(x_76, 5, x_36);
lean_closure_set(x_76, 6, x_2);
lean_closure_set(x_76, 7, x_6);
x_77 = l_Task_Priority_default;
x_78 = 0;
x_79 = lean_io_bind_task(x_73, x_76, x_77, x_78, x_46);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
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
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_45, 0, x_83);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_44);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_74);
lean_free_object(x_45);
lean_dec(x_52);
lean_free_object(x_44);
lean_dec(x_48);
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_87 = x_79;
} else {
 lean_dec_ref(x_79);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_45, 0);
x_90 = lean_ctor_get(x_45, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_45);
x_91 = l_Lake_BuildJob_collectArray___rarg(x_89);
lean_dec(x_89);
x_92 = l_Lake_BuildJob_collectArray___rarg(x_18);
lean_dec(x_18);
x_93 = l_Lake_BuildJob_collectArray___rarg(x_34);
lean_dec(x_34);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
x_97 = l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1;
x_98 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__5___boxed), 10, 8);
lean_closure_set(x_98, 0, x_92);
lean_closure_set(x_98, 1, x_93);
lean_closure_set(x_98, 2, x_97);
lean_closure_set(x_98, 3, x_35);
lean_closure_set(x_98, 4, x_23);
lean_closure_set(x_98, 5, x_36);
lean_closure_set(x_98, 6, x_2);
lean_closure_set(x_98, 7, x_6);
x_99 = l_Task_Priority_default;
x_100 = 0;
x_101 = lean_io_bind_task(x_94, x_98, x_99, x_100, x_46);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
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
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_90);
lean_ctor_set(x_44, 0, x_106);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_44);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_90);
lean_free_object(x_44);
lean_dec(x_48);
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
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
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_112 = lean_ctor_get(x_44, 1);
lean_inc(x_112);
lean_dec(x_44);
x_113 = lean_ctor_get(x_45, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_45, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_115 = x_45;
} else {
 lean_dec_ref(x_45);
 x_115 = lean_box(0);
}
x_116 = l_Lake_BuildJob_collectArray___rarg(x_113);
lean_dec(x_113);
x_117 = l_Lake_BuildJob_collectArray___rarg(x_18);
lean_dec(x_18);
x_118 = l_Lake_BuildJob_collectArray___rarg(x_34);
lean_dec(x_34);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_121 = x_116;
} else {
 lean_dec_ref(x_116);
 x_121 = lean_box(0);
}
x_122 = l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1;
x_123 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__5___boxed), 10, 8);
lean_closure_set(x_123, 0, x_117);
lean_closure_set(x_123, 1, x_118);
lean_closure_set(x_123, 2, x_122);
lean_closure_set(x_123, 3, x_35);
lean_closure_set(x_123, 4, x_23);
lean_closure_set(x_123, 5, x_36);
lean_closure_set(x_123, 6, x_2);
lean_closure_set(x_123, 7, x_6);
x_124 = l_Task_Priority_default;
x_125 = 0;
x_126 = lean_io_bind_task(x_119, x_123, x_124, x_125, x_46);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_121;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_120);
if (lean_is_scalar(x_115)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_115;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_114);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_112);
if (lean_is_scalar(x_129)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_129;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_128);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_112);
x_134 = lean_ctor_get(x_126, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_126, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_136 = x_126;
} else {
 lean_dec_ref(x_126);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_2);
x_138 = !lean_is_exclusive(x_43);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_43, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_44);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_44, 0);
lean_dec(x_141);
x_142 = !lean_is_exclusive(x_45);
if (x_142 == 0)
{
return x_43;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_45, 0);
x_144 = lean_ctor_get(x_45, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_45);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_44, 0, x_145);
return x_43;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_44, 1);
lean_inc(x_146);
lean_dec(x_44);
x_147 = lean_ctor_get(x_45, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_45, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_149 = x_45;
} else {
 lean_dec_ref(x_45);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_43, 0, x_151);
return x_43;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_152 = lean_ctor_get(x_43, 1);
lean_inc(x_152);
lean_dec(x_43);
x_153 = lean_ctor_get(x_44, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_154 = x_44;
} else {
 lean_dec_ref(x_44);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_45, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_45, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_157 = x_45;
} else {
 lean_dec_ref(x_45);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
if (lean_is_scalar(x_154)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_154;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_153);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_152);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_2);
x_161 = !lean_is_exclusive(x_43);
if (x_161 == 0)
{
return x_43;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_43, 0);
x_163 = lean_ctor_get(x_43, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_43);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_27);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_ctor_get(x_27, 0);
lean_dec(x_166);
x_167 = !lean_is_exclusive(x_28);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_28, 0);
lean_dec(x_168);
x_169 = !lean_is_exclusive(x_29);
if (x_169 == 0)
{
return x_27;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_29, 0);
x_171 = lean_ctor_get(x_29, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_29);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_28, 0, x_172);
return x_27;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_173 = lean_ctor_get(x_28, 1);
lean_inc(x_173);
lean_dec(x_28);
x_174 = lean_ctor_get(x_29, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_29, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_176 = x_29;
} else {
 lean_dec_ref(x_29);
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
lean_ctor_set(x_27, 0, x_178);
return x_27;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_179 = lean_ctor_get(x_27, 1);
lean_inc(x_179);
lean_dec(x_27);
x_180 = lean_ctor_get(x_28, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_181 = x_28;
} else {
 lean_dec_ref(x_28);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_29, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_29, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_184 = x_29;
} else {
 lean_dec_ref(x_29);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_180);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_27);
if (x_188 == 0)
{
return x_27;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_27, 0);
x_190 = lean_ctor_get(x_27, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_27);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_13);
if (x_198 == 0)
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_13, 0);
lean_dec(x_199);
x_200 = !lean_is_exclusive(x_14);
if (x_200 == 0)
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_14, 0);
lean_dec(x_201);
x_202 = !lean_is_exclusive(x_15);
if (x_202 == 0)
{
return x_13;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_15, 0);
x_204 = lean_ctor_get(x_15, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_15);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_14, 0, x_205);
return x_13;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_206 = lean_ctor_get(x_14, 1);
lean_inc(x_206);
lean_dec(x_14);
x_207 = lean_ctor_get(x_15, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_15, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_209 = x_15;
} else {
 lean_dec_ref(x_15);
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
lean_ctor_set(x_13, 0, x_211);
return x_13;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_212 = lean_ctor_get(x_13, 1);
lean_inc(x_212);
lean_dec(x_13);
x_213 = lean_ctor_get(x_14, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_214 = x_14;
} else {
 lean_dec_ref(x_14);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_15, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_15, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_217 = x_15;
} else {
 lean_dec_ref(x_15);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
if (lean_is_scalar(x_214)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_214;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_213);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_212);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_13);
if (x_221 == 0)
{
return x_13;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_13, 0);
x_223 = lean_ctor_get(x_13, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_13);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Module_recBuildDynlib___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, lean_box(0));
x_18 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__6), 9, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_8);
x_19 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__16___rarg), 8, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lake_withRegisterJob___rarg(x_14, x_19, x_2, x_3, x_4, x_5, x_6, x_7);
return x_20;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Module_recBuildDynlib___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_16 = l_Lake_Module_recBuildDynlib___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Lake_Module_recBuildDynlib___lambda__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; lean_object* x_13; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Lake_Module_recBuildDynlib___lambda__4(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Lake_Module_recBuildDynlib___lambda__5(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_dynlibFacetConfig___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_task_map(x_4, x_3, x_5, x_6);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_task_map(x_10, x_8, x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
static lean_object* _init_l_Lake_Module_dynlibFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_Module_dynlibFacetConfig___spec__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_dynlibFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Module_dynlibFacetConfig___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_dynlibFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_dynlibFacetConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_dynlibFacetConfig___closed__3;
x_2 = l_Lake_Module_dynlibFacetConfig___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_dynlibFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_dynlibFacetConfig___closed__4;
return x_1;
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
x_2 = l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
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
x_2 = l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
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
x_2 = l_Lake_Module_depsFacetConfig___closed__4;
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
x_2 = l_Lake_Module_leanArtsFacetConfig___closed__4;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_OrdHashSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_List(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Module(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1);
l_Lake_recBuildExternDynlibs___closed__1 = _init_l_Lake_recBuildExternDynlibs___closed__1();
lean_mark_persistent(l_Lake_recBuildExternDynlibs___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__12___closed__3);
l_Lake_Module_recParseImports___closed__1 = _init_l_Lake_Module_recParseImports___closed__1();
lean_mark_persistent(l_Lake_Module_recParseImports___closed__1);
l_Lake_Module_importsFacetConfig___closed__1 = _init_l_Lake_Module_importsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__1);
l_Lake_Module_importsFacetConfig___closed__2 = _init_l_Lake_Module_importsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__2);
l_Lake_Module_importsFacetConfig___closed__3 = _init_l_Lake_Module_importsFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__3);
l_Lake_Module_importsFacetConfig___closed__4 = _init_l_Lake_Module_importsFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__4);
l_Lake_Module_importsFacetConfig = _init_l_Lake_Module_importsFacetConfig();
lean_mark_persistent(l_Lake_Module_importsFacetConfig);
l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1);
l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2);
l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3);
l_Lake_collectImportsAux___closed__1 = _init_l_Lake_collectImportsAux___closed__1();
lean_mark_persistent(l_Lake_collectImportsAux___closed__1);
l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2);
l_Lake_Module_transImportsFacetConfig___closed__1 = _init_l_Lake_Module_transImportsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig___closed__1);
l_Lake_Module_transImportsFacetConfig___closed__2 = _init_l_Lake_Module_transImportsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig___closed__2);
l_Lake_Module_transImportsFacetConfig = _init_l_Lake_Module_transImportsFacetConfig();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig);
l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2);
l_Lake_Module_precompileImportsFacetConfig___closed__1 = _init_l_Lake_Module_precompileImportsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_precompileImportsFacetConfig___closed__1);
l_Lake_Module_precompileImportsFacetConfig___closed__2 = _init_l_Lake_Module_precompileImportsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_precompileImportsFacetConfig___closed__2);
l_Lake_Module_precompileImportsFacetConfig = _init_l_Lake_Module_precompileImportsFacetConfig();
lean_mark_persistent(l_Lake_Module_precompileImportsFacetConfig);
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
l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__2);
l_Lake_Module_recBuildDeps___lambda__1___closed__1 = _init_l_Lake_Module_recBuildDeps___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDeps___lambda__1___closed__1);
l_Lake_Module_recBuildDeps___lambda__1___closed__2 = _init_l_Lake_Module_recBuildDeps___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildDeps___lambda__1___closed__2);
l_Lake_Module_recBuildDeps___lambda__1___closed__3___boxed__const__1 = _init_l_Lake_Module_recBuildDeps___lambda__1___closed__3___boxed__const__1();
lean_mark_persistent(l_Lake_Module_recBuildDeps___lambda__1___closed__3___boxed__const__1);
l_Lake_Module_recBuildDeps___lambda__1___closed__3 = _init_l_Lake_Module_recBuildDeps___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Module_recBuildDeps___lambda__1___closed__3);
l_Lake_Module_recBuildDeps___closed__1 = _init_l_Lake_Module_recBuildDeps___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDeps___closed__1);
l_Lake_Module_recBuildDeps___closed__2 = _init_l_Lake_Module_recBuildDeps___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildDeps___closed__2);
l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__1 = _init_l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__1();
lean_mark_persistent(l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__1);
l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2 = _init_l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2();
lean_mark_persistent(l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2);
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
l_Lake_Module_depsFacetConfig___closed__6 = _init_l_Lake_Module_depsFacetConfig___closed__6();
lean_mark_persistent(l_Lake_Module_depsFacetConfig___closed__6);
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
l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__2);
l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__4);
l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Module_recBuildLean___spec__4___closed__5);
l_Lake_Module_recBuildLean___lambda__3___closed__1 = _init_l_Lake_Module_recBuildLean___lambda__3___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLean___lambda__3___closed__1);
l_Lake_Module_recBuildLean___lambda__5___closed__1 = _init_l_Lake_Module_recBuildLean___lambda__5___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLean___lambda__5___closed__1);
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
l_Lake_Module_leanArtsFacetConfig___closed__6 = _init_l_Lake_Module_leanArtsFacetConfig___closed__6();
lean_mark_persistent(l_Lake_Module_leanArtsFacetConfig___closed__6);
l_Lake_Module_leanArtsFacetConfig = _init_l_Lake_Module_leanArtsFacetConfig();
lean_mark_persistent(l_Lake_Module_leanArtsFacetConfig);
l_Lake_Module_oleanFacetConfig___closed__1 = _init_l_Lake_Module_oleanFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig___closed__1);
l_Lake_Module_oleanFacetConfig___closed__2 = _init_l_Lake_Module_oleanFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig___closed__2);
l_Lake_Module_oleanFacetConfig___closed__3 = _init_l_Lake_Module_oleanFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig___closed__3);
l_Lake_Module_oleanFacetConfig___closed__4 = _init_l_Lake_Module_oleanFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig___closed__4);
l_Lake_Module_oleanFacetConfig = _init_l_Lake_Module_oleanFacetConfig();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig);
l_Lake_Module_ileanFacetConfig___closed__1 = _init_l_Lake_Module_ileanFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_ileanFacetConfig___closed__1);
l_Lake_Module_ileanFacetConfig___closed__2 = _init_l_Lake_Module_ileanFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_ileanFacetConfig___closed__2);
l_Lake_Module_ileanFacetConfig___closed__3 = _init_l_Lake_Module_ileanFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_ileanFacetConfig___closed__3);
l_Lake_Module_ileanFacetConfig = _init_l_Lake_Module_ileanFacetConfig();
lean_mark_persistent(l_Lake_Module_ileanFacetConfig);
l_Lake_Module_cFacetConfig___closed__1 = _init_l_Lake_Module_cFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_cFacetConfig___closed__1);
l_Lake_Module_cFacetConfig___closed__2 = _init_l_Lake_Module_cFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_cFacetConfig___closed__2);
l_Lake_Module_cFacetConfig___closed__3 = _init_l_Lake_Module_cFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_cFacetConfig___closed__3);
l_Lake_Module_cFacetConfig = _init_l_Lake_Module_cFacetConfig();
lean_mark_persistent(l_Lake_Module_cFacetConfig);
l_Lake_Module_bcFacetConfig___closed__1 = _init_l_Lake_Module_bcFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_bcFacetConfig___closed__1);
l_Lake_Module_bcFacetConfig___closed__2 = _init_l_Lake_Module_bcFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_bcFacetConfig___closed__2);
l_Lake_Module_bcFacetConfig___closed__3 = _init_l_Lake_Module_bcFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_bcFacetConfig___closed__3);
l_Lake_Module_bcFacetConfig = _init_l_Lake_Module_bcFacetConfig();
lean_mark_persistent(l_Lake_Module_bcFacetConfig);
l_Lake_Module_recBuildLeanCToOExport___lambda__5___closed__1 = _init_l_Lake_Module_recBuildLeanCToOExport___lambda__5___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToOExport___lambda__5___closed__1);
l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__1 = _init_l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__1);
l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__2 = _init_l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToOExport___lambda__7___closed__2);
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
l_Lake_Module_coNoExportFacetConfig = _init_l_Lake_Module_coNoExportFacetConfig();
lean_mark_persistent(l_Lake_Module_coNoExportFacetConfig);
l_Lake_Module_coFacetConfig___closed__1 = _init_l_Lake_Module_coFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_coFacetConfig___closed__1);
l_Lake_Module_coFacetConfig___closed__2 = _init_l_Lake_Module_coFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_coFacetConfig___closed__2);
l_Lake_Module_coFacetConfig___closed__3 = _init_l_Lake_Module_coFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_coFacetConfig___closed__3);
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
l_Lake_Module_bcoFacetConfig = _init_l_Lake_Module_bcoFacetConfig();
lean_mark_persistent(l_Lake_Module_bcoFacetConfig);
l_Lake_Module_oExportFacetConfig___closed__1 = _init_l_Lake_Module_oExportFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_oExportFacetConfig___closed__1);
l_Lake_Module_oExportFacetConfig___closed__2 = _init_l_Lake_Module_oExportFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_oExportFacetConfig___closed__2);
l_Lake_Module_oExportFacetConfig___closed__3 = _init_l_Lake_Module_oExportFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_oExportFacetConfig___closed__3);
l_Lake_Module_oExportFacetConfig = _init_l_Lake_Module_oExportFacetConfig();
lean_mark_persistent(l_Lake_Module_oExportFacetConfig);
l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__1 = _init_l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__1();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__1);
l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__2 = _init_l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__2();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__2);
l_Lake_Module_oNoExportFacetConfig___closed__1 = _init_l_Lake_Module_oNoExportFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___closed__1);
l_Lake_Module_oNoExportFacetConfig___closed__2 = _init_l_Lake_Module_oNoExportFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___closed__2);
l_Lake_Module_oNoExportFacetConfig___closed__3 = _init_l_Lake_Module_oNoExportFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig___closed__3);
l_Lake_Module_oNoExportFacetConfig = _init_l_Lake_Module_oNoExportFacetConfig();
lean_mark_persistent(l_Lake_Module_oNoExportFacetConfig);
l_Lake_Module_oFacetConfig___closed__1 = _init_l_Lake_Module_oFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_oFacetConfig___closed__1);
l_Lake_Module_oFacetConfig___closed__2 = _init_l_Lake_Module_oFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_oFacetConfig___closed__2);
l_Lake_Module_oFacetConfig___closed__3 = _init_l_Lake_Module_oFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_oFacetConfig___closed__3);
l_Lake_Module_oFacetConfig = _init_l_Lake_Module_oFacetConfig();
lean_mark_persistent(l_Lake_Module_oFacetConfig);
l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___closed__1);
l_Lake_Module_recBuildDynlib___lambda__2___closed__1 = _init_l_Lake_Module_recBuildDynlib___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__2___closed__1);
l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1 = _init_l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1);
l_Lake_Module_recBuildDynlib___closed__1 = _init_l_Lake_Module_recBuildDynlib___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___closed__1);
l_Lake_Module_dynlibFacetConfig___closed__1 = _init_l_Lake_Module_dynlibFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_dynlibFacetConfig___closed__1);
l_Lake_Module_dynlibFacetConfig___closed__2 = _init_l_Lake_Module_dynlibFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_dynlibFacetConfig___closed__2);
l_Lake_Module_dynlibFacetConfig___closed__3 = _init_l_Lake_Module_dynlibFacetConfig___closed__3();
lean_mark_persistent(l_Lake_Module_dynlibFacetConfig___closed__3);
l_Lake_Module_dynlibFacetConfig___closed__4 = _init_l_Lake_Module_dynlibFacetConfig___closed__4();
lean_mark_persistent(l_Lake_Module_dynlibFacetConfig___closed__4);
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

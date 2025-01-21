// Lean compiler output
// Module: Lake.Build.Module
// Imports: Lake.Util.OrdHashSet Lake.Util.List Lean.Elab.ParseImportsFast Lake.Build.Common
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
static lean_object* l_Lake_Module_transImportsFacetConfig___closed__1;
lean_object* l_Lake_Module_bcFile_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__4;
lean_object* l_Array_take___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__2;
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig;
static lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__2;
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__2;
extern lean_object* l_Lake_instOrdBuildType;
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_nameToSharedLib(lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__13;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(lean_object*, size_t, size_t, uint64_t);
static uint8_t l_Lake_Module_clearOutputHashes___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__1___boxed(lean_object*);
lean_object* l_Lake_instBEqModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___lambda__3___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__1;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__1(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__4;
static lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_bcFacetConfig___closed__2;
static lean_object* l_Lake_Module_clearOutputHashes___closed__2;
lean_object* l___private_Lake_Build_Job_0__Lake_Job_toOpaqueImpl___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__5;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig;
static lean_object* l_Lake_Module_ileanFacetConfig___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_initModuleFacetConfigs___closed__10;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Ord_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildUnlessUpToDate_x3f_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4(size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recParseImports___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oExportFacetConfig___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2___closed__3___boxed__const__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_fetchFileTrace(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(size_t, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___closed__1;
lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_bcFacetConfig___closed__3;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__7;
lean_object* l_Lake_ensureJob___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___closed__1;
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__5;
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_ileanFacetConfig___closed__1;
static lean_object* l_Lake_Module_recBuildDeps___lambda__2___closed__2;
static lean_object* l_Lake_Module_coExportFacetConfig___closed__5;
static lean_object* l_Lake_initModuleFacetConfigs___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recBuildDeps___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_clearOutputHashes(lean_object*, lean_object*);
extern uint64_t l_Lake_platformTrace;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_instHashableModule___boxed(lean_object*);
lean_object* l_Lake_Module_getMTime(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___lambda__3___closed__1;
static lean_object* l_Lake_collectImportsAux___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13(lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1;
lean_object* l_Lake_Module_checkExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_cacheOutputHashes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFacetConfig;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recBuildDeps___spec__10___at_Lake_Module_recBuildDeps___spec__11(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__12;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mixArray___rarg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coExportFacetConfig;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig;
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_initModuleFacetConfigs;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_collectImportsAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coExportFacetConfig___closed__2;
static lean_object* l_Lake_Module_bcoFacetConfig___closed__3;
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_withRegisterJob___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oExportFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig;
static lean_object* l_Lake_initModuleFacetConfigs___closed__16;
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_ileanFacetConfig___closed__3;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__2;
lean_object* l_Lake_Job_mapM___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lake_Module_recBuildLean___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig;
static lean_object* l_Lake_Module_bcFacetConfig___closed__1;
lean_object* l_Lake_Workspace_leanPath(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__1;
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanBcToO___closed__1;
lean_object* l_Lake_cacheFileHash(lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__1;
static lean_object* l_Lake_Module_oFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1;
static lean_object* l_Lake_Module_cFacetConfig___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__1;
static lean_object* l_Lake_Module_oleanFacetConfig___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recParseImports___spec__6___at_Lake_Module_recParseImports___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFacetConfig;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Ord_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coExportFacetConfig___closed__4;
static lean_object* l_Lake_initModuleFacetConfigs___closed__17;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_cFacetConfig___closed__1;
extern lean_object* l_Lake_BuildTrace_nil;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate_x27___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig;
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__2;
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_bcoFacetConfig;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(lean_object*, lean_object*);
lean_object* l_Lake_Job_collectArray___rarg(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recComputeTransImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recParseImports___closed__2;
static lean_object* l_Lake_Module_coExportFacetConfig___closed__1;
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recParseImports___closed__1;
static lean_object* l_Lake_Module_depsFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_recBuildExternDynlibs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recBuildExternDynlibs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__6;
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
static lean_object* l_Lake_Module_cFacetConfig___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recBuildDeps___spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__4;
lean_object* l_Lake_EquipT_lift___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_clearOutputHashes___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__14;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___closed__1;
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
static lean_object* l_Lake_Module_oleanFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToONoExport___closed__1;
uint8_t l_Lake_Backend_orPreferLeft(uint8_t, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
static lean_object* l_Lake_recBuildExternDynlibs___closed__1;
static lean_object* l_Lake_initModuleFacetConfigs___closed__11;
static lean_object* l_Lake_Module_bcoFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recParseImports___spec__6(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computePrecompileImportsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__3;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coFacetConfig___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Module_dynlibSuffix;
lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashablePackage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
static lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__3;
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
static lean_object* l_Lake_Module_transImportsFacetConfig___closed__2;
static lean_object* l_Lake_Module_precompileImportsFacetConfig___closed__1;
static lean_object* l_Lake_Module_coFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___lambda__1(lean_object*);
lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_clearOutputHashes___closed__4;
static lean_object* l_Lake_initModuleFacetConfigs___closed__3;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recBuildDeps___spec__8(lean_object*);
uint8_t lean_internal_has_llvm_backend(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__3(lean_object*, lean_object*);
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__3;
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instBEqPackage___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Module_coFacetConfig___closed__3;
static lean_object* l_Lake_Module_precompileImportsFacetConfig___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Module_oExportFacetConfig___closed__3;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__12(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recComputePrecompileImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6___closed__1;
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_Module_depsFacetConfig___closed__2;
static lean_object* l_Lake_initModuleFacetConfigs___closed__9;
static lean_object* l_Lake_Module_recBuildDeps___lambda__2___closed__3;
lean_object* l_Lean_Name_toStringWithSep(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_BuildType_leancArgs(uint8_t);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(size_t, size_t, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__15;
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recParseImports___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_clearFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectImportsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectImportsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computePrecompileImportsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
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
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_7);
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
lean_inc(x_8);
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
x_7 = x_21;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_8);
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
lean_dec(x_8);
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
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_10);
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
lean_inc(x_11);
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
x_10 = x_35;
x_12 = x_33;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_11);
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
lean_dec(x_11);
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
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_15 = lean_apply_1(x_1, x_14);
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
x_18 = lean_apply_1(x_1, x_16);
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
x_24 = lean_apply_1(x_1, x_21);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__3(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recParseImports___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recParseImports___spec__6___at_Lake_Module_recParseImports___spec__7(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recParseImports___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recParseImports___spec__6___at_Lake_Module_recParseImports___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recParseImports___spec__4(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recParseImports___spec__5(x_7, x_1, x_6);
return x_8;
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
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__3(x_2, x_21);
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
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recParseImports___spec__4(x_29);
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
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__3(x_2, x_55);
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
x_70 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recParseImports___spec__4(x_63);
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
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Functor_mapRev___at_Lake_Module_recParseImports___spec__8___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__3(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__3;
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__2;
x_17 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg), 8, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg), 8, 2);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__3), 2, 1);
lean_closure_set(x_19, 0, x_4);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Functor_mapRev___at_Lake_Module_recParseImports___spec__8___rarg(x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_2 = x_26;
x_4 = x_23;
x_8 = x_24;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_20, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_20, 0, x_33);
return x_20;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_37 = x_21;
} else {
 lean_dec_ref(x_21);
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
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_8);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_10);
return x_45;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_194; 
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
x_194 = l_IO_FS_readFile(x_19, x_7);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_194, 1);
lean_ctor_set(x_194, 1, x_5);
x_20 = x_194;
x_21 = x_196;
goto block_193;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_194, 0);
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_194);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_5);
x_20 = x_199;
x_21 = x_198;
goto block_193;
}
}
else
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_194);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_ctor_get(x_194, 0);
x_202 = lean_ctor_get(x_194, 1);
x_203 = lean_io_error_to_string(x_201);
x_204 = 3;
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_204);
x_206 = lean_array_get_size(x_5);
x_207 = lean_array_push(x_5, x_205);
lean_ctor_set(x_194, 1, x_207);
lean_ctor_set(x_194, 0, x_206);
x_20 = x_194;
x_21 = x_202;
goto block_193;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_208 = lean_ctor_get(x_194, 0);
x_209 = lean_ctor_get(x_194, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_194);
x_210 = lean_io_error_to_string(x_208);
x_211 = 3;
x_212 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*1, x_211);
x_213 = lean_array_get_size(x_5);
x_214 = lean_array_push(x_5, x_212);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_20 = x_215;
x_21 = x_209;
goto block_193;
}
}
block_193:
{
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_118; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
x_118 = l_Lean_parseImports_x27(x_23, x_19, x_21);
lean_dec(x_19);
lean_dec(x_23);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_ctor_set(x_20, 0, x_119);
x_25 = x_20;
x_26 = x_120;
goto block_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
x_123 = lean_io_error_to_string(x_121);
x_124 = 3;
x_125 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_124);
x_126 = lean_array_get_size(x_24);
x_127 = lean_array_push(x_24, x_125);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_127);
lean_ctor_set(x_20, 0, x_126);
x_25 = x_20;
x_26 = x_122;
goto block_117;
}
block_117:
{
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_array_get_size(x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = l_Lake_Module_recParseImports___closed__2;
lean_ctor_set(x_25, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_30, x_30);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = l_Lake_Module_recParseImports___closed__2;
lean_ctor_set(x_25, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_26);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_25);
x_38 = 0;
x_39 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_40 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_41 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9(x_28, x_38, x_39, x_40, x_2, x_3, x_4, x_29, x_6, x_26);
lean_dec(x_28);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_ctor_set(x_42, 0, x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_42, 0);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_42);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_41, 0, x_51);
return x_41;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_dec(x_41);
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_55 = x_42;
} else {
 lean_dec_ref(x_42);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_52);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_41);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_41, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
return x_41;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_42, 0);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_42);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_41, 0, x_64);
return x_41;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_dec(x_41);
x_66 = lean_ctor_get(x_42, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_42, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_68 = x_42;
} else {
 lean_dec_ref(x_42);
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
x_71 = !lean_is_exclusive(x_41);
if (x_71 == 0)
{
return x_41;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_41, 0);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_41);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_25, 0);
x_76 = lean_ctor_get(x_25, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_25);
x_77 = lean_array_get_size(x_75);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_lt(x_78, x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = l_Lake_Module_recParseImports___closed__2;
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_26);
return x_82;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_77, x_77);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = l_Lake_Module_recParseImports___closed__2;
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_76);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_26);
return x_86;
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; 
x_87 = 0;
x_88 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_89 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_90 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9(x_75, x_87, x_88, x_89, x_2, x_3, x_4, x_76, x_6, x_26);
lean_dec(x_75);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
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
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
if (lean_is_scalar(x_93)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_93;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_92);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_101 = x_90;
} else {
 lean_dec_ref(x_90);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_91, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_91, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_104 = x_91;
} else {
 lean_dec_ref(x_91);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
if (lean_is_scalar(x_101)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_101;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_100);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_90, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_90, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_109 = x_90;
} else {
 lean_dec_ref(x_90);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_25);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_25);
lean_ctor_set(x_112, 1, x_26);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_25, 0);
x_114 = lean_ctor_get(x_25, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_25);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_26);
return x_116;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_175; 
x_128 = lean_ctor_get(x_20, 0);
x_129 = lean_ctor_get(x_20, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_20);
x_175 = l_Lean_parseImports_x27(x_128, x_19, x_21);
lean_dec(x_19);
lean_dec(x_128);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_129);
x_130 = x_178;
x_131 = x_177;
goto block_174;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_179 = lean_ctor_get(x_175, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
lean_dec(x_175);
x_181 = lean_io_error_to_string(x_179);
x_182 = 3;
x_183 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set_uint8(x_183, sizeof(void*)*1, x_182);
x_184 = lean_array_get_size(x_129);
x_185 = lean_array_push(x_129, x_183);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_130 = x_186;
x_131 = x_180;
goto block_174;
}
block_174:
{
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
x_135 = lean_array_get_size(x_132);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_lt(x_136, x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_138 = l_Lake_Module_recParseImports___closed__2;
if (lean_is_scalar(x_134)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_134;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_133);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_131);
return x_140;
}
else
{
uint8_t x_141; 
x_141 = lean_nat_dec_le(x_135, x_135);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = l_Lake_Module_recParseImports___closed__2;
if (lean_is_scalar(x_134)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_134;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_133);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_131);
return x_144;
}
else
{
size_t x_145; size_t x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_134);
x_145 = 0;
x_146 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_147 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_148 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9(x_132, x_145, x_146, x_147, x_2, x_3, x_4, x_133, x_6, x_131);
lean_dec(x_132);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
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
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
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
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
if (lean_is_scalar(x_151)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_151;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_150);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_148, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_159 = x_148;
} else {
 lean_dec_ref(x_148);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_149, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_149, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_162 = x_149;
} else {
 lean_dec_ref(x_149);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
if (lean_is_scalar(x_159)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_159;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_158);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_148, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_148, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_167 = x_148;
} else {
 lean_dec_ref(x_148);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_169 = lean_ctor_get(x_130, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_130, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_171 = x_130;
} else {
 lean_dec_ref(x_130);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_131);
return x_173;
}
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_187 = !lean_is_exclusive(x_20);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_20);
lean_ctor_set(x_188, 1, x_21);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_20, 0);
x_190 = lean_ctor_get(x_20, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_20);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_21);
return x_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recParseImports___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": bad import '", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_60; 
x_18 = lean_array_uget(x_5, x_7);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_21 = x_8;
} else {
 lean_dec_ref(x_8);
 x_21 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_18);
x_60 = lean_apply_7(x_3, x_18, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_61, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_20);
x_69 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_20, x_68);
lean_dec(x_68);
x_70 = lean_unbox(x_67);
lean_dec(x_67);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_ctor_set(x_62, 1, x_69);
lean_ctor_set(x_62, 0, x_19);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_62);
lean_ctor_set(x_61, 0, x_72);
x_22 = x_61;
x_23 = x_63;
goto block_59;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_inc(x_18);
x_73 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_69, x_18);
lean_ctor_set(x_62, 1, x_73);
lean_ctor_set(x_62, 0, x_19);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_62);
lean_ctor_set(x_61, 0, x_75);
x_22 = x_61;
x_23 = x_63;
goto block_59;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_62, 0);
x_77 = lean_ctor_get(x_62, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_62);
lean_inc(x_20);
x_78 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_20, x_77);
lean_dec(x_77);
x_79 = lean_unbox(x_76);
lean_dec(x_76);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_19);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_61, 0, x_82);
x_22 = x_61;
x_23 = x_63;
goto block_59;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_18);
x_83 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_78, x_18);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_19);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_61, 0, x_86);
x_22 = x_61;
x_23 = x_63;
goto block_59;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_61, 1);
lean_inc(x_87);
lean_dec(x_61);
x_88 = lean_ctor_get(x_62, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_62, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_90 = x_62;
} else {
 lean_dec_ref(x_62);
 x_90 = lean_box(0);
}
lean_inc(x_20);
x_91 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_20, x_89);
lean_dec(x_89);
x_92 = lean_unbox(x_88);
lean_dec(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_19);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_87);
x_22 = x_96;
x_23 = x_63;
goto block_59;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_inc(x_18);
x_97 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_91, x_18);
if (lean_is_scalar(x_90)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_90;
}
lean_ctor_set(x_98, 0, x_19);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_87);
x_22 = x_101;
x_23 = x_63;
goto block_59;
}
}
}
else
{
lean_object* x_102; uint8_t x_103; 
lean_dec(x_19);
x_102 = lean_ctor_get(x_60, 1);
lean_inc(x_102);
lean_dec(x_60);
x_103 = !lean_is_exclusive(x_61);
if (x_103 == 0)
{
x_22 = x_61;
x_23 = x_102;
goto block_59;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_61, 0);
x_105 = lean_ctor_get(x_61, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_61);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_22 = x_106;
x_23 = x_102;
goto block_59;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_60);
if (x_107 == 0)
{
return x_60;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_60, 0);
x_109 = lean_ctor_get(x_60, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_60);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
block_59:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
size_t x_28; size_t x_29; 
x_28 = 1;
x_29 = lean_usize_add(x_7, x_28);
x_7 = x_29;
x_8 = x_25;
x_12 = x_26;
x_14 = x_23;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = 1;
x_35 = lean_usize_add(x_7, x_34);
x_7 = x_35;
x_8 = x_33;
x_12 = x_26;
x_14 = x_23;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = l_Array_take___rarg(x_38, x_37);
lean_dec(x_37);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_41 = lean_string_append(x_40, x_1);
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_dec(x_18);
x_45 = 1;
x_46 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_47 = l_Lean_Name_toString(x_44, x_45, x_46);
x_48 = lean_string_append(x_43, x_47);
lean_dec(x_47);
x_49 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4;
x_50 = lean_string_append(x_48, x_49);
x_51 = 3;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_array_push(x_39, x_52);
x_54 = lean_box(x_45);
if (lean_is_scalar(x_21)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_21;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_20);
x_56 = 1;
x_57 = lean_usize_add(x_7, x_56);
x_7 = x_57;
x_8 = x_55;
x_12 = x_53;
x_14 = x_23;
goto _start;
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
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = lean_array_size(x_2);
x_12 = 0;
x_13 = lean_array_get_size(x_7);
x_14 = l_Lake_collectImportsAux___closed__1;
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3(x_1, x_2, x_3, x_10, x_2, x_11, x_12, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_ctor_set(x_16, 0, x_25);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_32 = x_16;
} else {
 lean_dec_ref(x_16);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_17);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_15, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_16, 0);
lean_dec(x_40);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_13);
return x_15;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_13);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_15, 0, x_42);
return x_15;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_dec(x_15);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_45 = x_16;
} else {
 lean_dec_ref(x_16);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_15, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_16);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_16, 0);
lean_dec(x_51);
lean_ctor_set(x_16, 0, x_13);
return x_15;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_dec(x_16);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_15, 0, x_53);
return x_15;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_dec(x_15);
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
lean_ctor_set(x_57, 0, x_13);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_13);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("transImports", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_recParseImports___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_59; lean_object* x_60; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_17 = lean_array_uget(x_4, x_6);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_20 = x_7;
} else {
 lean_dec_ref(x_7);
 x_20 = lean_box(0);
}
x_105 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_17);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_17);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_107 = lean_apply_6(x_8, x_106, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_108, 0);
x_112 = 1;
x_113 = lean_box(x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
lean_ctor_set(x_108, 0, x_114);
x_59 = x_108;
x_60 = x_109;
goto block_104;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_108, 0);
x_116 = lean_ctor_get(x_108, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_108);
x_117 = 1;
x_118 = lean_box(x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_116);
x_59 = x_120;
x_60 = x_109;
goto block_104;
}
}
else
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_107, 1);
lean_inc(x_121);
lean_dec(x_107);
x_122 = !lean_is_exclusive(x_108);
if (x_122 == 0)
{
x_59 = x_108;
x_60 = x_121;
goto block_104;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_108, 0);
x_124 = lean_ctor_get(x_108, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_108);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_59 = x_125;
x_60 = x_121;
goto block_104;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_126 = !lean_is_exclusive(x_107);
if (x_126 == 0)
{
return x_107;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_107, 0);
x_128 = lean_ctor_get(x_107, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_107);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
block_58:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
size_t x_27; size_t x_28; 
x_27 = 1;
x_28 = lean_usize_add(x_6, x_27);
x_6 = x_28;
x_7 = x_24;
x_11 = x_25;
x_13 = x_22;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = 1;
x_34 = lean_usize_add(x_6, x_33);
x_6 = x_34;
x_7 = x_32;
x_11 = x_25;
x_13 = x_22;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; 
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = l_Array_take___rarg(x_37, x_36);
lean_dec(x_36);
x_39 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_40 = lean_string_append(x_39, x_2);
x_41 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_dec(x_17);
x_44 = 1;
x_45 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_46 = l_Lean_Name_toString(x_43, x_44, x_45);
x_47 = lean_string_append(x_42, x_46);
lean_dec(x_46);
x_48 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4;
x_49 = lean_string_append(x_47, x_48);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_push(x_38, x_51);
x_53 = lean_box(x_44);
if (lean_is_scalar(x_20)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_20;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_19);
x_55 = 1;
x_56 = lean_usize_add(x_6, x_55);
x_6 = x_56;
x_7 = x_54;
x_11 = x_52;
x_13 = x_22;
goto _start;
}
}
block_104:
{
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_19);
x_66 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_19, x_65);
lean_dec(x_65);
x_67 = lean_unbox(x_64);
lean_dec(x_64);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_ctor_set(x_62, 1, x_66);
lean_ctor_set(x_62, 0, x_18);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_62);
lean_ctor_set(x_59, 0, x_69);
x_21 = x_59;
x_22 = x_60;
goto block_58;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_inc(x_17);
x_70 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_66, x_17);
lean_ctor_set(x_62, 1, x_70);
lean_ctor_set(x_62, 0, x_18);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_62);
lean_ctor_set(x_59, 0, x_72);
x_21 = x_59;
x_22 = x_60;
goto block_58;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_62, 0);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_62);
lean_inc(x_19);
x_75 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_19, x_74);
lean_dec(x_74);
x_76 = lean_unbox(x_73);
lean_dec(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_18);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_59, 0, x_79);
x_21 = x_59;
x_22 = x_60;
goto block_58;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_17);
x_80 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_75, x_17);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_18);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_59, 0, x_83);
x_21 = x_59;
x_22 = x_60;
goto block_58;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_84 = lean_ctor_get(x_59, 0);
x_85 = lean_ctor_get(x_59, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_59);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_88 = x_84;
} else {
 lean_dec_ref(x_84);
 x_88 = lean_box(0);
}
lean_inc(x_19);
x_89 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_19, x_87);
lean_dec(x_87);
x_90 = lean_unbox(x_86);
lean_dec(x_86);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_18);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_85);
x_21 = x_94;
x_22 = x_60;
goto block_58;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_inc(x_17);
x_95 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_89, x_17);
if (lean_is_scalar(x_88)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_88;
}
lean_ctor_set(x_96, 0, x_18);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_85);
x_21 = x_99;
x_22 = x_60;
goto block_58;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_18);
x_100 = !lean_is_exclusive(x_59);
if (x_100 == 0)
{
x_21 = x_59;
x_22 = x_60;
goto block_58;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_59, 0);
x_102 = lean_ctor_get(x_59, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_59);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_21 = x_103;
x_22 = x_60;
goto block_58;
}
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
lean_inc(x_6);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 7);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_System_FilePath_join(x_17, x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_System_FilePath_join(x_20, x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lake_Module_recParseImports___closed__1;
x_26 = l_Lean_modToFilePath(x_23, x_24, x_25);
lean_dec(x_24);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = lean_array_size(x_13);
x_29 = 0;
x_30 = lean_array_get_size(x_14);
x_31 = l_Lake_collectImportsAux___closed__1;
x_32 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1(x_13, x_26, x_27, x_13, x_28, x_29, x_31, x_2, x_3, x_4, x_14, x_6, x_12);
lean_dec(x_26);
lean_dec(x_13);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_30);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_32, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_ctor_set(x_33, 0, x_42);
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_32, 0, x_46);
return x_32;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_dec(x_32);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_49 = x_33;
} else {
 lean_dec_ref(x_33);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_dec(x_34);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_34);
x_54 = !lean_is_exclusive(x_32);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_32, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_33);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_33, 0);
lean_dec(x_57);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_30);
return x_32;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
lean_dec(x_33);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_30);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_32, 0, x_59);
return x_32;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_32, 1);
lean_inc(x_60);
lean_dec(x_32);
x_61 = lean_ctor_get(x_33, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_62 = x_33;
} else {
 lean_dec_ref(x_33);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_30);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_32);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_32, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_33);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_33, 0);
lean_dec(x_68);
lean_ctor_set(x_33, 0, x_30);
return x_32;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_33, 1);
lean_inc(x_69);
lean_dec(x_33);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_30);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_32, 0, x_70);
return x_32;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_32, 1);
lean_inc(x_71);
lean_dec(x_32);
x_72 = lean_ctor_get(x_33, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_73 = x_33;
} else {
 lean_dec_ref(x_33);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_30);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_30);
x_76 = !lean_is_exclusive(x_32);
if (x_76 == 0)
{
return x_32;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_32, 0);
x_78 = lean_ctor_get(x_32, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_32);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_10);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_10, 0);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_11);
if (x_82 == 0)
{
return x_10;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_11, 0);
x_84 = lean_ctor_get(x_11, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_11);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_10, 0, x_85);
return x_10;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_10, 1);
lean_inc(x_86);
lean_dec(x_10);
x_87 = lean_ctor_get(x_11, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_11, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_89 = x_11;
} else {
 lean_dec_ref(x_11);
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_10);
if (x_92 == 0)
{
return x_10;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_10, 0);
x_94 = lean_ctor_get(x_10, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_10);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precompileImports", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_recParseImports___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_92; lean_object* x_93; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_17 = lean_array_uget(x_4, x_6);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_29 = x_7;
} else {
 lean_dec_ref(x_7);
 x_29 = lean_box(0);
}
x_138 = lean_ctor_get(x_17, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 2);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_ctor_get_uint8(x_140, sizeof(void*)*29);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
lean_dec(x_138);
x_143 = lean_ctor_get_uint8(x_142, sizeof(void*)*9);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
lean_inc(x_17);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_17);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_146 = lean_apply_6(x_8, x_145, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_147, 0);
x_151 = 0;
x_152 = lean_box(x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_150);
lean_ctor_set(x_147, 0, x_153);
x_92 = x_147;
x_93 = x_148;
goto block_137;
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_147, 0);
x_155 = lean_ctor_get(x_147, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_147);
x_156 = 0;
x_157 = lean_box(x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_154);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_155);
x_92 = x_159;
x_93 = x_148;
goto block_137;
}
}
else
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_146, 1);
lean_inc(x_160);
lean_dec(x_146);
x_161 = !lean_is_exclusive(x_147);
if (x_161 == 0)
{
x_92 = x_147;
x_93 = x_160;
goto block_137;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_147, 0);
x_163 = lean_ctor_get(x_147, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_147);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_92 = x_164;
x_93 = x_160;
goto block_137;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_165 = !lean_is_exclusive(x_146);
if (x_165 == 0)
{
return x_146;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_146, 0);
x_167 = lean_ctor_get(x_146, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_146);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_17);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_17);
lean_ctor_set(x_170, 1, x_169);
lean_inc(x_8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_171 = lean_apply_6(x_8, x_170, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = !lean_is_exclusive(x_172);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_172, 0);
x_176 = 1;
x_177 = lean_box(x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_172, 0, x_178);
x_92 = x_172;
x_93 = x_173;
goto block_137;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_179 = lean_ctor_get(x_172, 0);
x_180 = lean_ctor_get(x_172, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_172);
x_181 = 1;
x_182 = lean_box(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_179);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_180);
x_92 = x_184;
x_93 = x_173;
goto block_137;
}
}
else
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_171, 1);
lean_inc(x_185);
lean_dec(x_171);
x_186 = !lean_is_exclusive(x_172);
if (x_186 == 0)
{
x_92 = x_172;
x_93 = x_185;
goto block_137;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_172, 0);
x_188 = lean_ctor_get(x_172, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_172);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_92 = x_189;
x_93 = x_185;
goto block_137;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_190 = !lean_is_exclusive(x_171);
if (x_190 == 0)
{
return x_171;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_171, 0);
x_192 = lean_ctor_get(x_171, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_171);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_138);
x_194 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_17);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_17);
lean_ctor_set(x_195, 1, x_194);
lean_inc(x_8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_196 = lean_apply_6(x_8, x_195, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = !lean_is_exclusive(x_197);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_197, 0);
x_201 = 1;
x_202 = lean_box(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_200);
lean_ctor_set(x_197, 0, x_203);
x_92 = x_197;
x_93 = x_198;
goto block_137;
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_204 = lean_ctor_get(x_197, 0);
x_205 = lean_ctor_get(x_197, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_197);
x_206 = 1;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_204);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_205);
x_92 = x_209;
x_93 = x_198;
goto block_137;
}
}
else
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_196, 1);
lean_inc(x_210);
lean_dec(x_196);
x_211 = !lean_is_exclusive(x_197);
if (x_211 == 0)
{
x_92 = x_197;
x_93 = x_210;
goto block_137;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_197, 0);
x_213 = lean_ctor_get(x_197, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_197);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_92 = x_214;
x_93 = x_210;
goto block_137;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_215 = !lean_is_exclusive(x_196);
if (x_215 == 0)
{
return x_196;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_196, 0);
x_217 = lean_ctor_get(x_196, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_196);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_6, x_23);
x_6 = x_24;
x_7 = x_22;
x_11 = x_21;
x_13 = x_19;
goto _start;
}
block_91:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_17);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_30, 0, x_37);
x_18 = x_30;
x_19 = x_31;
goto block_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_30, 0, x_41);
x_18 = x_30;
x_19 = x_31;
goto block_26;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_45 = x_33;
} else {
 lean_dec_ref(x_33);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
x_18 = x_48;
x_19 = x_31;
goto block_26;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
x_52 = l_Array_take___rarg(x_51, x_50);
lean_dec(x_50);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_54 = lean_string_append(x_53, x_1);
x_55 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_ctor_get(x_17, 1);
lean_inc(x_57);
lean_dec(x_17);
x_58 = 1;
x_59 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_60 = l_Lean_Name_toString(x_57, x_58, x_59);
x_61 = lean_string_append(x_56, x_60);
lean_dec(x_60);
x_62 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4;
x_63 = lean_string_append(x_61, x_62);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_push(x_52, x_65);
x_67 = lean_box(x_58);
if (lean_is_scalar(x_29)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_29;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_28);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 1, x_66);
lean_ctor_set(x_30, 0, x_69);
x_18 = x_30;
x_19 = x_31;
goto block_26;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_70 = lean_ctor_get(x_30, 0);
x_71 = lean_ctor_get(x_30, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_30);
x_72 = l_Array_take___rarg(x_71, x_70);
lean_dec(x_70);
x_73 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_74 = lean_string_append(x_73, x_1);
x_75 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_76 = lean_string_append(x_74, x_75);
x_77 = lean_ctor_get(x_17, 1);
lean_inc(x_77);
lean_dec(x_17);
x_78 = 1;
x_79 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_80 = l_Lean_Name_toString(x_77, x_78, x_79);
x_81 = lean_string_append(x_76, x_80);
lean_dec(x_80);
x_82 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4;
x_83 = lean_string_append(x_81, x_82);
x_84 = 3;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = lean_array_push(x_72, x_85);
x_87 = lean_box(x_78);
if (lean_is_scalar(x_29)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_29;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_28);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
x_18 = x_90;
x_19 = x_31;
goto block_26;
}
}
}
block_137:
{
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_28);
x_99 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_28, x_98);
lean_dec(x_98);
x_100 = lean_unbox(x_97);
lean_dec(x_97);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_ctor_set(x_95, 1, x_99);
lean_ctor_set(x_95, 0, x_27);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_95);
lean_ctor_set(x_92, 0, x_102);
x_30 = x_92;
x_31 = x_93;
goto block_91;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_inc(x_17);
x_103 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_99, x_17);
lean_ctor_set(x_95, 1, x_103);
lean_ctor_set(x_95, 0, x_27);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
lean_ctor_set(x_92, 0, x_105);
x_30 = x_92;
x_31 = x_93;
goto block_91;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_95, 0);
x_107 = lean_ctor_get(x_95, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_95);
lean_inc(x_28);
x_108 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_28, x_107);
lean_dec(x_107);
x_109 = lean_unbox(x_106);
lean_dec(x_106);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_27);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_92, 0, x_112);
x_30 = x_92;
x_31 = x_93;
goto block_91;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_inc(x_17);
x_113 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_108, x_17);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_27);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_92, 0, x_116);
x_30 = x_92;
x_31 = x_93;
goto block_91;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_117 = lean_ctor_get(x_92, 0);
x_118 = lean_ctor_get(x_92, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_92);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
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
lean_inc(x_28);
x_122 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_28, x_120);
lean_dec(x_120);
x_123 = lean_unbox(x_119);
lean_dec(x_119);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_27);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_118);
x_30 = x_127;
x_31 = x_93;
goto block_91;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_inc(x_17);
x_128 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_122, x_17);
if (lean_is_scalar(x_121)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_121;
}
lean_ctor_set(x_129, 0, x_27);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_118);
x_30 = x_132;
x_31 = x_93;
goto block_91;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_27);
x_133 = !lean_is_exclusive(x_92);
if (x_133 == 0)
{
x_30 = x_92;
x_31 = x_93;
goto block_91;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_92, 0);
x_135 = lean_ctor_get(x_92, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_92);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_30 = x_136;
x_31 = x_93;
goto block_91;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computePrecompileImportsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_box(0);
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = lean_array_get_size(x_6);
x_13 = l_Lake_collectImportsAux___closed__1;
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1(x_1, x_2, x_9, x_2, x_10, x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_31 = x_15;
} else {
 lean_dec_ref(x_15);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_16);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_14, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_15, 0);
lean_dec(x_39);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_12);
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_12);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_14, 0, x_41);
return x_14;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_dec(x_14);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_44 = x_15;
} else {
 lean_dec_ref(x_15);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_14, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_15);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_15, 0);
lean_dec(x_50);
lean_ctor_set(x_15, 0, x_12);
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_15, 1);
lean_inc(x_51);
lean_dec(x_15);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_14, 0, x_52);
return x_14;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
lean_dec(x_14);
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_55 = x_15;
} else {
 lean_dec_ref(x_15);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_12);
x_58 = !lean_is_exclusive(x_14);
if (x_58 == 0)
{
return x_14;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_14, 0);
x_60 = lean_ctor_get(x_14, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_14);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_92; lean_object* x_93; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_17 = lean_array_uget(x_4, x_6);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_29 = x_7;
} else {
 lean_dec_ref(x_7);
 x_29 = lean_box(0);
}
x_138 = lean_ctor_get(x_17, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 2);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_ctor_get_uint8(x_140, sizeof(void*)*29);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
lean_dec(x_138);
x_143 = lean_ctor_get_uint8(x_142, sizeof(void*)*9);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
lean_inc(x_17);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_17);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_146 = lean_apply_6(x_8, x_145, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_147, 0);
x_151 = 0;
x_152 = lean_box(x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_150);
lean_ctor_set(x_147, 0, x_153);
x_92 = x_147;
x_93 = x_148;
goto block_137;
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_147, 0);
x_155 = lean_ctor_get(x_147, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_147);
x_156 = 0;
x_157 = lean_box(x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_154);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_155);
x_92 = x_159;
x_93 = x_148;
goto block_137;
}
}
else
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_146, 1);
lean_inc(x_160);
lean_dec(x_146);
x_161 = !lean_is_exclusive(x_147);
if (x_161 == 0)
{
x_92 = x_147;
x_93 = x_160;
goto block_137;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_147, 0);
x_163 = lean_ctor_get(x_147, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_147);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_92 = x_164;
x_93 = x_160;
goto block_137;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_165 = !lean_is_exclusive(x_146);
if (x_165 == 0)
{
return x_146;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_146, 0);
x_167 = lean_ctor_get(x_146, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_146);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_17);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_17);
lean_ctor_set(x_170, 1, x_169);
lean_inc(x_8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_171 = lean_apply_6(x_8, x_170, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = !lean_is_exclusive(x_172);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_172, 0);
x_176 = 1;
x_177 = lean_box(x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_172, 0, x_178);
x_92 = x_172;
x_93 = x_173;
goto block_137;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_179 = lean_ctor_get(x_172, 0);
x_180 = lean_ctor_get(x_172, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_172);
x_181 = 1;
x_182 = lean_box(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_179);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_180);
x_92 = x_184;
x_93 = x_173;
goto block_137;
}
}
else
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_171, 1);
lean_inc(x_185);
lean_dec(x_171);
x_186 = !lean_is_exclusive(x_172);
if (x_186 == 0)
{
x_92 = x_172;
x_93 = x_185;
goto block_137;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_172, 0);
x_188 = lean_ctor_get(x_172, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_172);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_92 = x_189;
x_93 = x_185;
goto block_137;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_190 = !lean_is_exclusive(x_171);
if (x_190 == 0)
{
return x_171;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_171, 0);
x_192 = lean_ctor_get(x_171, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_171);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_138);
x_194 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_17);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_17);
lean_ctor_set(x_195, 1, x_194);
lean_inc(x_8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
x_196 = lean_apply_6(x_8, x_195, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = !lean_is_exclusive(x_197);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_197, 0);
x_201 = 1;
x_202 = lean_box(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_200);
lean_ctor_set(x_197, 0, x_203);
x_92 = x_197;
x_93 = x_198;
goto block_137;
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_204 = lean_ctor_get(x_197, 0);
x_205 = lean_ctor_get(x_197, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_197);
x_206 = 1;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_204);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_205);
x_92 = x_209;
x_93 = x_198;
goto block_137;
}
}
else
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_196, 1);
lean_inc(x_210);
lean_dec(x_196);
x_211 = !lean_is_exclusive(x_197);
if (x_211 == 0)
{
x_92 = x_197;
x_93 = x_210;
goto block_137;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_197, 0);
x_213 = lean_ctor_get(x_197, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_197);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_92 = x_214;
x_93 = x_210;
goto block_137;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_215 = !lean_is_exclusive(x_196);
if (x_215 == 0)
{
return x_196;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_196, 0);
x_217 = lean_ctor_get(x_196, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_196);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_6, x_23);
x_6 = x_24;
x_7 = x_22;
x_11 = x_21;
x_13 = x_19;
goto _start;
}
block_91:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_17);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_30, 0, x_37);
x_18 = x_30;
x_19 = x_31;
goto block_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_30, 0, x_41);
x_18 = x_30;
x_19 = x_31;
goto block_26;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_45 = x_33;
} else {
 lean_dec_ref(x_33);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
x_18 = x_48;
x_19 = x_31;
goto block_26;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
x_52 = l_Array_take___rarg(x_51, x_50);
lean_dec(x_50);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_54 = lean_string_append(x_53, x_2);
x_55 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_ctor_get(x_17, 1);
lean_inc(x_57);
lean_dec(x_17);
x_58 = 1;
x_59 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_60 = l_Lean_Name_toString(x_57, x_58, x_59);
x_61 = lean_string_append(x_56, x_60);
lean_dec(x_60);
x_62 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4;
x_63 = lean_string_append(x_61, x_62);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_push(x_52, x_65);
x_67 = lean_box(x_58);
if (lean_is_scalar(x_29)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_29;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_28);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 1, x_66);
lean_ctor_set(x_30, 0, x_69);
x_18 = x_30;
x_19 = x_31;
goto block_26;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_70 = lean_ctor_get(x_30, 0);
x_71 = lean_ctor_get(x_30, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_30);
x_72 = l_Array_take___rarg(x_71, x_70);
lean_dec(x_70);
x_73 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_74 = lean_string_append(x_73, x_2);
x_75 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2;
x_76 = lean_string_append(x_74, x_75);
x_77 = lean_ctor_get(x_17, 1);
lean_inc(x_77);
lean_dec(x_17);
x_78 = 1;
x_79 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
x_80 = l_Lean_Name_toString(x_77, x_78, x_79);
x_81 = lean_string_append(x_76, x_80);
lean_dec(x_80);
x_82 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4;
x_83 = lean_string_append(x_81, x_82);
x_84 = 3;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = lean_array_push(x_72, x_85);
x_87 = lean_box(x_78);
if (lean_is_scalar(x_29)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_29;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_28);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
x_18 = x_90;
x_19 = x_31;
goto block_26;
}
}
}
block_137:
{
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_28);
x_99 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_28, x_98);
lean_dec(x_98);
x_100 = lean_unbox(x_97);
lean_dec(x_97);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_ctor_set(x_95, 1, x_99);
lean_ctor_set(x_95, 0, x_27);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_95);
lean_ctor_set(x_92, 0, x_102);
x_30 = x_92;
x_31 = x_93;
goto block_91;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_inc(x_17);
x_103 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_99, x_17);
lean_ctor_set(x_95, 1, x_103);
lean_ctor_set(x_95, 0, x_27);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
lean_ctor_set(x_92, 0, x_105);
x_30 = x_92;
x_31 = x_93;
goto block_91;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_95, 0);
x_107 = lean_ctor_get(x_95, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_95);
lean_inc(x_28);
x_108 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_28, x_107);
lean_dec(x_107);
x_109 = lean_unbox(x_106);
lean_dec(x_106);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_27);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_92, 0, x_112);
x_30 = x_92;
x_31 = x_93;
goto block_91;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_inc(x_17);
x_113 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_108, x_17);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_27);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_92, 0, x_116);
x_30 = x_92;
x_31 = x_93;
goto block_91;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_117 = lean_ctor_get(x_92, 0);
x_118 = lean_ctor_get(x_92, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_92);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
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
lean_inc(x_28);
x_122 = l_Lake_OrdHashSet_appendArray___at_Lake_collectImportsAux___spec__1(x_28, x_120);
lean_dec(x_120);
x_123 = lean_unbox(x_119);
lean_dec(x_119);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_27);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_118);
x_30 = x_127;
x_31 = x_93;
goto block_91;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_inc(x_17);
x_128 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_122, x_17);
if (lean_is_scalar(x_121)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_121;
}
lean_ctor_set(x_129, 0, x_27);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_118);
x_30 = x_132;
x_31 = x_93;
goto block_91;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_27);
x_133 = !lean_is_exclusive(x_92);
if (x_133 == 0)
{
x_30 = x_92;
x_31 = x_93;
goto block_91;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_92, 0);
x_135 = lean_ctor_get(x_92, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_92);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_30 = x_136;
x_31 = x_93;
goto block_91;
}
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
lean_inc(x_6);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 7);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_System_FilePath_join(x_17, x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_System_FilePath_join(x_20, x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lake_Module_recParseImports___closed__1;
x_26 = l_Lean_modToFilePath(x_23, x_24, x_25);
lean_dec(x_24);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = lean_array_size(x_13);
x_29 = 0;
x_30 = lean_array_get_size(x_14);
x_31 = l_Lake_collectImportsAux___closed__1;
x_32 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1(x_13, x_26, x_27, x_13, x_28, x_29, x_31, x_2, x_3, x_4, x_14, x_6, x_12);
lean_dec(x_26);
lean_dec(x_13);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_30);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_32, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_ctor_set(x_33, 0, x_42);
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_32, 0, x_46);
return x_32;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_dec(x_32);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_49 = x_33;
} else {
 lean_dec_ref(x_33);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_dec(x_34);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_34);
x_54 = !lean_is_exclusive(x_32);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_32, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_33);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_33, 0);
lean_dec(x_57);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_30);
return x_32;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
lean_dec(x_33);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_30);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_32, 0, x_59);
return x_32;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_32, 1);
lean_inc(x_60);
lean_dec(x_32);
x_61 = lean_ctor_get(x_33, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_62 = x_33;
} else {
 lean_dec_ref(x_33);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_30);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_32);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_32, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_33);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_33, 0);
lean_dec(x_68);
lean_ctor_set(x_33, 0, x_30);
return x_32;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_33, 1);
lean_inc(x_69);
lean_dec(x_33);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_30);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_32, 0, x_70);
return x_32;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_32, 1);
lean_inc(x_71);
lean_dec(x_32);
x_72 = lean_ctor_get(x_33, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_73 = x_33;
} else {
 lean_dec_ref(x_33);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_30);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_30);
x_76 = !lean_is_exclusive(x_32);
if (x_76 == 0)
{
return x_32;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_32, 0);
x_78 = lean_ctor_get(x_32, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_32);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_10);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_10, 0);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_11);
if (x_82 == 0)
{
return x_10;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_11, 0);
x_84 = lean_ctor_get(x_11, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_11);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_10, 0, x_85);
return x_10;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_10, 1);
lean_inc(x_86);
lean_dec(x_10);
x_87 = lean_ctor_get(x_11, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_11, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_89 = x_11;
} else {
 lean_dec_ref(x_11);
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_10);
if (x_92 == 0)
{
return x_10;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_10, 0);
x_94 = lean_ctor_get(x_10, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_10);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputePrecompileImports___spec__1(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
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
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_9);
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
lean_inc(x_10);
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
x_9 = x_26;
x_11 = x_24;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_10);
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
lean_dec(x_10);
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
x_57 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_58 = lean_string_append(x_57, x_56);
lean_dec(x_56);
x_59 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___closed__1;
x_60 = lean_string_append(x_58, x_59);
x_61 = 3;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_array_push(x_9, x_62);
x_64 = lean_box(0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_65 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1(x_15, x_64, x_6, x_7, x_8, x_63, x_10, x_11);
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
x_9 = x_69;
x_11 = x_67;
goto _start;
}
else
{
uint8_t x_74; 
lean_dec(x_17);
lean_dec(x_10);
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
lean_dec(x_10);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_7);
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
lean_inc(x_8);
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
x_7 = x_22;
x_9 = x_20;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_8);
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
lean_dec(x_8);
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
lean_dec(x_6);
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
x_5 = l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
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
x_8 = l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__7(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recBuildDeps___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recBuildDeps___spec__10___at_Lake_Module_recBuildDeps___spec__11(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recBuildDeps___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_Module_recBuildDeps___spec__10___at_Lake_Module_recBuildDeps___spec__11(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recBuildDeps___spec__8(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_Module_recBuildDeps___spec__9(x_7, x_1, x_6);
return x_8;
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
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__7(x_2, x_22);
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
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recBuildDeps___spec__8(x_30);
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
x_58 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__7(x_2, x_57);
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
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_Module_recBuildDeps___spec__8(x_65);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
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
x_14 = lean_apply_7(x_2, x_12, x_3, x_4, x_5, x_13, x_7, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
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
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(x_1, x_10, x_9);
lean_dec(x_9);
x_12 = l_Array_append___rarg(x_2, x_11);
lean_dec(x_11);
x_13 = lean_array_to_list(x_12);
x_14 = lean_array_size(x_1);
x_15 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_14, x_3, x_1);
x_16 = lean_array_size(x_4);
x_17 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_16, x_3, x_4);
x_18 = l_Array_append___rarg(x_15, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_11, 8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_13, 2);
x_15 = lean_ctor_get(x_14, 1);
x_16 = lean_ctor_get(x_15, 8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = l_Lake_BuildTrace_mix(x_18, x_5);
lean_ctor_set(x_8, 1, x_19);
x_20 = lean_box(0);
x_21 = l_Lake_Module_recBuildDeps___lambda__1(x_6, x_1, x_2, x_3, x_20, x_7, x_8, x_9);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_22);
lean_dec(x_8);
x_25 = l_Lake_BuildTrace_mix(x_24, x_5);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_23);
x_27 = lean_box(0);
x_28 = l_Lake_Module_recBuildDeps___lambda__1(x_6, x_1, x_2, x_3, x_27, x_7, x_26, x_9);
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
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_8, 1);
x_33 = l_Lake_BuildTrace_mix(x_32, x_5);
x_34 = l_Lake_Module_recBuildDeps___lambda__2___closed__3;
x_35 = l_Lake_BuildTrace_mix(x_33, x_34);
lean_ctor_set(x_8, 1, x_35);
x_36 = lean_box(0);
x_37 = l_Lake_Module_recBuildDeps___lambda__1(x_6, x_1, x_2, x_3, x_36, x_7, x_8, x_9);
return x_37;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_inc(x_38);
lean_dec(x_8);
x_41 = l_Lake_BuildTrace_mix(x_40, x_5);
x_42 = l_Lake_Module_recBuildDeps___lambda__2___closed__3;
x_43 = l_Lake_BuildTrace_mix(x_41, x_42);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_39);
x_45 = lean_box(0);
x_46 = l_Lake_Module_recBuildDeps___lambda__1(x_6, x_1, x_2, x_3, x_45, x_7, x_44, x_9);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_8, 1);
lean_dec(x_48);
lean_ctor_set(x_8, 1, x_5);
x_49 = lean_box(0);
x_50 = l_Lake_Module_recBuildDeps___lambda__1(x_6, x_1, x_2, x_3, x_49, x_7, x_8, x_9);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_8, 0);
x_52 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
lean_inc(x_51);
lean_dec(x_8);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_5);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_52);
x_54 = lean_box(0);
x_55 = l_Lake_Module_recBuildDeps___lambda__1(x_6, x_1, x_2, x_3, x_54, x_7, x_53, x_9);
return x_55;
}
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_8);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_8, 1);
x_60 = l_Lake_BuildTrace_mix(x_59, x_5);
x_61 = l_Lake_Module_recBuildDeps___lambda__2___closed__3;
x_62 = l_Lake_BuildTrace_mix(x_60, x_61);
lean_ctor_set(x_8, 1, x_62);
x_63 = lean_box(0);
x_64 = l_Lake_Module_recBuildDeps___lambda__1(x_6, x_1, x_2, x_3, x_63, x_7, x_8, x_9);
return x_64;
}
else
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_8, 0);
x_66 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
lean_inc(x_65);
lean_dec(x_8);
x_68 = l_Lake_BuildTrace_mix(x_67, x_5);
x_69 = l_Lake_Module_recBuildDeps___lambda__2___closed__3;
x_70 = l_Lake_BuildTrace_mix(x_68, x_69);
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_66);
x_72 = lean_box(0);
x_73 = l_Lake_Module_recBuildDeps___lambda__1(x_6, x_1, x_2, x_3, x_72, x_7, x_71, x_9);
return x_73;
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_8);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_8, 1);
lean_dec(x_75);
lean_ctor_set(x_8, 1, x_5);
x_76 = lean_box(0);
x_77 = l_Lake_Module_recBuildDeps___lambda__1(x_6, x_1, x_2, x_3, x_76, x_7, x_8, x_9);
return x_77;
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_8, 0);
x_79 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
lean_inc(x_78);
lean_dec(x_8);
x_80 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_5);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_79);
x_81 = lean_box(0);
x_82 = l_Lake_Module_recBuildDeps___lambda__1(x_6, x_1, x_2, x_3, x_81, x_7, x_80, x_9);
return x_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_box_usize(x_2);
x_11 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2___boxed), 9, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = l_Task_Priority_default;
x_14 = 0;
x_15 = l_Lake_Job_mapM___rarg(x_5, x_11, x_13, x_14, x_7, x_12, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
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
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lake_BuildTrace_nil;
lean_ctor_set(x_8, 1, x_12);
x_13 = lean_box_usize(x_2);
x_14 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__3___boxed), 9, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_11);
lean_closure_set(x_14, 4, x_4);
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = l_Lake_Job_bindM___rarg(x_5, x_14, x_15, x_16, x_7, x_12, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_8);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_29);
lean_dec(x_8);
x_32 = l_Lake_BuildTrace_nil;
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_30);
x_34 = lean_box_usize(x_2);
x_35 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__3___boxed), 9, 5);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_34);
lean_closure_set(x_35, 2, x_3);
lean_closure_set(x_35, 3, x_31);
lean_closure_set(x_35, 4, x_4);
x_36 = l_Task_Priority_default;
x_37 = 0;
x_38 = l_Lake_Job_bindM___rarg(x_5, x_35, x_36, x_37, x_7, x_32, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_33);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_33);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_box_usize(x_2);
x_12 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__4___boxed), 9, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = l_Task_Priority_default;
x_15 = 0;
x_16 = l_Lake_Job_bindM___rarg(x_6, x_12, x_14, x_15, x_8, x_13, x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; lean_object* x_13; 
x_12 = lean_array_size(x_5);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(x_12, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_83 = lean_array_get_size(x_5);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_lt(x_84, x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_83);
lean_dec(x_5);
x_86 = lean_ctor_get(x_2, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 2);
lean_inc(x_87);
x_88 = lean_ctor_get_uint8(x_87, sizeof(void*)*29);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
x_90 = lean_ctor_get_uint8(x_89, sizeof(void*)*9);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_86);
x_91 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_18 = x_91;
goto block_82;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_93 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_92, x_86);
x_18 = x_93;
goto block_82;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_95 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_94, x_86);
x_18 = x_95;
goto block_82;
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_2, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 2);
lean_inc(x_97);
x_98 = lean_ctor_get_uint8(x_97, sizeof(void*)*29);
lean_dec(x_97);
x_99 = lean_nat_dec_le(x_83, x_83);
if (x_99 == 0)
{
lean_dec(x_83);
lean_dec(x_5);
if (x_98 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_2, 1);
lean_inc(x_100);
x_101 = lean_ctor_get_uint8(x_100, sizeof(void*)*9);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_96);
x_102 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_18 = x_102;
goto block_82;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_104 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_103, x_96);
x_18 = x_104;
goto block_82;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_106 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_105, x_96);
x_18 = x_106;
goto block_82;
}
}
else
{
size_t x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_108 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_109 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__12(x_5, x_1, x_107, x_108);
lean_dec(x_5);
if (x_98 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_2, 1);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_110, sizeof(void*)*9);
lean_dec(x_110);
if (x_111 == 0)
{
lean_dec(x_96);
x_18 = x_109;
goto block_82;
}
else
{
lean_object* x_112; 
x_112 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_109, x_96);
x_18 = x_112;
goto block_82;
}
}
else
{
lean_object* x_113; 
x_113 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_109, x_96);
x_18 = x_113;
goto block_82;
}
}
}
block_82:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_8);
x_20 = l_Lake_recBuildExternDynlibs(x_19, x_6, x_7, x_8, x_17, x_10, x_15);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_21, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lake_Job_collectArray___rarg(x_27);
lean_dec(x_27);
x_30 = l_Lake_Job_collectArray___rarg(x_16);
lean_dec(x_16);
x_31 = lean_box_usize(x_1);
x_32 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 10, 6);
lean_closure_set(x_32, 0, x_28);
lean_closure_set(x_32, 1, x_31);
lean_closure_set(x_32, 2, x_2);
lean_closure_set(x_32, 3, x_29);
lean_closure_set(x_32, 4, x_30);
lean_closure_set(x_32, 5, x_3);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = l_Lake_BuildTrace_nil;
x_36 = l_Lake_Job_bindM___rarg(x_4, x_32, x_33, x_34, x_8, x_35, x_23);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_21, 0, x_38);
lean_ctor_set(x_36, 0, x_21);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_21, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_21);
lean_dec(x_25);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_dec(x_22);
x_49 = l_Lake_Job_collectArray___rarg(x_47);
lean_dec(x_47);
x_50 = l_Lake_Job_collectArray___rarg(x_16);
lean_dec(x_16);
x_51 = lean_box_usize(x_1);
x_52 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 10, 6);
lean_closure_set(x_52, 0, x_48);
lean_closure_set(x_52, 1, x_51);
lean_closure_set(x_52, 2, x_2);
lean_closure_set(x_52, 3, x_49);
lean_closure_set(x_52, 4, x_50);
lean_closure_set(x_52, 5, x_3);
x_53 = l_Task_Priority_default;
x_54 = 0;
x_55 = l_Lake_BuildTrace_nil;
x_56 = l_Lake_Job_bindM___rarg(x_4, x_52, x_53, x_54, x_8, x_55, x_23);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
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
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_46);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_46);
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_20);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_20, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_21);
if (x_68 == 0)
{
return x_20;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_21, 0);
x_70 = lean_ctor_get(x_21, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_21);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_20, 0, x_71);
return x_20;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_20, 1);
lean_inc(x_72);
lean_dec(x_20);
x_73 = lean_ctor_get(x_21, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_21, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_75 = x_21;
} else {
 lean_dec_ref(x_21);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_72);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_20);
if (x_78 == 0)
{
return x_20;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_20, 0);
x_80 = lean_ctor_get(x_20, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_20);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_13);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_13, 0);
lean_dec(x_115);
x_116 = !lean_is_exclusive(x_14);
if (x_116 == 0)
{
return x_13;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_14, 0);
x_118 = lean_ctor_get(x_14, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_14);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_13, 0, x_119);
return x_13;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_13, 1);
lean_inc(x_120);
lean_dec(x_13);
x_121 = lean_ctor_get(x_14, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_14, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_123 = x_14;
} else {
 lean_dec_ref(x_14);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_120);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_126 = !lean_is_exclusive(x_13);
if (x_126 == 0)
{
return x_13;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_13, 0);
x_128 = lean_ctor_get(x_13, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_13);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
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
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_apply_6(x_4, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_array_size(x_15);
x_18 = 0;
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_19 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(x_1, x_2, x_17, x_18, x_15, x_4, x_5, x_6, x_16, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lake_Job_mixArray___rarg(x_22);
lean_dec(x_22);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*29);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*9);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_4);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_32 = lean_apply_6(x_4, x_31, x_5, x_6, x_23, x_8, x_21);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Lake_Module_recBuildDeps___lambda__6(x_18, x_2, x_24, x_3, x_35, x_4, x_5, x_6, x_36, x_8, x_34);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_32, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_32, 0, x_43);
return x_32;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_47 = x_33;
} else {
 lean_dec_ref(x_33);
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
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_32, 0);
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_32);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_4);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_56 = lean_apply_6(x_4, x_55, x_5, x_6, x_23, x_8, x_21);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Lake_Module_recBuildDeps___lambda__6(x_18, x_2, x_24, x_3, x_59, x_4, x_5, x_6, x_60, x_8, x_58);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_56);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_56, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_57);
if (x_64 == 0)
{
return x_56;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_57);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_56, 0, x_67);
return x_56;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_dec(x_56);
x_69 = lean_ctor_get(x_57, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_71 = x_57;
} else {
 lean_dec_ref(x_57);
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
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_56);
if (x_74 == 0)
{
return x_56;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_56, 0);
x_76 = lean_ctor_get(x_56, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_56);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_4);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_80 = lean_apply_6(x_4, x_79, x_5, x_6, x_23, x_8, x_21);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = l_Lake_Module_recBuildDeps___lambda__6(x_18, x_2, x_24, x_3, x_83, x_4, x_5, x_6, x_84, x_8, x_82);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_80);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_80, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
return x_80;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_81, 0);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_81);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_80, 0, x_91);
return x_80;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_dec(x_80);
x_93 = lean_ctor_get(x_81, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_81, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_95 = x_81;
} else {
 lean_dec_ref(x_81);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_92);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_80);
if (x_98 == 0)
{
return x_80;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_80, 0);
x_100 = lean_ctor_get(x_80, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_80);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_19);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_19, 0);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_20);
if (x_104 == 0)
{
return x_19;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_20, 0);
x_106 = lean_ctor_get(x_20, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_20);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_19, 0, x_107);
return x_19;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_19, 1);
lean_inc(x_108);
lean_dec(x_19);
x_109 = lean_ctor_get(x_20, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_20, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_111 = x_20;
} else {
 lean_dec_ref(x_20);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_108);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_19);
if (x_114 == 0)
{
return x_19;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_19, 0);
x_116 = lean_ctor_get(x_19, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_19);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_12);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_12, 0);
lean_dec(x_119);
x_120 = !lean_is_exclusive(x_13);
if (x_120 == 0)
{
return x_12;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_13, 0);
x_122 = lean_ctor_get(x_13, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_13);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_12, 0, x_123);
return x_12;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_12, 1);
lean_inc(x_124);
lean_dec(x_12);
x_125 = lean_ctor_get(x_13, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_13, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_127 = x_13;
} else {
 lean_dec_ref(x_13);
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
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_12);
if (x_130 == 0)
{
return x_12;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_12, 0);
x_132 = lean_ctor_get(x_12, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_12);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
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
x_13 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13___rarg), 8, 2);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_Module_recBuildDeps___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__12(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Lake_Module_recBuildDeps___lambda__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Lake_Module_recBuildDeps___lambda__3(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Lake_Module_recBuildDeps___lambda__4(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Lake_Module_recBuildDeps___lambda__5(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_12;
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
static lean_object* _init_l_Lake_Module_depsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Job_0__Lake_Job_toOpaqueImpl___rarg___boxed), 1, 0);
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
x_12 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate_x27___spec__5(x_11, x_3);
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
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_25);
lean_dec(x_6);
x_28 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_1, x_4, x_7);
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
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_26);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lake_Module_checkExists(x_1, x_7);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_37);
lean_ctor_set(x_35, 0, x_2);
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
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_inc(x_41);
lean_dec(x_6);
x_44 = l_Lake_Module_checkExists(x_1, x_7);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_42);
lean_ctor_set(x_2, 1, x_48);
lean_ctor_set(x_2, 0, x_45);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_2);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
lean_dec(x_2);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate_x27___spec__5(x_51, x_3);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_5, 0);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_4);
lean_dec(x_1);
x_55 = 0;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_6);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_7);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_59 = lean_ctor_get(x_6, 0);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_62 = x_6;
} else {
 lean_dec_ref(x_6);
 x_62 = lean_box(0);
}
x_63 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_1, x_4, x_7);
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
if (lean_is_scalar(x_62)) {
 x_67 = lean_alloc_ctor(0, 2, 1);
} else {
 x_67 = x_62;
}
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_61);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_4);
x_70 = lean_ctor_get(x_6, 0);
lean_inc(x_70);
x_71 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_72 = lean_ctor_get(x_6, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_73 = x_6;
} else {
 lean_dec_ref(x_6);
 x_73 = lean_box(0);
}
x_74 = l_Lake_Module_checkExists(x_1, x_7);
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
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 2, 1);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_71);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
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
lean_object* x_17; lean_object* x_18; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_94 = lean_ctor_get(x_14, 1);
lean_inc(x_94);
lean_dec(x_14);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_ctor_get(x_96, 7);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
x_99 = l_Lean_modToFilePath(x_1, x_2, x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lake_Module_clearOutputHashes___closed__1;
x_102 = l_Lean_modToFilePath(x_1, x_2, x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_ctor_get(x_3, 12);
x_105 = l_System_FilePath_join(x_4, x_104);
x_106 = l_Lake_Module_clearOutputHashes___closed__2;
x_107 = l_Lean_modToFilePath(x_105, x_2, x_106);
lean_dec(x_105);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
lean_inc(x_5);
x_109 = l_Lake_Module_bcFile_x3f(x_5);
x_110 = lean_ctor_get(x_6, 2);
lean_inc(x_110);
lean_dec(x_6);
x_111 = lean_ctor_get(x_7, 2);
x_112 = l_Array_append___rarg(x_110, x_111);
x_113 = l_Array_append___rarg(x_112, x_8);
x_114 = !lean_is_exclusive(x_15);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_15, 0);
x_116 = lean_ctor_get(x_15, 1);
x_117 = l_Lake_compileLeanModule(x_9, x_100, x_103, x_108, x_109, x_13, x_10, x_11, x_12, x_113, x_97, x_115, x_16);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_100);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = !lean_is_exclusive(x_118);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_118, 1);
lean_ctor_set(x_15, 0, x_121);
lean_ctor_set(x_118, 1, x_15);
x_17 = x_118;
x_18 = x_119;
goto block_93;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_118, 0);
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_118);
lean_ctor_set(x_15, 0, x_123);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_15);
x_17 = x_124;
x_18 = x_119;
goto block_93;
}
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
lean_dec(x_117);
x_126 = !lean_is_exclusive(x_118);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_118, 1);
lean_ctor_set(x_15, 0, x_127);
lean_ctor_set(x_118, 1, x_15);
x_17 = x_118;
x_18 = x_125;
goto block_93;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_118, 0);
x_129 = lean_ctor_get(x_118, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_118);
lean_ctor_set(x_15, 0, x_129);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_15);
x_17 = x_130;
x_18 = x_125;
goto block_93;
}
}
}
else
{
uint8_t x_131; 
lean_free_object(x_15);
lean_dec(x_116);
lean_dec(x_5);
x_131 = !lean_is_exclusive(x_117);
if (x_131 == 0)
{
return x_117;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_117, 0);
x_133 = lean_ctor_get(x_117, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_117);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_15, 0);
x_136 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_137 = lean_ctor_get(x_15, 1);
lean_inc(x_137);
lean_inc(x_135);
lean_dec(x_15);
x_138 = l_Lake_compileLeanModule(x_9, x_100, x_103, x_108, x_109, x_13, x_10, x_11, x_12, x_113, x_97, x_135, x_16);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_100);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_143 = x_139;
} else {
 lean_dec_ref(x_139);
 x_143 = lean_box(0);
}
x_144 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_137);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_136);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_141);
lean_ctor_set(x_145, 1, x_144);
x_17 = x_145;
x_18 = x_140;
goto block_93;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_138, 1);
lean_inc(x_146);
lean_dec(x_138);
x_147 = lean_ctor_get(x_139, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_139, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_149 = x_139;
} else {
 lean_dec_ref(x_139);
 x_149 = lean_box(0);
}
x_150 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_137);
lean_ctor_set_uint8(x_150, sizeof(void*)*2, x_136);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_150);
x_17 = x_151;
x_18 = x_146;
goto block_93;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_137);
lean_dec(x_5);
x_152 = lean_ctor_get(x_138, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_138, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_154 = x_138;
} else {
 lean_dec_ref(x_138);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
block_93:
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
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_inc(x_45);
lean_dec(x_20);
x_48 = l_Lake_Module_clearOutputHashes(x_5, x_18);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
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
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_46);
lean_ctor_set(x_17, 1, x_52);
lean_ctor_set(x_17, 0, x_49);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_17);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
x_57 = lean_io_error_to_string(x_54);
x_58 = 3;
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_array_get_size(x_45);
x_61 = lean_array_push(x_45, x_59);
x_62 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_47);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_46);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_62);
lean_ctor_set(x_17, 0, x_60);
if (lean_is_scalar(x_56)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_56;
 lean_ctor_set_tag(x_63, 0);
}
lean_ctor_set(x_63, 0, x_17);
lean_ctor_set(x_63, 1, x_55);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_17, 1);
lean_inc(x_64);
lean_dec(x_17);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_64, sizeof(void*)*2);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
x_69 = l_Lake_Module_clearOutputHashes(x_5, x_18);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
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
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 1);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_65);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_78 = x_69;
} else {
 lean_dec_ref(x_69);
 x_78 = lean_box(0);
}
x_79 = lean_io_error_to_string(x_76);
x_80 = 3;
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_82 = lean_array_get_size(x_65);
x_83 = lean_array_push(x_65, x_81);
if (lean_is_scalar(x_68)) {
 x_84 = lean_alloc_ctor(0, 2, 1);
} else {
 x_84 = x_68;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_67);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_66);
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
lean_dec(x_5);
x_87 = !lean_is_exclusive(x_17);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_17);
lean_ctor_set(x_88, 1, x_18);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_17, 0);
x_90 = lean_ctor_get(x_17, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_17);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_18);
return x_92;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_279; 
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
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 5, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
x_279 = !lean_is_exclusive(x_19);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_280 = lean_ctor_get(x_19, 0);
x_281 = l_System_FilePath_pathExists(x_15, x_20);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_unbox(x_282);
lean_dec(x_282);
if (x_283 == 0)
{
uint8_t x_284; 
lean_dec(x_17);
x_284 = !lean_is_exclusive(x_281);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_285 = lean_ctor_get(x_281, 1);
x_286 = lean_ctor_get(x_281, 0);
lean_dec(x_286);
x_287 = lean_ctor_get(x_14, 1);
lean_inc(x_287);
x_288 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_287, x_285);
x_289 = !lean_is_exclusive(x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_290 = lean_ctor_get(x_288, 0);
x_291 = lean_ctor_get(x_288, 1);
x_292 = lean_unbox(x_290);
lean_dec(x_290);
if (x_292 == 0)
{
lean_object* x_293; 
lean_free_object(x_288);
lean_free_object(x_281);
x_293 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_19, x_291);
return x_293;
}
else
{
uint8_t x_294; lean_object* x_295; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_14);
x_294 = 1;
x_295 = lean_box(x_294);
lean_ctor_set(x_281, 1, x_19);
lean_ctor_set(x_281, 0, x_295);
lean_ctor_set(x_288, 0, x_281);
return x_288;
}
}
else
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_296 = lean_ctor_get(x_288, 0);
x_297 = lean_ctor_get(x_288, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_288);
x_298 = lean_unbox(x_296);
lean_dec(x_296);
if (x_298 == 0)
{
lean_object* x_299; 
lean_free_object(x_281);
x_299 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_19, x_297);
return x_299;
}
else
{
uint8_t x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_14);
x_300 = 1;
x_301 = lean_box(x_300);
lean_ctor_set(x_281, 1, x_19);
lean_ctor_set(x_281, 0, x_301);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_281);
lean_ctor_set(x_302, 1, x_297);
return x_302;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_303 = lean_ctor_get(x_281, 1);
lean_inc(x_303);
lean_dec(x_281);
x_304 = lean_ctor_get(x_14, 1);
lean_inc(x_304);
x_305 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_304, x_303);
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
x_309 = lean_unbox(x_306);
lean_dec(x_306);
if (x_309 == 0)
{
lean_object* x_310; 
lean_dec(x_308);
x_310 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_19, x_307);
return x_310;
}
else
{
uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_14);
x_311 = 1;
x_312 = lean_box(x_311);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_19);
if (lean_is_scalar(x_308)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_308;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_307);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_315 = lean_ctor_get(x_281, 1);
lean_inc(x_315);
lean_dec(x_281);
x_316 = l_Lake_readTraceFile_x3f(x_15, x_280, x_315);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = !lean_is_exclusive(x_317);
if (x_319 == 0)
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_317, 1);
lean_ctor_set(x_19, 0, x_320);
lean_ctor_set(x_317, 1, x_19);
x_24 = x_317;
x_25 = x_318;
goto block_278;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_317, 0);
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_317);
lean_ctor_set(x_19, 0, x_322);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_19);
x_24 = x_323;
x_25 = x_318;
goto block_278;
}
}
}
else
{
lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_324 = lean_ctor_get(x_19, 0);
x_325 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
x_326 = lean_ctor_get(x_19, 1);
lean_inc(x_326);
lean_inc(x_324);
lean_dec(x_19);
x_327 = l_System_FilePath_pathExists(x_15, x_20);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_unbox(x_328);
lean_dec(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; 
lean_dec(x_17);
x_330 = lean_ctor_get(x_327, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_331 = x_327;
} else {
 lean_dec_ref(x_327);
 x_331 = lean_box(0);
}
x_332 = lean_ctor_get(x_14, 1);
lean_inc(x_332);
x_333 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_332, x_330);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_336 = x_333;
} else {
 lean_dec_ref(x_333);
 x_336 = lean_box(0);
}
x_337 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_337, 0, x_324);
lean_ctor_set(x_337, 1, x_326);
lean_ctor_set_uint8(x_337, sizeof(void*)*2, x_325);
x_338 = lean_unbox(x_334);
lean_dec(x_334);
if (x_338 == 0)
{
lean_object* x_339; 
lean_dec(x_336);
lean_dec(x_331);
x_339 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_337, x_335);
return x_339;
}
else
{
uint8_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_14);
x_340 = 1;
x_341 = lean_box(x_340);
if (lean_is_scalar(x_331)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_331;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_337);
if (lean_is_scalar(x_336)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_336;
}
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_335);
return x_343;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_344 = lean_ctor_get(x_327, 1);
lean_inc(x_344);
lean_dec(x_327);
x_345 = l_Lake_readTraceFile_x3f(x_15, x_324, x_344);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_ctor_get(x_346, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_350 = x_346;
} else {
 lean_dec_ref(x_346);
 x_350 = lean_box(0);
}
x_351 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_326);
lean_ctor_set_uint8(x_351, sizeof(void*)*2, x_325);
if (lean_is_scalar(x_350)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_350;
}
lean_ctor_set(x_352, 0, x_348);
lean_ctor_set(x_352, 1, x_351);
x_24 = x_352;
x_25 = x_347;
goto block_278;
}
}
block_278:
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
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_54 = lean_ctor_get(x_28, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_28);
x_55 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_17, x_25);
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
x_59 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_53);
if (x_31 == 0)
{
lean_object* x_60; 
lean_dec(x_58);
lean_dec(x_56);
lean_free_object(x_24);
x_60 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_59, x_57);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = lean_unbox(x_56);
lean_dec(x_56);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_58);
lean_free_object(x_24);
x_62 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_59, x_57);
return x_62;
}
else
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_14);
x_63 = 1;
x_64 = lean_box(x_63);
lean_ctor_set(x_24, 1, x_59);
lean_ctor_set(x_24, 0, x_64);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_24);
lean_ctor_set(x_65, 1, x_57);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
lean_dec(x_24);
x_67 = lean_ctor_get(x_18, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_67, sizeof(void*)*1);
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_66, sizeof(void*)*2);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_72 = x_66;
} else {
 lean_dec_ref(x_66);
 x_72 = lean_box(0);
}
x_73 = l_Lake_MTime_checkUpToDate___at_Lake_Module_recBuildLean___spec__2(x_13, x_17, x_25);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
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
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 2, 1);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_71);
lean_ctor_set_uint8(x_77, sizeof(void*)*2, x_70);
if (x_68 == 0)
{
lean_object* x_78; 
lean_dec(x_76);
lean_dec(x_74);
x_78 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_77, x_75);
return x_78;
}
else
{
uint8_t x_79; 
x_79 = lean_unbox(x_74);
lean_dec(x_74);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_76);
x_80 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_77, x_75);
return x_80;
}
else
{
uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_14);
x_81 = 1;
x_82 = lean_box(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
if (lean_is_scalar(x_76)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_76;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_75);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_26);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_86 = lean_ctor_get(x_26, 0);
x_87 = lean_ctor_get(x_24, 1);
lean_inc(x_87);
lean_dec(x_24);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
lean_ctor_set(x_26, 0, x_88);
lean_inc(x_14);
x_90 = l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(x_13, x_14, x_26, x_17, x_18, x_87, x_25);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_89);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_95, x_94);
return x_96;
}
else
{
uint8_t x_97; 
lean_dec(x_23);
lean_dec(x_14);
x_97 = !lean_is_exclusive(x_91);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_91, 1);
x_99 = lean_ctor_get(x_91, 0);
lean_dec(x_99);
x_100 = !lean_is_exclusive(x_90);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_90, 1);
x_102 = lean_ctor_get(x_90, 0);
lean_dec(x_102);
x_103 = !lean_is_exclusive(x_98);
if (x_103 == 0)
{
uint8_t x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_104 = lean_ctor_get_uint8(x_98, sizeof(void*)*2);
x_105 = 1;
x_106 = l_Lake_JobAction_merge(x_104, x_105);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_106);
x_107 = lean_array_get_size(x_89);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_nat_dec_lt(x_108, x_107);
if (x_109 == 0)
{
uint8_t x_110; lean_object* x_111; 
lean_dec(x_107);
lean_dec(x_89);
lean_dec(x_18);
x_110 = 1;
x_111 = lean_box(x_110);
lean_ctor_set(x_91, 0, x_111);
return x_90;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_107, x_107);
if (x_112 == 0)
{
uint8_t x_113; lean_object* x_114; 
lean_dec(x_107);
lean_dec(x_89);
lean_dec(x_18);
x_113 = 1;
x_114 = lean_box(x_113);
lean_ctor_set(x_91, 0, x_114);
return x_90;
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_free_object(x_90);
lean_free_object(x_91);
x_115 = 0;
x_116 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_117 = lean_box(0);
x_118 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_89, x_115, x_116, x_117, x_18, x_98, x_101);
lean_dec(x_18);
lean_dec(x_89);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_120, 0);
lean_dec(x_122);
x_123 = 1;
x_124 = lean_box(x_123);
lean_ctor_set(x_120, 0, x_124);
return x_118;
}
else
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec(x_120);
x_126 = 1;
x_127 = lean_box(x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
lean_ctor_set(x_118, 0, x_128);
return x_118;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_129 = lean_ctor_get(x_118, 0);
x_130 = lean_ctor_get(x_118, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_118);
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
x_133 = 1;
x_134 = lean_box(x_133);
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_132;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_131);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_130);
return x_136;
}
}
}
}
else
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_137 = lean_ctor_get(x_98, 0);
x_138 = lean_ctor_get_uint8(x_98, sizeof(void*)*2);
x_139 = lean_ctor_get(x_98, 1);
lean_inc(x_139);
lean_inc(x_137);
lean_dec(x_98);
x_140 = 1;
x_141 = l_Lake_JobAction_merge(x_138, x_140);
x_142 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_139);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_141);
x_143 = lean_array_get_size(x_89);
x_144 = lean_unsigned_to_nat(0u);
x_145 = lean_nat_dec_lt(x_144, x_143);
if (x_145 == 0)
{
uint8_t x_146; lean_object* x_147; 
lean_dec(x_143);
lean_dec(x_89);
lean_dec(x_18);
x_146 = 1;
x_147 = lean_box(x_146);
lean_ctor_set(x_91, 1, x_142);
lean_ctor_set(x_91, 0, x_147);
return x_90;
}
else
{
uint8_t x_148; 
x_148 = lean_nat_dec_le(x_143, x_143);
if (x_148 == 0)
{
uint8_t x_149; lean_object* x_150; 
lean_dec(x_143);
lean_dec(x_89);
lean_dec(x_18);
x_149 = 1;
x_150 = lean_box(x_149);
lean_ctor_set(x_91, 1, x_142);
lean_ctor_set(x_91, 0, x_150);
return x_90;
}
else
{
size_t x_151; size_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_free_object(x_90);
lean_free_object(x_91);
x_151 = 0;
x_152 = lean_usize_of_nat(x_143);
lean_dec(x_143);
x_153 = lean_box(0);
x_154 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_89, x_151, x_152, x_153, x_18, x_142, x_101);
lean_dec(x_18);
lean_dec(x_89);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_159 = x_155;
} else {
 lean_dec_ref(x_155);
 x_159 = lean_box(0);
}
x_160 = 1;
x_161 = lean_box(x_160);
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_158);
if (lean_is_scalar(x_157)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_157;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_156);
return x_163;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_164 = lean_ctor_get(x_90, 1);
lean_inc(x_164);
lean_dec(x_90);
x_165 = lean_ctor_get(x_98, 0);
lean_inc(x_165);
x_166 = lean_ctor_get_uint8(x_98, sizeof(void*)*2);
x_167 = lean_ctor_get(x_98, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_168 = x_98;
} else {
 lean_dec_ref(x_98);
 x_168 = lean_box(0);
}
x_169 = 1;
x_170 = l_Lake_JobAction_merge(x_166, x_169);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 2, 1);
} else {
 x_171 = x_168;
}
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set_uint8(x_171, sizeof(void*)*2, x_170);
x_172 = lean_array_get_size(x_89);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_nat_dec_lt(x_173, x_172);
if (x_174 == 0)
{
uint8_t x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_172);
lean_dec(x_89);
lean_dec(x_18);
x_175 = 1;
x_176 = lean_box(x_175);
lean_ctor_set(x_91, 1, x_171);
lean_ctor_set(x_91, 0, x_176);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_91);
lean_ctor_set(x_177, 1, x_164);
return x_177;
}
else
{
uint8_t x_178; 
x_178 = lean_nat_dec_le(x_172, x_172);
if (x_178 == 0)
{
uint8_t x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_172);
lean_dec(x_89);
lean_dec(x_18);
x_179 = 1;
x_180 = lean_box(x_179);
lean_ctor_set(x_91, 1, x_171);
lean_ctor_set(x_91, 0, x_180);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_91);
lean_ctor_set(x_181, 1, x_164);
return x_181;
}
else
{
size_t x_182; size_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_free_object(x_91);
x_182 = 0;
x_183 = lean_usize_of_nat(x_172);
lean_dec(x_172);
x_184 = lean_box(0);
x_185 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_89, x_182, x_183, x_184, x_18, x_171, x_164);
lean_dec(x_18);
lean_dec(x_89);
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
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_195 = lean_ctor_get(x_91, 1);
lean_inc(x_195);
lean_dec(x_91);
x_196 = lean_ctor_get(x_90, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_197 = x_90;
} else {
 lean_dec_ref(x_90);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
x_199 = lean_ctor_get_uint8(x_195, sizeof(void*)*2);
x_200 = lean_ctor_get(x_195, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_201 = x_195;
} else {
 lean_dec_ref(x_195);
 x_201 = lean_box(0);
}
x_202 = 1;
x_203 = l_Lake_JobAction_merge(x_199, x_202);
if (lean_is_scalar(x_201)) {
 x_204 = lean_alloc_ctor(0, 2, 1);
} else {
 x_204 = x_201;
}
lean_ctor_set(x_204, 0, x_198);
lean_ctor_set(x_204, 1, x_200);
lean_ctor_set_uint8(x_204, sizeof(void*)*2, x_203);
x_205 = lean_array_get_size(x_89);
x_206 = lean_unsigned_to_nat(0u);
x_207 = lean_nat_dec_lt(x_206, x_205);
if (x_207 == 0)
{
uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_205);
lean_dec(x_89);
lean_dec(x_18);
x_208 = 1;
x_209 = lean_box(x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_204);
if (lean_is_scalar(x_197)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_197;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_196);
return x_211;
}
else
{
uint8_t x_212; 
x_212 = lean_nat_dec_le(x_205, x_205);
if (x_212 == 0)
{
uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_205);
lean_dec(x_89);
lean_dec(x_18);
x_213 = 1;
x_214 = lean_box(x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_204);
if (lean_is_scalar(x_197)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_197;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_196);
return x_216;
}
else
{
size_t x_217; size_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_197);
x_217 = 0;
x_218 = lean_usize_of_nat(x_205);
lean_dec(x_205);
x_219 = lean_box(0);
x_220 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_89, x_217, x_218, x_219, x_18, x_204, x_196);
lean_dec(x_18);
lean_dec(x_89);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_225 = x_221;
} else {
 lean_dec_ref(x_221);
 x_225 = lean_box(0);
}
x_226 = 1;
x_227 = lean_box(x_226);
if (lean_is_scalar(x_225)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_225;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_224);
if (lean_is_scalar(x_223)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_223;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_222);
return x_229;
}
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_230 = lean_ctor_get(x_26, 0);
lean_inc(x_230);
lean_dec(x_26);
x_231 = lean_ctor_get(x_24, 1);
lean_inc(x_231);
lean_dec(x_24);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_232);
lean_inc(x_14);
x_235 = l_Lake_checkHashUpToDate___at_Lake_Module_recBuildLean___spec__3(x_13, x_14, x_234, x_17, x_18, x_231, x_25);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_unbox(x_237);
lean_dec(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_233);
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
lean_dec(x_235);
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
lean_dec(x_236);
x_241 = l_Lake_buildUnlessUpToDate_x3f_go(x_14, x_15, x_23, x_16, x_18, x_240, x_239);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
lean_dec(x_23);
lean_dec(x_14);
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
x_244 = lean_ctor_get(x_235, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_245 = x_235;
} else {
 lean_dec_ref(x_235);
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
x_250 = 1;
x_251 = l_Lake_JobAction_merge(x_247, x_250);
if (lean_is_scalar(x_249)) {
 x_252 = lean_alloc_ctor(0, 2, 1);
} else {
 x_252 = x_249;
}
lean_ctor_set(x_252, 0, x_246);
lean_ctor_set(x_252, 1, x_248);
lean_ctor_set_uint8(x_252, sizeof(void*)*2, x_251);
x_253 = lean_array_get_size(x_233);
x_254 = lean_unsigned_to_nat(0u);
x_255 = lean_nat_dec_lt(x_254, x_253);
if (x_255 == 0)
{
uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_253);
lean_dec(x_233);
lean_dec(x_18);
x_256 = 1;
x_257 = lean_box(x_256);
if (lean_is_scalar(x_243)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_243;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_252);
if (lean_is_scalar(x_245)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_245;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_244);
return x_259;
}
else
{
uint8_t x_260; 
x_260 = lean_nat_dec_le(x_253, x_253);
if (x_260 == 0)
{
uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_253);
lean_dec(x_233);
lean_dec(x_18);
x_261 = 1;
x_262 = lean_box(x_261);
if (lean_is_scalar(x_243)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_243;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_252);
if (lean_is_scalar(x_245)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_245;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_244);
return x_264;
}
else
{
size_t x_265; size_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_245);
lean_dec(x_243);
x_265 = 0;
x_266 = lean_usize_of_nat(x_253);
lean_dec(x_253);
x_267 = lean_box(0);
x_268 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate_x27___spec__6(x_233, x_265, x_266, x_267, x_18, x_252, x_244);
lean_dec(x_18);
lean_dec(x_233);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_273 = x_269;
} else {
 lean_dec_ref(x_269);
 x_273 = lean_box(0);
}
x_274 = 1;
x_275 = lean_box(x_274);
if (lean_is_scalar(x_273)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_273;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_272);
if (lean_is_scalar(x_271)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_271;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_270);
return x_277;
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_329; uint64_t x_330; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_14 = x_5;
} else {
 lean_dec_ref(x_5);
 x_14 = lean_box(0);
}
x_15 = l_Lake_BuildTrace_mix(x_13, x_10);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_array_size(x_20);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_21, x_22, x_20);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
x_25 = l_Array_append___rarg(x_23, x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_array_size(x_28);
x_30 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_29, x_22, x_28);
x_31 = l_Array_append___rarg(x_25, x_30);
lean_dec(x_30);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
x_33 = l_Array_append___rarg(x_31, x_32);
lean_dec(x_32);
x_34 = lean_array_get_size(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_lt(x_35, x_34);
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
lean_dec(x_17);
x_38 = lean_ctor_get(x_18, 7);
lean_inc(x_38);
lean_inc(x_37);
x_39 = l_System_FilePath_join(x_37, x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_26, 2);
lean_inc(x_40);
lean_dec(x_26);
x_41 = l_System_FilePath_join(x_39, x_40);
lean_dec(x_40);
x_42 = l_Lake_Module_recParseImports___closed__1;
x_43 = l_Lean_modToFilePath(x_41, x_2, x_42);
x_329 = l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(x_43, x_6);
if (x_36 == 0)
{
uint64_t x_361; 
lean_dec(x_34);
x_361 = l_Lake_Hash_nil;
x_330 = x_361;
goto block_360;
}
else
{
uint8_t x_362; 
x_362 = lean_nat_dec_le(x_34, x_34);
if (x_362 == 0)
{
uint64_t x_363; 
lean_dec(x_34);
x_363 = l_Lake_Hash_nil;
x_330 = x_363;
goto block_360;
}
else
{
size_t x_364; uint64_t x_365; uint64_t x_366; 
x_364 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_365 = l_Lake_Hash_nil;
x_366 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(x_33, x_22, x_364, x_365);
x_330 = x_366;
goto block_360;
}
}
block_328:
{
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_9);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_50 = l_Lake_BuildTrace_mix(x_49, x_47);
lean_inc(x_50);
lean_ctor_set(x_46, 1, x_50);
x_51 = lean_ctor_get(x_18, 8);
lean_inc(x_51);
x_52 = l_System_FilePath_join(x_37, x_51);
lean_dec(x_51);
x_53 = lean_ctor_get(x_18, 9);
lean_inc(x_53);
lean_inc(x_52);
x_54 = l_System_FilePath_join(x_52, x_53);
lean_dec(x_53);
x_55 = l_Lake_Module_recBuildLean___lambda__1___closed__1;
x_56 = l_Lean_modToFilePath(x_54, x_2, x_55);
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_dec(x_47);
x_58 = 3;
lean_inc(x_4);
lean_inc_n(x_1, 2);
x_59 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(x_1, x_2, x_7, x_8, x_18, x_19, x_27, x_33, x_41, x_43, x_52, x_54, x_1, x_50, x_56, x_58, x_57, x_4, x_46, x_45);
lean_dec(x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_60, 1);
x_65 = lean_ctor_get(x_60, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_64, 0);
x_69 = l_Lake_Module_cacheOutputHashes(x_1, x_66);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 0);
lean_ctor_set(x_60, 0, x_71);
lean_ctor_set(x_69, 0, x_60);
return x_69;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_69);
lean_ctor_set(x_60, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_60);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_69);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_69, 0);
x_77 = lean_io_error_to_string(x_76);
x_78 = 3;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = lean_array_get_size(x_68);
x_81 = lean_array_push(x_68, x_79);
lean_ctor_set(x_64, 0, x_81);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_80);
lean_ctor_set_tag(x_69, 0);
lean_ctor_set(x_69, 0, x_60);
return x_69;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_69, 0);
x_83 = lean_ctor_get(x_69, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_69);
x_84 = lean_io_error_to_string(x_82);
x_85 = 3;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_array_get_size(x_68);
x_88 = lean_array_push(x_68, x_86);
lean_ctor_set(x_64, 0, x_88);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_60);
lean_ctor_set(x_89, 1, x_83);
return x_89;
}
}
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_64, 0);
x_91 = lean_ctor_get_uint8(x_64, sizeof(void*)*2);
x_92 = lean_ctor_get(x_64, 1);
lean_inc(x_92);
lean_inc(x_90);
lean_dec(x_64);
x_93 = l_Lake_Module_cacheOutputHashes(x_1, x_66);
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
x_97 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_92);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_91);
lean_ctor_set(x_60, 1, x_97);
lean_ctor_set(x_60, 0, x_94);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_60);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
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
x_102 = lean_io_error_to_string(x_99);
x_103 = 3;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_array_get_size(x_90);
x_106 = lean_array_push(x_90, x_104);
x_107 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_92);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_91);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_107);
lean_ctor_set(x_60, 0, x_105);
if (lean_is_scalar(x_101)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_101;
 lean_ctor_set_tag(x_108, 0);
}
lean_ctor_set(x_108, 0, x_60);
lean_ctor_set(x_108, 1, x_100);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_60, 1);
lean_inc(x_109);
lean_dec(x_60);
x_110 = lean_ctor_get(x_59, 1);
lean_inc(x_110);
lean_dec(x_59);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get_uint8(x_109, sizeof(void*)*2);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_114 = x_109;
} else {
 lean_dec_ref(x_109);
 x_114 = lean_box(0);
}
x_115 = l_Lake_Module_cacheOutputHashes(x_1, x_110);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_119 = lean_alloc_ctor(0, 2, 1);
} else {
 x_119 = x_114;
}
lean_ctor_set(x_119, 0, x_111);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_112);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_117);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_122 = lean_ctor_get(x_115, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_115, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_124 = x_115;
} else {
 lean_dec_ref(x_115);
 x_124 = lean_box(0);
}
x_125 = lean_io_error_to_string(x_122);
x_126 = 3;
x_127 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_126);
x_128 = lean_array_get_size(x_111);
x_129 = lean_array_push(x_111, x_127);
if (lean_is_scalar(x_114)) {
 x_130 = lean_alloc_ctor(0, 2, 1);
} else {
 x_130 = x_114;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_113);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_112);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
if (lean_is_scalar(x_124)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_124;
 lean_ctor_set_tag(x_132, 0);
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_123);
return x_132;
}
}
}
else
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_4, 0);
lean_inc(x_133);
lean_dec(x_4);
x_134 = lean_ctor_get_uint8(x_133, sizeof(void*)*1 + 1);
lean_dec(x_133);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_60);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_60, 1);
x_137 = lean_ctor_get(x_60, 0);
lean_dec(x_137);
x_138 = lean_ctor_get(x_59, 1);
lean_inc(x_138);
lean_dec(x_59);
x_139 = !lean_is_exclusive(x_136);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_136, 0);
x_141 = l_Lake_Module_cacheOutputHashes(x_1, x_138);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_141, 0);
lean_ctor_set(x_60, 0, x_143);
lean_ctor_set(x_141, 0, x_60);
return x_141;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_141, 0);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_141);
lean_ctor_set(x_60, 0, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_60);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_141);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_141, 0);
x_149 = lean_io_error_to_string(x_148);
x_150 = 3;
x_151 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_150);
x_152 = lean_array_get_size(x_140);
x_153 = lean_array_push(x_140, x_151);
lean_ctor_set(x_136, 0, x_153);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_152);
lean_ctor_set_tag(x_141, 0);
lean_ctor_set(x_141, 0, x_60);
return x_141;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_154 = lean_ctor_get(x_141, 0);
x_155 = lean_ctor_get(x_141, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_141);
x_156 = lean_io_error_to_string(x_154);
x_157 = 3;
x_158 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*1, x_157);
x_159 = lean_array_get_size(x_140);
x_160 = lean_array_push(x_140, x_158);
lean_ctor_set(x_136, 0, x_160);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_60);
lean_ctor_set(x_161, 1, x_155);
return x_161;
}
}
}
else
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_136, 0);
x_163 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_164 = lean_ctor_get(x_136, 1);
lean_inc(x_164);
lean_inc(x_162);
lean_dec(x_136);
x_165 = l_Lake_Module_cacheOutputHashes(x_1, x_138);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
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
x_169 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_169, 0, x_162);
lean_ctor_set(x_169, 1, x_164);
lean_ctor_set_uint8(x_169, sizeof(void*)*2, x_163);
lean_ctor_set(x_60, 1, x_169);
lean_ctor_set(x_60, 0, x_166);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_60);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_171 = lean_ctor_get(x_165, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_165, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_173 = x_165;
} else {
 lean_dec_ref(x_165);
 x_173 = lean_box(0);
}
x_174 = lean_io_error_to_string(x_171);
x_175 = 3;
x_176 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_175);
x_177 = lean_array_get_size(x_162);
x_178 = lean_array_push(x_162, x_176);
x_179 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_164);
lean_ctor_set_uint8(x_179, sizeof(void*)*2, x_163);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_179);
lean_ctor_set(x_60, 0, x_177);
if (lean_is_scalar(x_173)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_173;
 lean_ctor_set_tag(x_180, 0);
}
lean_ctor_set(x_180, 0, x_60);
lean_ctor_set(x_180, 1, x_172);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = lean_ctor_get(x_60, 1);
lean_inc(x_181);
lean_dec(x_60);
x_182 = lean_ctor_get(x_59, 1);
lean_inc(x_182);
lean_dec(x_59);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_181, sizeof(void*)*2);
x_185 = lean_ctor_get(x_181, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_186 = x_181;
} else {
 lean_dec_ref(x_181);
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
}
else
{
uint8_t x_205; 
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_59);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_ctor_get(x_59, 0);
lean_dec(x_206);
x_207 = !lean_is_exclusive(x_60);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_60, 0);
lean_dec(x_208);
x_209 = lean_box(0);
lean_ctor_set(x_60, 0, x_209);
return x_59;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_60, 1);
lean_inc(x_210);
lean_dec(x_60);
x_211 = lean_box(0);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_210);
lean_ctor_set(x_59, 0, x_212);
return x_59;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_59, 1);
lean_inc(x_213);
lean_dec(x_59);
x_214 = lean_ctor_get(x_60, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_215 = x_60;
} else {
 lean_dec_ref(x_60);
 x_215 = lean_box(0);
}
x_216 = lean_box(0);
if (lean_is_scalar(x_215)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_215;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_214);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_213);
return x_218;
}
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_4);
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_59);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_59, 0);
lean_dec(x_220);
x_221 = !lean_is_exclusive(x_60);
if (x_221 == 0)
{
return x_59;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_60, 0);
x_223 = lean_ctor_get(x_60, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_60);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_59, 0, x_224);
return x_59;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_225 = lean_ctor_get(x_59, 1);
lean_inc(x_225);
lean_dec(x_59);
x_226 = lean_ctor_get(x_60, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_60, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_228 = x_60;
} else {
 lean_dec_ref(x_60);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_225);
return x_230;
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_4);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_59);
if (x_231 == 0)
{
return x_59;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_59, 0);
x_233 = lean_ctor_get(x_59, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_59);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; 
x_235 = lean_ctor_get(x_46, 0);
x_236 = lean_ctor_get_uint8(x_46, sizeof(void*)*2);
x_237 = lean_ctor_get(x_46, 1);
lean_inc(x_237);
lean_inc(x_235);
lean_dec(x_46);
lean_inc(x_47);
x_238 = l_Lake_BuildTrace_mix(x_237, x_47);
lean_inc(x_238);
x_239 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_239, 0, x_235);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set_uint8(x_239, sizeof(void*)*2, x_236);
x_240 = lean_ctor_get(x_18, 8);
lean_inc(x_240);
x_241 = l_System_FilePath_join(x_37, x_240);
lean_dec(x_240);
x_242 = lean_ctor_get(x_18, 9);
lean_inc(x_242);
lean_inc(x_241);
x_243 = l_System_FilePath_join(x_241, x_242);
lean_dec(x_242);
x_244 = l_Lake_Module_recBuildLean___lambda__1___closed__1;
x_245 = l_Lean_modToFilePath(x_243, x_2, x_244);
x_246 = lean_ctor_get(x_47, 1);
lean_inc(x_246);
lean_dec(x_47);
x_247 = 3;
lean_inc(x_4);
lean_inc_n(x_1, 2);
x_248 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_Module_recBuildLean___spec__1(x_1, x_2, x_7, x_8, x_18, x_19, x_27, x_33, x_41, x_43, x_241, x_243, x_1, x_238, x_245, x_247, x_246, x_4, x_239, x_45);
lean_dec(x_245);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_unbox(x_250);
lean_dec(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_4);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_253 = x_249;
} else {
 lean_dec_ref(x_249);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_248, 1);
lean_inc(x_254);
lean_dec(x_248);
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
x_256 = lean_ctor_get_uint8(x_252, sizeof(void*)*2);
x_257 = lean_ctor_get(x_252, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_258 = x_252;
} else {
 lean_dec_ref(x_252);
 x_258 = lean_box(0);
}
x_259 = l_Lake_Module_cacheOutputHashes(x_1, x_254);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_262 = x_259;
} else {
 lean_dec_ref(x_259);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_263 = lean_alloc_ctor(0, 2, 1);
} else {
 x_263 = x_258;
}
lean_ctor_set(x_263, 0, x_255);
lean_ctor_set(x_263, 1, x_257);
lean_ctor_set_uint8(x_263, sizeof(void*)*2, x_256);
if (lean_is_scalar(x_253)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_253;
}
lean_ctor_set(x_264, 0, x_260);
lean_ctor_set(x_264, 1, x_263);
if (lean_is_scalar(x_262)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_262;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_261);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_266 = lean_ctor_get(x_259, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_259, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_268 = x_259;
} else {
 lean_dec_ref(x_259);
 x_268 = lean_box(0);
}
x_269 = lean_io_error_to_string(x_266);
x_270 = 3;
x_271 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set_uint8(x_271, sizeof(void*)*1, x_270);
x_272 = lean_array_get_size(x_255);
x_273 = lean_array_push(x_255, x_271);
if (lean_is_scalar(x_258)) {
 x_274 = lean_alloc_ctor(0, 2, 1);
} else {
 x_274 = x_258;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_257);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_256);
if (lean_is_scalar(x_253)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_253;
 lean_ctor_set_tag(x_275, 1);
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_274);
if (lean_is_scalar(x_268)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_268;
 lean_ctor_set_tag(x_276, 0);
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_267);
return x_276;
}
}
else
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_ctor_get(x_4, 0);
lean_inc(x_277);
lean_dec(x_4);
x_278 = lean_ctor_get_uint8(x_277, sizeof(void*)*1 + 1);
lean_dec(x_277);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_279 = lean_ctor_get(x_249, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_280 = x_249;
} else {
 lean_dec_ref(x_249);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_248, 1);
lean_inc(x_281);
lean_dec(x_248);
x_282 = lean_ctor_get(x_279, 0);
lean_inc(x_282);
x_283 = lean_ctor_get_uint8(x_279, sizeof(void*)*2);
x_284 = lean_ctor_get(x_279, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_285 = x_279;
} else {
 lean_dec_ref(x_279);
 x_285 = lean_box(0);
}
x_286 = l_Lake_Module_cacheOutputHashes(x_1, x_281);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
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
if (lean_is_scalar(x_285)) {
 x_290 = lean_alloc_ctor(0, 2, 1);
} else {
 x_290 = x_285;
}
lean_ctor_set(x_290, 0, x_282);
lean_ctor_set(x_290, 1, x_284);
lean_ctor_set_uint8(x_290, sizeof(void*)*2, x_283);
if (lean_is_scalar(x_280)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_280;
}
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_290);
if (lean_is_scalar(x_289)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_289;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_288);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_293 = lean_ctor_get(x_286, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_286, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_295 = x_286;
} else {
 lean_dec_ref(x_286);
 x_295 = lean_box(0);
}
x_296 = lean_io_error_to_string(x_293);
x_297 = 3;
x_298 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set_uint8(x_298, sizeof(void*)*1, x_297);
x_299 = lean_array_get_size(x_282);
x_300 = lean_array_push(x_282, x_298);
if (lean_is_scalar(x_285)) {
 x_301 = lean_alloc_ctor(0, 2, 1);
} else {
 x_301 = x_285;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_284);
lean_ctor_set_uint8(x_301, sizeof(void*)*2, x_283);
if (lean_is_scalar(x_280)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_280;
 lean_ctor_set_tag(x_302, 1);
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_301);
if (lean_is_scalar(x_295)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_295;
 lean_ctor_set_tag(x_303, 0);
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_294);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_1);
x_304 = lean_ctor_get(x_248, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_305 = x_248;
} else {
 lean_dec_ref(x_248);
 x_305 = lean_box(0);
}
x_306 = lean_ctor_get(x_249, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_307 = x_249;
} else {
 lean_dec_ref(x_249);
 x_307 = lean_box(0);
}
x_308 = lean_box(0);
if (lean_is_scalar(x_307)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_307;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_306);
if (lean_is_scalar(x_305)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_305;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_304);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_4);
lean_dec(x_1);
x_311 = lean_ctor_get(x_248, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_312 = x_248;
} else {
 lean_dec_ref(x_248);
 x_312 = lean_box(0);
}
x_313 = lean_ctor_get(x_249, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_249, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_315 = x_249;
} else {
 lean_dec_ref(x_249);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_314);
if (lean_is_scalar(x_312)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_312;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_311);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_4);
lean_dec(x_1);
x_318 = lean_ctor_get(x_248, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_248, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_320 = x_248;
} else {
 lean_dec_ref(x_248);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
}
else
{
uint8_t x_322; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_322 = !lean_is_exclusive(x_44);
if (x_322 == 0)
{
lean_object* x_323; 
if (lean_is_scalar(x_9)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_9;
}
lean_ctor_set(x_323, 0, x_44);
lean_ctor_set(x_323, 1, x_45);
return x_323;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_324 = lean_ctor_get(x_44, 0);
x_325 = lean_ctor_get(x_44, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_44);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
if (lean_is_scalar(x_9)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_9;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_45);
return x_327;
}
}
}
block_360:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_331 = l_Lake_Module_recBuildDeps___lambda__2___closed__2;
x_332 = lean_box_uint64(x_330);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_331);
x_334 = l_Lake_BuildTrace_mix(x_15, x_333);
if (lean_obj_tag(x_329) == 0)
{
uint8_t x_335; 
x_335 = !lean_is_exclusive(x_329);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_329, 1);
if (lean_is_scalar(x_14)) {
 x_337 = lean_alloc_ctor(0, 2, 1);
} else {
 x_337 = x_14;
}
lean_ctor_set(x_337, 0, x_11);
lean_ctor_set(x_337, 1, x_334);
lean_ctor_set_uint8(x_337, sizeof(void*)*2, x_12);
lean_ctor_set(x_329, 1, x_337);
x_44 = x_329;
x_45 = x_336;
goto block_328;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_338 = lean_ctor_get(x_329, 0);
x_339 = lean_ctor_get(x_329, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_329);
if (lean_is_scalar(x_14)) {
 x_340 = lean_alloc_ctor(0, 2, 1);
} else {
 x_340 = x_14;
}
lean_ctor_set(x_340, 0, x_11);
lean_ctor_set(x_340, 1, x_334);
lean_ctor_set_uint8(x_340, sizeof(void*)*2, x_12);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_340);
x_44 = x_341;
x_45 = x_339;
goto block_328;
}
}
else
{
uint8_t x_342; 
x_342 = !lean_is_exclusive(x_329);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_343 = lean_ctor_get(x_329, 0);
x_344 = lean_ctor_get(x_329, 1);
x_345 = lean_io_error_to_string(x_343);
x_346 = 3;
x_347 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*1, x_346);
x_348 = lean_array_get_size(x_11);
x_349 = lean_array_push(x_11, x_347);
if (lean_is_scalar(x_14)) {
 x_350 = lean_alloc_ctor(0, 2, 1);
} else {
 x_350 = x_14;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_334);
lean_ctor_set_uint8(x_350, sizeof(void*)*2, x_12);
lean_ctor_set(x_329, 1, x_350);
lean_ctor_set(x_329, 0, x_348);
x_44 = x_329;
x_45 = x_344;
goto block_328;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_351 = lean_ctor_get(x_329, 0);
x_352 = lean_ctor_get(x_329, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_329);
x_353 = lean_io_error_to_string(x_351);
x_354 = 3;
x_355 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set_uint8(x_355, sizeof(void*)*1, x_354);
x_356 = lean_array_get_size(x_11);
x_357 = lean_array_push(x_11, x_355);
if (lean_is_scalar(x_14)) {
 x_358 = lean_alloc_ctor(0, 2, 1);
} else {
 x_358 = x_14;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_334);
lean_ctor_set_uint8(x_358, sizeof(void*)*2, x_12);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_358);
x_44 = x_359;
x_45 = x_352;
goto block_328;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__1), 6, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = l_Lake_BuildTrace_nil;
x_14 = l_Lake_Job_mapM___rarg(x_3, x_10, x_11, x_12, x_6, x_13, x_9);
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
lean_ctor_set(x_17, 1, x_7);
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
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_7);
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
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
lean_inc(x_8);
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = l_Lake_Module_depsFacetConfig___closed__4;
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, lean_box(0));
x_15 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__2___boxed), 9, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_8);
x_16 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13___rarg), 8, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = 0;
x_18 = l_Lake_withRegisterJob___rarg(x_11, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
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
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_15);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Module_recBuildLean___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_leanArtsFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacetConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_leanArtsFacetConfig___closed__3;
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
x_1 = l_Lake_Module_leanArtsFacetConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
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
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 9);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_System_FilePath_join(x_11, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___lambda__1___closed__1;
x_16 = l_Lean_modToFilePath(x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
x_17 = 0;
lean_inc(x_16);
x_18 = l_Lake_fetchFileTrace(x_16, x_17, x_3, x_4, x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_20, 1);
x_28 = l_Lake_BuildTrace_mix(x_27, x_24);
lean_ctor_set(x_20, 1, x_28);
lean_ctor_set(x_19, 0, x_16);
return x_18;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_29);
lean_dec(x_20);
x_32 = l_Lake_BuildTrace_mix(x_31, x_24);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_30);
lean_ctor_set(x_19, 1, x_33);
lean_ctor_set(x_19, 0, x_16);
return x_18;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_38 = x_20;
} else {
 lean_dec_ref(x_20);
 x_38 = lean_box(0);
}
x_39 = l_Lake_BuildTrace_mix(x_37, x_34);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 1);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_18, 0, x_41);
return x_18;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_dec(x_18);
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_44 = x_19;
} else {
 lean_dec_ref(x_19);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_20, 0);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
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
x_49 = l_Lake_BuildTrace_mix(x_47, x_43);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 1);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_46);
if (lean_is_scalar(x_44)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_44;
}
lean_ctor_set(x_51, 0, x_16);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_18, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_19);
if (x_55 == 0)
{
return x_18;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_19, 0);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_18, 0, x_58);
return x_18;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_18, 1);
lean_inc(x_59);
lean_dec(x_18);
x_60 = lean_ctor_get(x_19, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_19, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_62 = x_19;
} else {
 lean_dec_ref(x_19);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_4);
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
x_16 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed), 5, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = l_Lake_BuildTrace_nil;
x_20 = l_Lake_Job_mapM___rarg(x_14, x_16, x_17, x_18, x_4, x_19, x_12);
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
x_32 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed), 5, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = l_Lake_BuildTrace_nil;
x_36 = l_Lake_Job_mapM___rarg(x_30, x_32, x_33, x_34, x_4, x_35, x_12);
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
lean_dec(x_4);
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
lean_dec(x_4);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oleanFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_oleanFacetConfig___closed__1;
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
x_1 = l_Lake_Module_oleanFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
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
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 9);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_System_FilePath_join(x_11, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_Module_clearOutputHashes___closed__1;
x_16 = l_Lean_modToFilePath(x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
x_17 = 0;
lean_inc(x_16);
x_18 = l_Lake_fetchFileTrace(x_16, x_17, x_3, x_4, x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_20, 1);
x_28 = l_Lake_BuildTrace_mix(x_27, x_24);
lean_ctor_set(x_20, 1, x_28);
lean_ctor_set(x_19, 0, x_16);
return x_18;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_29);
lean_dec(x_20);
x_32 = l_Lake_BuildTrace_mix(x_31, x_24);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_30);
lean_ctor_set(x_19, 1, x_33);
lean_ctor_set(x_19, 0, x_16);
return x_18;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_38 = x_20;
} else {
 lean_dec_ref(x_20);
 x_38 = lean_box(0);
}
x_39 = l_Lake_BuildTrace_mix(x_37, x_34);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 1);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_18, 0, x_41);
return x_18;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_dec(x_18);
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_44 = x_19;
} else {
 lean_dec_ref(x_19);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_20, 0);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
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
x_49 = l_Lake_BuildTrace_mix(x_47, x_43);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 1);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_46);
if (lean_is_scalar(x_44)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_44;
}
lean_ctor_set(x_51, 0, x_16);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_18, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_19);
if (x_55 == 0)
{
return x_18;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_19, 0);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_18, 0, x_58);
return x_18;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_18, 1);
lean_inc(x_59);
lean_dec(x_18);
x_60 = lean_ctor_get(x_19, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_19, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_62 = x_19;
} else {
 lean_dec_ref(x_19);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_4);
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
x_16 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1___boxed), 5, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = l_Lake_BuildTrace_nil;
x_20 = l_Lake_Job_mapM___rarg(x_14, x_16, x_17, x_18, x_4, x_19, x_12);
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
x_32 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1___boxed), 5, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = l_Lake_BuildTrace_nil;
x_36 = l_Lake_Job_mapM___rarg(x_30, x_32, x_33, x_34, x_4, x_35, x_12);
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
lean_dec(x_4);
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
lean_dec(x_4);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_ileanFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_ileanFacetConfig___closed__2;
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
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
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 12);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_System_FilePath_join(x_11, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_Module_clearOutputHashes___closed__2;
x_16 = l_Lean_modToFilePath(x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
x_17 = 0;
lean_inc(x_16);
x_18 = l_Lake_fetchFileTrace(x_16, x_17, x_3, x_4, x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 2);
lean_inc(x_28);
lean_dec(x_3);
x_29 = l_Lake_BuildTrace_mix(x_24, x_28);
lean_ctor_set(x_20, 1, x_29);
lean_ctor_set(x_19, 0, x_16);
return x_18;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_ctor_get(x_3, 2);
lean_inc(x_32);
lean_dec(x_3);
x_33 = l_Lake_BuildTrace_mix(x_24, x_32);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_31);
lean_ctor_set(x_19, 1, x_34);
lean_ctor_set(x_19, 0, x_16);
return x_18;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_19, 0);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_ctor_get(x_20, 0);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_38 = x_20;
} else {
 lean_dec_ref(x_20);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_3, 2);
lean_inc(x_39);
lean_dec(x_3);
x_40 = l_Lake_BuildTrace_mix(x_35, x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 1);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_37);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_16);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_18, 0, x_42);
return x_18;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_ctor_get(x_19, 0);
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
x_47 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_48 = x_20;
} else {
 lean_dec_ref(x_20);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_3, 2);
lean_inc(x_49);
lean_dec(x_3);
x_50 = l_Lake_BuildTrace_mix(x_44, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 1);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_47);
if (lean_is_scalar(x_45)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_45;
}
lean_ctor_set(x_52, 0, x_16);
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
lean_dec(x_16);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_18);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_18, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
return x_18;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_19, 0);
x_58 = lean_ctor_get(x_19, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_18, 0, x_59);
return x_18;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_dec(x_18);
x_61 = lean_ctor_get(x_19, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_63 = x_19;
} else {
 lean_dec_ref(x_19);
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
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_4);
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
x_16 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed), 5, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = l_Lake_BuildTrace_nil;
x_20 = l_Lake_Job_mapM___rarg(x_14, x_16, x_17, x_18, x_4, x_19, x_12);
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
x_32 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed), 5, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = l_Lake_BuildTrace_nil;
x_36 = l_Lake_Job_mapM___rarg(x_30, x_32, x_33, x_34, x_4, x_35, x_12);
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
lean_dec(x_4);
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
lean_dec(x_4);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_cFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_cFacetConfig___closed__2;
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
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
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 12);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_System_FilePath_join(x_11, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_Module_clearOutputHashes___closed__4;
x_16 = l_Lean_modToFilePath(x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
x_17 = 0;
lean_inc(x_16);
x_18 = l_Lake_fetchFileTrace(x_16, x_17, x_3, x_4, x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_20, 1);
lean_dec(x_27);
lean_ctor_set(x_20, 1, x_24);
lean_ctor_set(x_19, 0, x_16);
return x_18;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_29);
lean_ctor_set(x_19, 1, x_30);
lean_ctor_set(x_19, 0, x_16);
return x_18;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_34 = x_20;
} else {
 lean_dec_ref(x_20);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 1);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_18, 0, x_36);
return x_18;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_dec(x_18);
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_39 = x_19;
} else {
 lean_dec_ref(x_19);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_42 = x_20;
} else {
 lean_dec_ref(x_20);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 1);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_16);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_18, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
return x_18;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_18, 0, x_51);
return x_18;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_dec(x_18);
x_53 = lean_ctor_get(x_19, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_19, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_55 = x_19;
} else {
 lean_dec_ref(x_19);
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
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Module_leanArtsFacetConfig___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_4);
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
x_16 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1___lambda__1___boxed), 5, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = l_Lake_BuildTrace_nil;
x_20 = l_Lake_Job_mapM___rarg(x_14, x_16, x_17, x_18, x_4, x_19, x_12);
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
x_32 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1___lambda__1___boxed), 5, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = l_Lake_BuildTrace_nil;
x_36 = l_Lake_Job_mapM___rarg(x_30, x_32, x_33, x_34, x_4, x_35, x_12);
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
lean_dec(x_4);
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
lean_dec(x_4);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_bcFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_bcFacetConfig___closed__2;
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Module_bcFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
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
x_25 = l_Lake_buildLeanO(x_20, x_7, x_23, x_6, x_10, x_24, x_13);
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
lean_ctor_set(x_28, 1, x_11);
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
lean_ctor_set(x_31, 1, x_11);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_11);
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
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
lean_dec(x_8);
x_10 = 2;
x_11 = l_Lake_instDecidableEqVerbosity(x_9, x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = 1;
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
lean_inc(x_12);
x_15 = l_Lean_Name_toString(x_12, x_13, x_14);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
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
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*9);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*9);
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
x_44 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13___rarg), 8, 2);
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
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
x_26 = lean_ctor_get_uint8(x_20, sizeof(void*)*9);
x_27 = lean_ctor_get_uint8(x_23, sizeof(void*)*9);
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
x_38 = l_Lake_buildLeanO(x_19, x_3, x_25, x_36, x_6, x_37, x_9);
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
lean_ctor_set(x_41, 1, x_7);
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
lean_ctor_set(x_44, 1, x_7);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_7);
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
x_56 = l_Lake_buildLeanO(x_19, x_3, x_25, x_54, x_6, x_55, x_9);
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
lean_ctor_set(x_59, 1, x_7);
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
lean_ctor_set(x_62, 1, x_7);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_7);
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
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
lean_dec(x_8);
x_10 = 2;
x_11 = l_Lake_instDecidableEqVerbosity(x_9, x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = 1;
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
lean_inc(x_12);
x_15 = l_Lean_Name_toString(x_12, x_13, x_14);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
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
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13___rarg), 8, 2);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
x_26 = lean_ctor_get_uint8(x_20, sizeof(void*)*9);
x_27 = lean_ctor_get_uint8(x_23, sizeof(void*)*9);
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
x_38 = l_Lake_buildLeanO(x_19, x_3, x_25, x_36, x_6, x_37, x_9);
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
lean_ctor_set(x_41, 1, x_7);
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
lean_ctor_set(x_44, 1, x_7);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_7);
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
x_56 = l_Lake_buildLeanO(x_19, x_3, x_25, x_54, x_6, x_55, x_9);
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
lean_ctor_set(x_59, 1, x_7);
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
lean_ctor_set(x_62, 1, x_7);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_7);
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
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
lean_inc(x_8);
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
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
x_20 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13___rarg), 8, 2);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_oNoExportFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_oNoExportFacetConfig___closed__2;
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_8);
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
lean_inc(x_9);
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
x_8 = x_22;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_9);
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
lean_dec(x_9);
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
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
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
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(x_1, x_15, x_14);
lean_dec(x_14);
x_17 = l_Array_append___rarg(x_2, x_16);
lean_dec(x_16);
x_18 = lean_array_size(x_3);
x_19 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_18, x_4, x_3);
x_20 = lean_array_size(x_1);
x_21 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_20, x_4, x_1);
x_22 = l_Array_append___rarg(x_19, x_21);
lean_dec(x_21);
x_23 = lean_array_size(x_5);
x_24 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_23, x_4, x_5);
x_25 = lean_array_size(x_17);
x_26 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3(x_25, x_4, x_17);
x_27 = l_Array_append___rarg(x_24, x_26);
lean_dec(x_26);
x_28 = lean_array_size(x_22);
x_29 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4(x_28, x_4, x_22);
x_30 = l_Array_append___rarg(x_27, x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_6, 7);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_ctor_get(x_7, 7);
x_33 = l_Array_append___rarg(x_31, x_32);
x_34 = l_Array_append___rarg(x_30, x_33);
lean_dec(x_33);
x_35 = l_Array_append___rarg(x_34, x_8);
x_36 = lean_ctor_get(x_10, 18);
lean_inc(x_36);
x_37 = l_Array_append___rarg(x_35, x_36);
lean_dec(x_36);
x_38 = lean_ctor_get(x_10, 12);
lean_inc(x_38);
lean_dec(x_10);
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
x_42 = l_Lake_compileSharedLib(x_9, x_37, x_38, x_40, x_13);
lean_dec(x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
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
lean_object* x_47; 
x_47 = lean_ctor_get(x_43, 1);
lean_ctor_set(x_12, 0, x_47);
lean_ctor_set(x_43, 1, x_12);
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
lean_ctor_set(x_12, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_12);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_ctor_get(x_43, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_54 = x_43;
} else {
 lean_dec_ref(x_43);
 x_54 = lean_box(0);
}
lean_ctor_set(x_12, 0, x_53);
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_12);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_42, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_43);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_43, 1);
lean_ctor_set(x_12, 0, x_60);
lean_ctor_set(x_43, 1, x_12);
return x_42;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_43);
lean_ctor_set(x_12, 0, x_62);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_12);
lean_ctor_set(x_42, 0, x_63);
return x_42;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_dec(x_42);
x_65 = lean_ctor_get(x_43, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_43, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_67 = x_43;
} else {
 lean_dec_ref(x_43);
 x_67 = lean_box(0);
}
lean_ctor_set(x_12, 0, x_66);
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_12);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_free_object(x_12);
lean_dec(x_41);
x_70 = !lean_is_exclusive(x_42);
if (x_70 == 0)
{
return x_42;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_42, 0);
x_72 = lean_ctor_get(x_42, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_42);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_12, 0);
x_75 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_inc(x_74);
lean_dec(x_12);
x_77 = l_Lake_compileSharedLib(x_9, x_37, x_38, x_74, x_13);
lean_dec(x_37);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
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
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
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
x_84 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_76);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_75);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
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
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_88 = x_77;
} else {
 lean_dec_ref(x_77);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_78, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_91 = x_78;
} else {
 lean_dec_ref(x_78);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_76);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_75);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
if (lean_is_scalar(x_88)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_88;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_87);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_76);
x_95 = lean_ctor_get(x_77, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_97 = x_77;
} else {
 lean_dec_ref(x_77);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; 
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_17 = x_11;
} else {
 lean_dec_ref(x_11);
 x_17 = lean_box(0);
}
x_18 = l_Lake_BuildTrace_mix(x_16, x_13);
x_19 = l_Lake_Module_recBuildDeps___lambda__2___closed__3;
x_20 = l_Lake_BuildTrace_mix(x_18, x_19);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 6);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 6);
lean_inc(x_25);
x_26 = l_Array_append___rarg(x_23, x_25);
lean_dec(x_25);
x_27 = lean_array_get_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_ctor_get(x_21, 8);
lean_inc(x_31);
x_32 = l_System_FilePath_join(x_30, x_31);
lean_dec(x_31);
x_33 = lean_ctor_get(x_21, 10);
lean_inc(x_33);
lean_dec(x_21);
x_34 = l_System_FilePath_join(x_32, x_33);
lean_dec(x_33);
x_35 = l_Lake_Module_recBuildDynlib___lambda__3___closed__1;
x_36 = 1;
x_37 = l_Lean_Name_toStringWithSep(x_35, x_36, x_3, x_4);
x_38 = l_Lake_Module_dynlibSuffix;
x_39 = lean_string_append(x_37, x_38);
x_40 = l_Lake_nameToSharedLib(x_39);
x_41 = l_System_FilePath_join(x_34, x_40);
lean_dec(x_40);
x_42 = lean_box_usize(x_7);
lean_inc(x_41);
lean_inc(x_26);
x_43 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__2___boxed), 13, 9);
lean_closure_set(x_43, 0, x_9);
lean_closure_set(x_43, 1, x_5);
lean_closure_set(x_43, 2, x_6);
lean_closure_set(x_43, 3, x_42);
lean_closure_set(x_43, 4, x_8);
lean_closure_set(x_43, 5, x_22);
lean_closure_set(x_43, 6, x_24);
lean_closure_set(x_43, 7, x_26);
lean_closure_set(x_43, 8, x_41);
x_44 = l_Lake_Module_recBuildDynlib___lambda__3___closed__2;
x_45 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate_x27___spec__1___rarg), 5, 2);
lean_closure_set(x_45, 0, x_44);
lean_closure_set(x_45, 1, x_43);
if (x_29 == 0)
{
uint64_t x_86; 
lean_dec(x_27);
lean_dec(x_26);
x_86 = l_Lake_Hash_nil;
x_46 = x_86;
goto block_85;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_27, x_27);
if (x_87 == 0)
{
uint64_t x_88; 
lean_dec(x_27);
lean_dec(x_26);
x_88 = l_Lake_Hash_nil;
x_46 = x_88;
goto block_85;
}
else
{
size_t x_89; uint64_t x_90; uint64_t x_91; 
x_89 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_90 = l_Lake_Hash_nil;
x_91 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(x_26, x_7, x_89, x_90);
lean_dec(x_26);
x_46 = x_91;
goto block_85;
}
}
block_85:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_47 = l_Lake_Module_recBuildDeps___lambda__2___closed__2;
x_48 = lean_box_uint64(x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lake_BuildTrace_mix(x_20, x_49);
if (lean_is_scalar(x_17)) {
 x_51 = lean_alloc_ctor(0, 2, 1);
} else {
 x_51 = x_17;
}
lean_ctor_set(x_51, 0, x_14);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_15);
x_52 = 0;
lean_inc(x_41);
x_53 = l_Lake_buildFileUnlessUpToDate_x27(x_41, x_45, x_52, x_10, x_51, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 0);
lean_dec(x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_41);
lean_ctor_set(x_59, 1, x_39);
lean_ctor_set(x_54, 0, x_59);
return x_53;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_39);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_53, 0, x_62);
return x_53;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_dec(x_53);
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
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_41);
lean_ctor_set(x_66, 1, x_39);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_41);
lean_dec(x_39);
x_69 = !lean_is_exclusive(x_53);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_53, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_54);
if (x_71 == 0)
{
return x_53;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_54, 0);
x_73 = lean_ctor_get(x_54, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_54);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_53, 0, x_74);
return x_53;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_53, 1);
lean_inc(x_75);
lean_dec(x_53);
x_76 = lean_ctor_get(x_54, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_54, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_78 = x_54;
} else {
 lean_dec_ref(x_54);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_41);
lean_dec(x_39);
x_81 = !lean_is_exclusive(x_53);
if (x_81 == 0)
{
return x_53;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_53, 0);
x_83 = lean_ctor_get(x_53, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_53);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_box_usize(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 12, 8);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_9);
lean_closure_set(x_14, 6, x_13);
lean_closure_set(x_14, 7, x_7);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = l_Task_Priority_default;
x_17 = 0;
x_18 = l_Lake_Job_mapM___rarg(x_8, x_14, x_16, x_17, x_10, x_15, x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_box_usize(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__4___boxed), 12, 8);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_13);
lean_closure_set(x_14, 6, x_9);
lean_closure_set(x_14, 7, x_7);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = l_Task_Priority_default;
x_17 = 0;
x_18 = l_Lake_Job_bindM___rarg(x_8, x_14, x_16, x_17, x_10, x_15, x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_4);
x_12 = 0;
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_array_get_size(x_4);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (x_20 == 0)
{
lean_object* x_116; 
lean_dec(x_18);
lean_dec(x_4);
x_116 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_23 = x_116;
goto block_115;
}
else
{
uint8_t x_117; 
x_117 = lean_nat_dec_le(x_18, x_18);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_18);
lean_dec(x_4);
x_118 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_23 = x_118;
goto block_115;
}
else
{
size_t x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_120 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_121 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__12(x_4, x_12, x_119, x_120);
lean_dec(x_4);
x_23 = x_121;
goto block_115;
}
}
block_115:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_22);
x_24 = l_Lake_OrdHashSet_insert___at_Lake_Module_recBuildDeps___spec__6(x_23, x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Lake_recBuildExternDynlibs(x_25, x_5, x_6, x_7, x_17, x_9, x_15);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_33, 8);
lean_inc(x_34);
x_35 = 1;
x_36 = lean_box(x_35);
x_37 = lean_apply_1(x_34, x_36);
x_38 = lean_array_size(x_37);
lean_inc(x_7);
x_39 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1(x_1, x_38, x_12, x_37, x_5, x_6, x_7, x_30, x_9, x_29);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
x_45 = l_Lake_Job_collectArray___rarg(x_43);
lean_dec(x_43);
x_46 = l_Lake_Job_collectArray___rarg(x_16);
lean_dec(x_16);
x_47 = l_Lake_Job_collectArray___rarg(x_31);
lean_dec(x_31);
x_48 = l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1;
x_49 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__5___boxed), 12, 8);
lean_closure_set(x_49, 0, x_22);
lean_closure_set(x_49, 1, x_33);
lean_closure_set(x_49, 2, x_2);
lean_closure_set(x_49, 3, x_3);
lean_closure_set(x_49, 4, x_32);
lean_closure_set(x_49, 5, x_48);
lean_closure_set(x_49, 6, x_47);
lean_closure_set(x_49, 7, x_46);
x_50 = l_Task_Priority_default;
x_51 = 0;
x_52 = l_Lake_BuildTrace_nil;
x_53 = l_Lake_Job_bindM___rarg(x_45, x_49, x_50, x_51, x_7, x_52, x_41);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_ctor_set(x_40, 0, x_55);
lean_ctor_set(x_53, 0, x_40);
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
lean_ctor_set(x_40, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_40);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_free_object(x_40);
lean_dec(x_44);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_40, 0);
x_64 = lean_ctor_get(x_40, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_40);
x_65 = l_Lake_Job_collectArray___rarg(x_63);
lean_dec(x_63);
x_66 = l_Lake_Job_collectArray___rarg(x_16);
lean_dec(x_16);
x_67 = l_Lake_Job_collectArray___rarg(x_31);
lean_dec(x_31);
x_68 = l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1;
x_69 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__5___boxed), 12, 8);
lean_closure_set(x_69, 0, x_22);
lean_closure_set(x_69, 1, x_33);
lean_closure_set(x_69, 2, x_2);
lean_closure_set(x_69, 3, x_3);
lean_closure_set(x_69, 4, x_32);
lean_closure_set(x_69, 5, x_68);
lean_closure_set(x_69, 6, x_67);
lean_closure_set(x_69, 7, x_66);
x_70 = l_Task_Priority_default;
x_71 = 0;
x_72 = l_Lake_BuildTrace_nil;
x_73 = l_Lake_Job_bindM___rarg(x_65, x_69, x_70, x_71, x_7, x_72, x_41);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
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
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_64);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_64);
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
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
}
else
{
uint8_t x_83; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_39);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_39, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_40);
if (x_85 == 0)
{
return x_39;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_40, 0);
x_87 = lean_ctor_get(x_40, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_40);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_39, 0, x_88);
return x_39;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_39, 1);
lean_inc(x_89);
lean_dec(x_39);
x_90 = lean_ctor_get(x_40, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_40, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_92 = x_40;
} else {
 lean_dec_ref(x_40);
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
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_39);
if (x_95 == 0)
{
return x_39;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_39, 0);
x_97 = lean_ctor_get(x_39, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_39);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_26);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_26, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_27);
if (x_101 == 0)
{
return x_26;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_27, 0);
x_103 = lean_ctor_get(x_27, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_27);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_26, 0, x_104);
return x_26;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_26, 1);
lean_inc(x_105);
lean_dec(x_26);
x_106 = lean_ctor_get(x_27, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_27, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_108 = x_27;
} else {
 lean_dec_ref(x_27);
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
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_26);
if (x_111 == 0)
{
return x_26;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_26, 0);
x_113 = lean_ctor_get(x_26, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_26);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_13);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_13, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_14);
if (x_124 == 0)
{
return x_13;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_14, 0);
x_126 = lean_ctor_get(x_14, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_14);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_13, 0, x_127);
return x_13;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_13, 1);
lean_inc(x_128);
lean_dec(x_13);
x_129 = lean_ctor_get(x_14, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_14, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_131 = x_14;
} else {
 lean_dec_ref(x_14);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_128);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_13);
if (x_134 == 0)
{
return x_13;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_13, 0);
x_136 = lean_ctor_get(x_13, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_13);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
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
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3;
lean_inc(x_8);
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lake_Module_recBuildDynlib___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, lean_box(0));
x_19 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__6), 10, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_8);
lean_closure_set(x_19, 2, x_10);
x_20 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_Module_recBuildDeps___spec__13___rarg), 8, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = 0;
x_22 = l_Lake_withRegisterJob___rarg(x_15, x_20, x_21, x_2, x_3, x_4, x_5, x_6, x_7);
return x_22;
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Module_recBuildDynlib___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; lean_object* x_15; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Lake_Module_recBuildDynlib___lambda__2(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Lake_Module_recBuildDynlib___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Lake_Module_recBuildDynlib___lambda__4(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Lake_Module_recBuildDynlib___lambda__5(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_dynlibFacetConfig___closed__1;
x_2 = l_Lake_Module_depsFacetConfig___closed__2;
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
x_1 = l_Lake_Module_dynlibFacetConfig___closed__2;
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
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2;
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
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2;
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
l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1);
l_Lake_recBuildExternDynlibs___closed__1 = _init_l_Lake_recBuildExternDynlibs___closed__1();
lean_mark_persistent(l_Lake_recBuildExternDynlibs___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__9___closed__3);
l_Lake_Module_recParseImports___closed__1 = _init_l_Lake_Module_recParseImports___closed__1();
lean_mark_persistent(l_Lake_Module_recParseImports___closed__1);
l_Lake_Module_recParseImports___closed__2 = _init_l_Lake_Module_recParseImports___closed__2();
lean_mark_persistent(l_Lake_Module_recParseImports___closed__2);
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
l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_collectImportsAux___spec__3___closed__4);
l_Lake_collectImportsAux___closed__1 = _init_l_Lake_collectImportsAux___closed__1();
lean_mark_persistent(l_Lake_collectImportsAux___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_Module_recComputeTransImports___spec__1___closed__2);
l_Lake_Module_transImportsFacetConfig___closed__1 = _init_l_Lake_Module_transImportsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig___closed__1);
l_Lake_Module_transImportsFacetConfig___closed__2 = _init_l_Lake_Module_transImportsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig___closed__2);
l_Lake_Module_transImportsFacetConfig = _init_l_Lake_Module_transImportsFacetConfig();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig);
l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_computePrecompileImportsAux___spec__1___closed__2);
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
l_Lake_Module_leanArtsFacetConfig = _init_l_Lake_Module_leanArtsFacetConfig();
lean_mark_persistent(l_Lake_Module_leanArtsFacetConfig);
l_Lake_Module_oleanFacetConfig___closed__1 = _init_l_Lake_Module_oleanFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig___closed__1);
l_Lake_Module_oleanFacetConfig___closed__2 = _init_l_Lake_Module_oleanFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_oleanFacetConfig___closed__2);
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
l_Lake_Module_recBuildDynlib___lambda__3___closed__1 = _init_l_Lake_Module_recBuildDynlib___lambda__3___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__3___closed__1);
l_Lake_Module_recBuildDynlib___lambda__3___closed__2 = _init_l_Lake_Module_recBuildDynlib___lambda__3___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__3___closed__2);
l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1 = _init_l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__6___boxed__const__1);
l_Lake_Module_recBuildDynlib___closed__1 = _init_l_Lake_Module_recBuildDynlib___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___closed__1);
l_Lake_Module_dynlibFacetConfig___closed__1 = _init_l_Lake_Module_dynlibFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_dynlibFacetConfig___closed__1);
l_Lake_Module_dynlibFacetConfig___closed__2 = _init_l_Lake_Module_dynlibFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_dynlibFacetConfig___closed__2);
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

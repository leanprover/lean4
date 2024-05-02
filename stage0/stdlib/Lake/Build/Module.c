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
static lean_object* l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__1;
extern lean_object* l_Lake_MTime_instOrd;
LEAN_EXPORT lean_object* l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__10___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Module_transImportsFacetConfig___closed__1;
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__4;
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1;
static lean_object* l_Lake_Module_recBuildLean___lambda__5___closed__3;
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig;
static lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLean___lambda__5___closed__4;
static lean_object* l_Lake_initModuleFacetConfigs___closed__2;
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__2;
extern lean_object* l_Lake_instOrdBuildType;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLean___closed__3;
lean_object* l_Lake_nameToSharedLib(lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__13;
static lean_object* l_Lake_Module_recBuildLean___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instBEqModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_List_squeeze___at_Lake_Module_recParseImports___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_Module_recBuildLean___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
static lean_object* l_Lake_Module_depsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__4;
uint64_t l_Lake_computeArrayHash___at_Lake_buildO___spec__1(lean_object*);
static lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_bcFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__5;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_transImportsFacetConfig;
static lean_object* l_Lake_Module_ileanFacetConfig___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_initModuleFacetConfigs___closed__10;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3(size_t, size_t, lean_object*);
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recBuildPrecompileDynlibs_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4(size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___boxed__const__1;
static uint8_t l_Lake_Module_recBuildLean___lambda__5___closed__6;
static lean_object* l_Lake_Module_recBuildDeps___lambda__1___closed__1;
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__9(lean_object*, lean_object*);
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__1;
lean_object* l_Lake_fetchFileTrace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(size_t, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___closed__1;
uint8_t l_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_bcFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__7;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___closed__1;
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__5;
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_recBuildPrecompileDynlibs_go___spec__13(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_ileanFacetConfig___closed__1;
static lean_object* l_Lake_Module_coExportFacetConfig___closed__5;
static lean_object* l_Lake_initModuleFacetConfigs___closed__5;
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_recBuildPrecompileDynlibs_go___spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint64_t l_Lake_platformTrace;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_compileSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashableModule___boxed(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lake_Module_getMTime(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1;
lean_object* l_Lake_Module_checkExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__10(lean_object*, lean_object*);
static lean_object* l_Lake_Module_oleanFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__12;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coExportFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig;
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_initModuleFacetConfigs;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1(lean_object*);
static lean_object* l_Lake_Module_coExportFacetConfig___closed__2;
static lean_object* l_Lake_Module_bcoFacetConfig___closed__3;
lean_object* l_Lake_BuildJob_collectArray___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacetConfig;
LEAN_EXPORT lean_object* l_Lake_recBuildPrecompileDynlibs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
static lean_object* l_Lake_initModuleFacetConfigs___closed__1;
static lean_object* l_Lake_Module_oExportFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig;
lean_object* l_Function_const___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__16;
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_Module_ileanFacetConfig___closed__3;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__2;
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLean___lambda__1___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__1;
static lean_object* l_Lake_Module_recBuildDynlib___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_recBuildPrecompileDynlibs_go___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig;
static lean_object* l_Lake_Module_bcFacetConfig___closed__1;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Lake_Workspace_leanPath(lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_precompileImportsFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_Module_recBuildLean___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLean___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_recBuildPrecompileDynlibs_go___spec__14___at_Lake_recBuildPrecompileDynlibs_go___spec__15(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___lambda__1___closed__3;
static lean_object* l_Lake_Module_recBuildLeanBcToO___closed__1;
lean_object* l_Lake_cacheFileHash(lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__2;
static lean_object* l_Lake_Module_oFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
static lean_object* l_Lake_Module_cFacetConfig___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__1;
static lean_object* l_Lake_Module_oleanFacetConfig___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFacetConfig;
lean_object* l_Lake_replayBuildLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coExportFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__11(lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__17;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_recBuildPrecompileDynlibs_go___spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__5;
static lean_object* l_Lake_Module_cFacetConfig___closed__1;
static lean_object* l_Lake_Module_recBuildDynlib___lambda__1___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__1;
lean_object* l_Lake_EResult_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_coFacetConfig;
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__2;
static lean_object* l_Lake_Module_oNoExportFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_recBuildPrecompileDynlibs_go___spec__5___at_Lake_recBuildPrecompileDynlibs_go___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_oFacetConfig___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_importsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_bcoFacetConfig;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recComputeTransImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recParseImports___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1___closed__3___boxed__const__1;
static lean_object* l_Lake_Module_coExportFacetConfig___closed__1;
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__1;
static lean_object* l_Lake_Module_recParseImports___closed__1;
static lean_object* l_Lake_Module_depsFacetConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_recBuildExternDynlibs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recBuildExternDynlibs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__6;
LEAN_EXPORT lean_object* l_Lake_Module_depsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___boxed__const__1;
static lean_object* l_Lake_Module_cFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_leanArtsFacetConfig___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__4;
lean_object* l_Lake_EquipT_lift___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__2(lean_object*, lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__14;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLean___lambda__5___closed__5;
LEAN_EXPORT lean_object* l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_recBuildPrecompileDynlibs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDynlib___closed__1;
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
static lean_object* l_Lake_Module_oleanFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLeanCToONoExport___closed__1;
uint8_t l_Lake_Backend_orPreferLeft(uint8_t, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_recBuildExternDynlibs___closed__1;
static lean_object* l_Lake_initModuleFacetConfigs___closed__11;
static lean_object* l_Lake_Module_bcoFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLean___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_depsFacetConfig___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterMapTR_go___at_Lake_Module_recParseImports___spec__5___closed__1;
lean_object* l_Lake_BuildJob_mixArray___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___at_Lake_Module_recBuildLean___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2;
static lean_object* l_Lake_Module_oleanFacetConfig___closed__4;
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_recBuildPrecompileDynlibs_go___spec__3(lean_object*, lean_object*);
uint8_t l_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coFacetConfig___closed__2;
extern lean_object* l_Lake_Module_dynlibSuffix;
lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_addModuleFacetConfig___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instHashablePackage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_oleanFacetConfig___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_recBuildPrecompileDynlibs___closed__1;
static lean_object* l_Lake_Module_transImportsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_recBuildPrecompileDynlibs_go___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_precompileImportsFacetConfig___closed__1;
static lean_object* l_Lake_Module_coFacetConfig___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
LEAN_EXPORT lean_object* l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__3;
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_object* l_Lake_Module_recBuildLean___closed__4;
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___closed__1;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig;
static lean_object* l_Lake_Module_recBuildLean___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_internal_has_llvm_backend(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_Module_recBuildDeps___lambda__1___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacetConfig;
static lean_object* l_Lake_Module_coNoExportFacetConfig___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_cacheBuildLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instBEqPackage___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coFacetConfig___closed__3;
static lean_object* l_Lake_Module_precompileImportsFacetConfig___closed__2;
static lean_object* l_Lake_Module_recParseImports___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
extern uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Module_oExportFacetConfig___closed__3;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacetConfig;
static lean_object* l_Lake_Module_depsFacetConfig___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_recComputePrecompileImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8___closed__2;
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_importsFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_Module_depsFacetConfig___closed__2;
static lean_object* l_Lake_initModuleFacetConfigs___closed__9;
lean_object* l_Lean_Name_toStringWithSep(lean_object*, uint8_t, lean_object*);
static uint8_t l_Lake_Module_recBuildLean___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_dynlibFacetConfig___spec__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___at_Lake_Module_recBuildLean___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildType_leancArgs(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Lake_Module_recParseImports___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__6;
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_Module_dynlibFacetConfig___closed__3;
static lean_object* l_Lake_Module_recBuildLeanCToOExport___closed__3;
lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___lambda__1(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__1;
lean_object* l_Lake_buildFileUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initModuleFacetConfigs___closed__15;
LEAN_EXPORT lean_object* l_Lake_recBuildPrecompileDynlibs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_leanArtsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_recBuildLean___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Module_coExportFacetConfig___closed__3;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oFacetConfig;
static lean_object* l_Lake_Module_bcoFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_6);
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
lean_inc(x_7);
lean_inc(x_5);
x_18 = lean_apply_6(x_4, x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
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
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_27 = lean_array_uset(x_16, x_2, x_23);
x_2 = x_26;
x_3 = x_27;
x_6 = x_24;
x_8 = x_22;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_7);
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
lean_dec(x_16);
lean_dec(x_7);
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
lean_object* x_11; lean_object* x_12; uint8_t x_45; 
x_45 = lean_usize_dec_lt(x_3, x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_7);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_9);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_10);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; lean_object* x_65; 
x_49 = lean_array_uget(x_1, x_3);
x_50 = lean_ctor_get(x_4, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_51);
lean_dec(x_4);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 8);
lean_inc(x_54);
x_55 = l_System_FilePath_join(x_52, x_54);
x_56 = lean_ctor_get(x_53, 10);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_System_FilePath_join(x_55, x_56);
x_58 = lean_array_push(x_51, x_57);
x_59 = lean_ctor_get(x_49, 10);
lean_inc(x_59);
x_60 = 0;
x_61 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_62 = l_Lean_RBNode_fold___at_Lake_recBuildExternDynlibs___spec__1(x_49, x_61, x_59);
lean_dec(x_59);
x_63 = lean_array_get_size(x_62);
x_64 = lean_usize_of_nat(x_63);
lean_dec(x_63);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_65 = l_Array_mapMUnsafe_map___at_Lake_recBuildExternDynlibs___spec__2(x_64, x_60, x_62, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = l_Array_append___rarg(x_50, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_58);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_67, 0, x_75);
x_11 = x_66;
x_12 = x_68;
goto block_44;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_67, 0);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_67);
x_78 = l_Array_append___rarg(x_50, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_58);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_66, 0, x_81);
x_11 = x_66;
x_12 = x_68;
goto block_44;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_66, 1);
lean_inc(x_82);
lean_dec(x_66);
x_83 = lean_ctor_get(x_67, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_67, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_85 = x_67;
} else {
 lean_dec_ref(x_67);
 x_85 = lean_box(0);
}
x_86 = l_Array_append___rarg(x_50, x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_58);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_82);
x_11 = x_90;
x_12 = x_68;
goto block_44;
}
}
else
{
lean_object* x_91; uint8_t x_92; 
lean_dec(x_58);
lean_dec(x_50);
x_91 = lean_ctor_get(x_65, 1);
lean_inc(x_91);
lean_dec(x_65);
x_92 = !lean_is_exclusive(x_66);
if (x_92 == 0)
{
x_11 = x_66;
x_12 = x_91;
goto block_44;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_66, 0);
x_94 = lean_ctor_get(x_66, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_66);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_11 = x_95;
x_12 = x_91;
goto block_44;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_96 = !lean_is_exclusive(x_65);
if (x_96 == 0)
{
return x_65;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_65, 0);
x_98 = lean_ctor_get(x_65, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_65);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
block_44:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
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
x_7 = x_33;
x_9 = x_32;
x_10 = x_12;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_12);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_12);
return x_43;
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
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_13, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_13, 0, x_30);
return x_12;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_33 = x_14;
} else {
 lean_dec_ref(x_14);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_dec(x_15);
if (lean_is_scalar(x_33)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_33;
}
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_12, 0, x_38);
return x_12;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_dec(x_12);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_41 = x_13;
} else {
 lean_dec_ref(x_13);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_43 = x_14;
} else {
 lean_dec_ref(x_14);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_dec(x_15);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
if (lean_is_scalar(x_41)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_41;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_12, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_13);
if (x_52 == 0)
{
return x_12;
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
lean_ctor_set(x_12, 0, x_55);
return x_12;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_dec(x_12);
x_57 = lean_ctor_get(x_13, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_59 = x_13;
} else {
 lean_dec_ref(x_13);
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
x_62 = !lean_is_exclusive(x_12);
if (x_62 == 0)
{
return x_12;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_12, 0);
x_64 = lean_ctor_get(x_12, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_12);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
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
LEAN_EXPORT uint8_t l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_recBuildPrecompileDynlibs_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_recBuildPrecompileDynlibs_go___spec__5___at_Lake_recBuildPrecompileDynlibs_go___spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_recBuildPrecompileDynlibs_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lake_recBuildPrecompileDynlibs_go___spec__5___at_Lake_recBuildPrecompileDynlibs_go___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_recBuildPrecompileDynlibs_go___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashSetImp_moveEntries___at_Lake_recBuildPrecompileDynlibs_go___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__7(x_7, x_2, x_3);
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
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_name_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__7(x_13, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__2(x_2, x_10);
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
x_17 = l_Lean_HashSetImp_expand___at_Lake_recBuildPrecompileDynlibs_go___spec__3(x_13, x_15);
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
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_inc(x_2);
x_18 = l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__7(x_10, x_2, x_2);
lean_dec(x_2);
x_19 = lean_array_uset(x_5, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_24 = l_Lean_Name_hash___override(x_23);
lean_dec(x_23);
lean_inc(x_22);
x_25 = lean_hashset_mk_idx(x_22, x_24);
x_26 = lean_array_uget(x_21, x_25);
x_27 = l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__2(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_20, x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_26);
x_31 = lean_array_uset(x_21, x_25, x_30);
x_32 = lean_nat_dec_le(x_29, x_22);
lean_dec(x_22);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_HashSetImp_expand___at_Lake_recBuildPrecompileDynlibs_go___spec__3(x_29, x_31);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_22);
lean_inc(x_2);
x_35 = l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__7(x_26, x_2, x_2);
lean_dec(x_2);
x_36 = lean_array_uset(x_21, x_25, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__10(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_hash___override(x_6);
lean_dec(x_6);
x_8 = lean_hashset_mk_idx(x_4, x_7);
x_9 = lean_array_uget(x_3, x_8);
lean_dec(x_3);
x_10 = l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__10(x_2, x_9);
lean_dec(x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_recBuildPrecompileDynlibs_go___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_recBuildPrecompileDynlibs_go___spec__14___at_Lake_recBuildPrecompileDynlibs_go___spec__15(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lake_recBuildPrecompileDynlibs_go___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lake_recBuildPrecompileDynlibs_go___spec__14___at_Lake_recBuildPrecompileDynlibs_go___spec__15(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lake_recBuildPrecompileDynlibs_go___spec__12(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashSetImp_moveEntries___at_Lake_recBuildPrecompileDynlibs_go___spec__13(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_10, 2);
x_12 = lean_name_eq(x_9, x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__16(x_7, x_2, x_3);
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
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_18, 2);
x_20 = lean_name_eq(x_17, x_19);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__16(x_15, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__11(lean_object* x_1, lean_object* x_2) {
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
x_12 = l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__10(x_2, x_11);
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
x_18 = l_Lean_HashSetImp_expand___at_Lake_recBuildPrecompileDynlibs_go___spec__12(x_14, x_16);
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
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_inc(x_2);
x_19 = l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__16(x_11, x_2, x_2);
lean_dec(x_2);
x_20 = lean_array_uset(x_5, x_10, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Name_hash___override(x_25);
lean_dec(x_25);
lean_inc(x_23);
x_27 = lean_hashset_mk_idx(x_23, x_26);
x_28 = lean_array_uget(x_22, x_27);
x_29 = l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__10(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_21, x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_array_uset(x_22, x_27, x_32);
x_34 = lean_nat_dec_le(x_31, x_23);
lean_dec(x_23);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_HashSetImp_expand___at_Lake_recBuildPrecompileDynlibs_go___spec__12(x_31, x_33);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_23);
lean_inc(x_2);
x_37 = l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__16(x_28, x_2, x_2);
lean_dec(x_2);
x_38 = lean_array_uset(x_22, x_27, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashablePackage___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqPackage___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_3);
x_4 = l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__9(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = lean_array_push(x_5, x_2);
x_7 = l_Lean_HashSetImp_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__11(x_3, x_2);
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
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__17(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_Name_hash___override(x_5);
lean_dec(x_5);
x_7 = lean_hashset_mk_idx(x_4, x_6);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("imports", 7);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_8);
x_15 = lean_apply_6(x_7, x_14, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_22 = l_Lake_recBuildPrecompileDynlibs_go(x_20, x_5, x_4, x_3, x_2, x_7, x_8, x_21, x_10, x_19, x_18);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_22, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_23, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_26, 1, x_31);
lean_ctor_set(x_26, 0, x_38);
lean_ctor_set(x_23, 0, x_26);
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
lean_ctor_set(x_23, 0, x_44);
return x_22;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_23, 1);
lean_inc(x_45);
lean_dec(x_23);
x_46 = lean_ctor_get(x_24, 1);
lean_inc(x_46);
lean_dec(x_24);
x_47 = lean_ctor_get(x_25, 0);
lean_inc(x_47);
lean_dec(x_25);
x_48 = lean_ctor_get(x_26, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_50 = x_26;
} else {
 lean_dec_ref(x_26);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_47);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_50;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
lean_ctor_set(x_22, 0, x_55);
return x_22;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
x_57 = lean_ctor_get(x_23, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_58 = x_23;
} else {
 lean_dec_ref(x_23);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
lean_dec(x_24);
x_60 = lean_ctor_get(x_25, 0);
lean_inc(x_60);
lean_dec(x_25);
x_61 = lean_ctor_get(x_26, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_26, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_63 = x_26;
} else {
 lean_dec_ref(x_26);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_60);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_59);
if (lean_is_scalar(x_58)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_58;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_57);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_56);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_22);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_22, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_23);
if (x_72 == 0)
{
return x_22;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_23, 0);
x_74 = lean_ctor_get(x_23, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_23);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_22, 0, x_75);
return x_22;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_22, 1);
lean_inc(x_76);
lean_dec(x_22);
x_77 = lean_ctor_get(x_23, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_23, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_79 = x_23;
} else {
 lean_dec_ref(x_23);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_22);
if (x_82 == 0)
{
return x_22;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_22, 0);
x_84 = lean_ctor_get(x_22, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_22);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_15);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_15, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_16);
if (x_88 == 0)
{
return x_15;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_16, 0);
x_90 = lean_ctor_get(x_16, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_16);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_15, 0, x_91);
return x_15;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_15, 1);
lean_inc(x_92);
lean_dec(x_15);
x_93 = lean_ctor_get(x_16, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_16, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_95 = x_16;
} else {
 lean_dec_ref(x_16);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = !lean_is_exclusive(x_15);
if (x_98 == 0)
{
return x_15;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_15, 0);
x_100 = lean_ctor_get(x_15, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_15);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dynlib", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
lean_inc(x_1);
x_13 = l_Lean_HashSetImp_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__1(x_4, x_1);
if (x_2 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 2);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*17);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*9);
lean_dec(x_53);
x_14 = x_54;
goto block_48;
}
else
{
uint8_t x_55; 
lean_dec(x_49);
x_55 = 1;
x_14 = x_55;
goto block_48;
}
}
else
{
uint8_t x_56; 
x_56 = 1;
x_14 = x_56;
goto block_48;
}
block_48:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1(x_1, x_14, x_3, x_13, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8(x_5, x_18);
x_20 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__2;
lean_inc(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_7);
lean_inc(x_10);
lean_inc(x_8);
x_22 = lean_apply_6(x_7, x_21, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
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
x_29 = lean_array_push(x_3, x_27);
x_30 = lean_box(0);
x_31 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1(x_1, x_14, x_29, x_13, x_19, x_30, x_7, x_8, x_28, x_10, x_26, x_25);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_22, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_22, 0, x_37);
return x_22;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
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
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_22);
if (x_44 == 0)
{
return x_22;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_22);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_8);
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
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_2, x_4);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_5, 1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_16);
lean_inc(x_21);
x_23 = l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__17(x_21, x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_18);
lean_free_object(x_5);
x_24 = lean_box(0);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2(x_16, x_1, x_20, x_21, x_22, x_24, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_27, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_26, 0, x_38);
return x_25;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_dec(x_26);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_41 = x_27;
} else {
 lean_dec_ref(x_27);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
lean_dec(x_28);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_25, 0, x_44);
return x_25;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_ctor_get(x_26, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_47 = x_26;
} else {
 lean_dec_ref(x_26);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_49 = x_27;
} else {
 lean_dec_ref(x_27);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_28, 0);
lean_inc(x_50);
lean_dec(x_28);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
if (lean_is_scalar(x_47)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_47;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_25, 1);
lean_inc(x_54);
lean_dec(x_25);
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_dec(x_26);
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
lean_dec(x_27);
x_57 = lean_ctor_get(x_28, 0);
lean_inc(x_57);
lean_dec(x_28);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_8 = x_56;
x_10 = x_55;
x_11 = x_54;
goto _start;
}
}
else
{
uint8_t x_61; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_61 = !lean_is_exclusive(x_25);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_25, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_26);
if (x_63 == 0)
{
return x_25;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_26, 0);
x_65 = lean_ctor_get(x_26, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_26);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_25, 0, x_66);
return x_25;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_dec(x_25);
x_68 = lean_ctor_get(x_26, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_26, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_70 = x_26;
} else {
 lean_dec_ref(x_26);
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
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_73 = !lean_is_exclusive(x_25);
if (x_73 == 0)
{
return x_25;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_25, 0);
x_75 = lean_ctor_get(x_25, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_25);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
size_t x_77; size_t x_78; 
lean_dec(x_16);
x_77 = 1;
x_78 = lean_usize_add(x_4, x_77);
x_4 = x_78;
goto _start;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_5, 0);
x_81 = lean_ctor_get(x_18, 0);
x_82 = lean_ctor_get(x_18, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_18);
lean_inc(x_16);
lean_inc(x_81);
x_83 = l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__17(x_81, x_16);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_free_object(x_5);
x_84 = lean_box(0);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_85 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2(x_16, x_1, x_80, x_81, x_82, x_84, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_90 = x_85;
} else {
 lean_dec_ref(x_85);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_92 = x_86;
} else {
 lean_dec_ref(x_86);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_95);
lean_dec(x_88);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
if (lean_is_scalar(x_92)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_92;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
if (lean_is_scalar(x_90)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_90;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_89);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; size_t x_103; size_t x_104; 
x_99 = lean_ctor_get(x_85, 1);
lean_inc(x_99);
lean_dec(x_85);
x_100 = lean_ctor_get(x_86, 1);
lean_inc(x_100);
lean_dec(x_86);
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
lean_dec(x_87);
x_102 = lean_ctor_get(x_88, 0);
lean_inc(x_102);
lean_dec(x_88);
x_103 = 1;
x_104 = lean_usize_add(x_4, x_103);
x_4 = x_104;
x_5 = x_102;
x_8 = x_101;
x_10 = x_100;
x_11 = x_99;
goto _start;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_106 = lean_ctor_get(x_85, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_107 = x_85;
} else {
 lean_dec_ref(x_85);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_86, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_86, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_110 = x_86;
} else {
 lean_dec_ref(x_86);
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
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_113 = lean_ctor_get(x_85, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_85, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_115 = x_85;
} else {
 lean_dec_ref(x_85);
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
else
{
lean_object* x_117; size_t x_118; size_t x_119; 
lean_dec(x_16);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_81);
lean_ctor_set(x_117, 1, x_82);
lean_ctor_set(x_5, 1, x_117);
x_118 = 1;
x_119 = lean_usize_add(x_4, x_118);
x_4 = x_119;
goto _start;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_5, 1);
x_122 = lean_ctor_get(x_5, 0);
lean_inc(x_121);
lean_inc(x_122);
lean_dec(x_5);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_125 = x_121;
} else {
 lean_dec_ref(x_121);
 x_125 = lean_box(0);
}
lean_inc(x_16);
lean_inc(x_123);
x_126 = l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__17(x_123, x_16);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
x_127 = lean_box(0);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_128 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2(x_16, x_1, x_122, x_123, x_124, x_127, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_133 = x_128;
} else {
 lean_dec_ref(x_128);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_135 = x_129;
} else {
 lean_dec_ref(x_129);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_137 = x_130;
} else {
 lean_dec_ref(x_130);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_131, 0);
lean_inc(x_138);
lean_dec(x_131);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
if (lean_is_scalar(x_135)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_135;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_134);
if (lean_is_scalar(x_133)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_133;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_132);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; size_t x_146; size_t x_147; 
x_142 = lean_ctor_get(x_128, 1);
lean_inc(x_142);
lean_dec(x_128);
x_143 = lean_ctor_get(x_129, 1);
lean_inc(x_143);
lean_dec(x_129);
x_144 = lean_ctor_get(x_130, 1);
lean_inc(x_144);
lean_dec(x_130);
x_145 = lean_ctor_get(x_131, 0);
lean_inc(x_145);
lean_dec(x_131);
x_146 = 1;
x_147 = lean_usize_add(x_4, x_146);
x_4 = x_147;
x_5 = x_145;
x_8 = x_144;
x_10 = x_143;
x_11 = x_142;
goto _start;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_149 = lean_ctor_get(x_128, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_150 = x_128;
} else {
 lean_dec_ref(x_128);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_129, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_129, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_153 = x_129;
} else {
 lean_dec_ref(x_129);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_150;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_149);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_156 = lean_ctor_get(x_128, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_128, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_158 = x_128;
} else {
 lean_dec_ref(x_128);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; size_t x_162; size_t x_163; 
lean_dec(x_16);
if (lean_is_scalar(x_125)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_125;
}
lean_ctor_set(x_160, 0, x_123);
lean_ctor_set(x_160, 1, x_124);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_122);
lean_ctor_set(x_161, 1, x_160);
x_162 = 1;
x_163 = lean_usize_add(x_4, x_162);
x_4 = x_163;
x_5 = x_161;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recBuildPrecompileDynlibs_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18(x_5, x_1, x_15, x_16, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_19, 1);
x_28 = lean_ctor_get(x_19, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_19);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_18, 0, x_33);
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_18, 0, x_40);
return x_17;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_43 = x_19;
} else {
 lean_dec_ref(x_19);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_20, 0);
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_ctor_get(x_21, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_17, 0, x_50);
return x_17;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_dec(x_17);
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
x_56 = lean_ctor_get(x_20, 0);
lean_inc(x_56);
lean_dec(x_20);
x_57 = lean_ctor_get(x_21, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_dec(x_21);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_54);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_52);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_51);
return x_63;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_17);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_17, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
return x_17;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_18, 0);
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_18);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_17, 0, x_69);
return x_17;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_dec(x_17);
x_71 = lean_ctor_get(x_18, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_18, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_73 = x_18;
} else {
 lean_dec_ref(x_18);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
return x_75;
}
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_17);
if (x_76 == 0)
{
return x_17;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_17, 0);
x_78 = lean_ctor_get(x_17, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_17);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lake_recBuildPrecompileDynlibs_go___spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__9(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lake_recBuildPrecompileDynlibs_go___spec__16(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__17___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__17(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_recBuildPrecompileDynlibs_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lake_recBuildPrecompileDynlibs_go(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lake_recBuildPrecompileDynlibs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recBuildPrecompileDynlibs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_9 = l_Lake_recBuildPrecompileDynlibs___closed__1;
x_10 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_11 = 0;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lake_recBuildPrecompileDynlibs_go(x_1, x_8, x_9, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lake_recBuildExternDynlibs(x_24, x_2, x_3, x_19, x_5, x_18, x_17);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_ctor_set(x_27, 1, x_33);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_16, 1, x_34);
lean_ctor_set(x_16, 0, x_27);
lean_ctor_set(x_26, 0, x_16);
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_16, 1, x_36);
lean_ctor_set(x_16, 0, x_37);
lean_ctor_set(x_26, 0, x_16);
return x_25;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_41 = x_27;
} else {
 lean_dec_ref(x_27);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_16, 1, x_40);
lean_ctor_set(x_16, 0, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_25, 0, x_43);
return x_25;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_25, 1);
lean_inc(x_44);
lean_dec(x_25);
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_46 = x_26;
} else {
 lean_dec_ref(x_26);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_27, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_49 = x_27;
} else {
 lean_dec_ref(x_27);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_22);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_16, 1, x_48);
lean_ctor_set(x_16, 0, x_50);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_46;
}
lean_ctor_set(x_51, 0, x_16);
lean_ctor_set(x_51, 1, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_free_object(x_16);
lean_dec(x_22);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_25, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_26);
if (x_55 == 0)
{
return x_25;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_26, 0);
x_57 = lean_ctor_get(x_26, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_26);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_25, 0, x_58);
return x_25;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
lean_dec(x_25);
x_60 = lean_ctor_get(x_26, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_26, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_62 = x_26;
} else {
 lean_dec_ref(x_26);
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
else
{
uint8_t x_65; 
lean_free_object(x_16);
lean_dec(x_22);
x_65 = !lean_is_exclusive(x_25);
if (x_65 == 0)
{
return x_25;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_25, 0);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_25);
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
x_69 = lean_ctor_get(x_16, 1);
lean_inc(x_69);
lean_dec(x_16);
x_70 = lean_ctor_get(x_20, 1);
lean_inc(x_70);
lean_dec(x_20);
x_71 = l_Lake_recBuildExternDynlibs(x_70, x_2, x_3, x_19, x_5, x_18, x_17);
lean_dec(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
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
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
if (lean_is_scalar(x_77)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_77;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_76);
if (lean_is_scalar(x_75)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_75;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_74);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_69);
x_85 = lean_ctor_get(x_71, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_86 = x_71;
} else {
 lean_dec_ref(x_71);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_72, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_89 = x_72;
} else {
 lean_dec_ref(x_72);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_86;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_85);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_69);
x_92 = lean_ctor_get(x_71, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_71, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_94 = x_71;
} else {
 lean_dec_ref(x_71);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_12);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_12, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_13);
if (x_98 == 0)
{
return x_12;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_13, 0);
x_100 = lean_ctor_get(x_13, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_13);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_12, 0, x_101);
return x_12;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_12, 1);
lean_inc(x_102);
lean_dec(x_12);
x_103 = lean_ctor_get(x_13, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_13, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_105 = x_13;
} else {
 lean_dec_ref(x_13);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_12);
if (x_108 == 0)
{
return x_12;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_12, 0);
x_110 = lean_ctor_get(x_12, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_12);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recBuildPrecompileDynlibs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recBuildPrecompileDynlibs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
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
return x_9;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_9, 0, x_45);
return x_9;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_dec(x_9);
x_47 = lean_ctor_get(x_10, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_49 = x_10;
} else {
 lean_dec_ref(x_10);
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
x_52 = !lean_is_exclusive(x_9);
if (x_52 == 0)
{
return x_9;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_9, 0);
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_9);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
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
lean_inc(x_2);
lean_inc(x_3);
x_4 = l_Lean_HashSetImp_contains___at_Lake_recBuildPrecompileDynlibs_go___spec__17(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = lean_array_push(x_5, x_2);
x_7 = l_Lean_HashSetImp_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__1(x_3, x_2);
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
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
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
return x_9;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_9, 0, x_45);
return x_9;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_dec(x_9);
x_47 = lean_ctor_get(x_10, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_49 = x_10;
} else {
 lean_dec_ref(x_10);
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
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_9);
if (x_52 == 0)
{
return x_9;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_9, 0);
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_9);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lake_Module_recParseImports___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Functor_mapRev___at_Lake_Module_recParseImports___spec__3___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__3(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_Workspace_findModule_x3f), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__3;
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__2;
x_17 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg), 8, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg), 8, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lake_EquipT_map___at_Lake_Module_recParseImports___spec__1___rarg), 8, 2);
lean_closure_set(x_19, 0, x_14);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__3), 2, 1);
lean_closure_set(x_20, 0, x_4);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Functor_mapRev___at_Lake_Module_recParseImports___spec__3___rarg(x_19, x_20, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
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
x_28 = 1;
x_29 = lean_usize_add(x_2, x_28);
x_2 = x_29;
x_4 = x_26;
x_7 = x_27;
x_9 = x_25;
x_10 = x_24;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_21, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_21, 0, x_36);
return x_21;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_ctor_get(x_22, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_40 = x_22;
} else {
 lean_dec_ref(x_22);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_7);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_9);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_10);
return x_49;
}
}
}
static lean_object* _init_l_List_filterMapTR_go___at_Lake_Module_recParseImports___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Lake_Module_recParseImports___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(lean_box(0), x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = 1;
x_8 = l_Lean_Name_toString(x_6, x_7);
x_9 = l_List_filterMapTR_go___at_Lake_Module_recParseImports___spec__5___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_10, x_9);
x_12 = lean_array_push(x_2, x_11);
x_1 = x_5;
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_1 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_List_squeeze___at_Lake_Module_recParseImports___spec__6(lean_object* x_1) {
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lake_List_squeeze___at_Lake_Module_recParseImports___spec__6(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_string_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_free_object(x_1);
lean_dec(x_4);
return x_6;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_string_dec_eq(x_4, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_1, 1, x_14);
return x_1;
}
else
{
lean_object* x_15; 
lean_free_object(x_1);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = l_Lake_List_squeeze___at_Lake_Module_recParseImports___spec__6(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
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
x_24 = lean_string_dec_eq(x_16, x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_16);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
}
}
}
static lean_object* _init_l_Lake_Module_recParseImports___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ▸ ", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recParseImports___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recParseImports___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recParseImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_167 = lean_ctor_get(x_1, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 2);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_170, 7);
lean_inc(x_171);
lean_dec(x_170);
x_172 = l_System_FilePath_join(x_169, x_171);
x_173 = lean_ctor_get(x_167, 1);
lean_inc(x_173);
lean_dec(x_167);
x_174 = lean_ctor_get(x_173, 2);
lean_inc(x_174);
lean_dec(x_173);
x_175 = l_System_FilePath_join(x_172, x_174);
x_176 = lean_ctor_get(x_1, 1);
lean_inc(x_176);
lean_dec(x_1);
x_177 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1;
x_178 = l_Lean_modToFilePath(x_175, x_176, x_177);
x_179 = l_IO_FS_readFile(x_178, x_7);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_parseImports_x27(x_180, x_178, x_181);
lean_dec(x_178);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_4);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_6);
x_8 = x_186;
x_9 = x_184;
goto block_166;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_4);
x_187 = lean_ctor_get(x_182, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_182, 1);
lean_inc(x_188);
lean_dec(x_182);
x_189 = lean_io_error_to_string(x_187);
x_190 = 3;
x_191 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*1, x_190);
x_192 = lean_array_get_size(x_6);
x_193 = lean_array_push(x_6, x_191);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_8 = x_194;
x_9 = x_188;
goto block_166;
}
}
else
{
uint8_t x_195; 
lean_dec(x_178);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_179);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_196 = lean_ctor_get(x_179, 0);
x_197 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_198 = l_List_filterMapTR_go___at_Lake_Module_recParseImports___spec__5(x_3, x_197);
x_199 = l_Lake_List_squeeze___at_Lake_Module_recParseImports___spec__6(x_198);
x_200 = l_List_reverse___rarg(x_199);
x_201 = l_Lake_Module_recParseImports___closed__1;
x_202 = l_String_intercalate(x_201, x_200);
x_203 = l_Lake_Module_recParseImports___closed__2;
x_204 = lean_string_append(x_203, x_202);
lean_dec(x_202);
x_205 = l_Lake_Module_recParseImports___closed__3;
x_206 = lean_string_append(x_204, x_205);
x_207 = lean_io_error_to_string(x_196);
x_208 = lean_string_append(x_206, x_207);
lean_dec(x_207);
x_209 = lean_string_append(x_208, x_203);
x_210 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = lean_io_error_to_string(x_210);
x_212 = 3;
x_213 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set_uint8(x_213, sizeof(void*)*1, x_212);
x_214 = lean_array_get_size(x_6);
x_215 = lean_array_push(x_6, x_213);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set_tag(x_179, 0);
lean_ctor_set(x_179, 0, x_216);
return x_179;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_217 = lean_ctor_get(x_179, 0);
x_218 = lean_ctor_get(x_179, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_179);
x_219 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_220 = l_List_filterMapTR_go___at_Lake_Module_recParseImports___spec__5(x_3, x_219);
x_221 = l_Lake_List_squeeze___at_Lake_Module_recParseImports___spec__6(x_220);
x_222 = l_List_reverse___rarg(x_221);
x_223 = l_Lake_Module_recParseImports___closed__1;
x_224 = l_String_intercalate(x_223, x_222);
x_225 = l_Lake_Module_recParseImports___closed__2;
x_226 = lean_string_append(x_225, x_224);
lean_dec(x_224);
x_227 = l_Lake_Module_recParseImports___closed__3;
x_228 = lean_string_append(x_226, x_227);
x_229 = lean_io_error_to_string(x_217);
x_230 = lean_string_append(x_228, x_229);
lean_dec(x_229);
x_231 = lean_string_append(x_230, x_225);
x_232 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_232, 0, x_231);
x_233 = lean_io_error_to_string(x_232);
x_234 = 3;
x_235 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set_uint8(x_235, sizeof(void*)*1, x_234);
x_236 = lean_array_get_size(x_6);
x_237 = lean_array_push(x_6, x_235);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_218);
return x_239;
}
}
block_166:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_array_get_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
lean_ctor_set(x_11, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_16, x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
lean_ctor_set(x_11, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_11);
lean_free_object(x_8);
x_24 = 0;
x_25 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_26 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_27 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4(x_14, x_24, x_25, x_26, x_2, x_3, x_15, x_5, x_13, x_9);
lean_dec(x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_ctor_set(x_29, 0, x_36);
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_28, 0, x_40);
return x_27;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_44 = x_29;
} else {
 lean_dec_ref(x_29);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_27, 0, x_47);
return x_27;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_dec(x_27);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_50 = x_28;
} else {
 lean_dec_ref(x_28);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_29, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_53 = x_29;
} else {
 lean_dec_ref(x_29);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
if (lean_is_scalar(x_50)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_50;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_48);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_27, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_28);
if (x_60 == 0)
{
return x_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_28, 0);
x_62 = lean_ctor_get(x_28, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_28);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_27, 0, x_63);
return x_27;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
lean_dec(x_27);
x_65 = lean_ctor_get(x_28, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_67 = x_28;
} else {
 lean_dec_ref(x_28);
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
return x_69;
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_27);
if (x_70 == 0)
{
return x_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_27, 0);
x_72 = lean_ctor_get(x_27, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_27);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_8, 1);
x_75 = lean_ctor_get(x_11, 0);
x_76 = lean_ctor_get(x_11, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_11);
x_77 = lean_array_get_size(x_75);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_lt(x_78, x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_80 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
lean_ctor_set(x_8, 0, x_81);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_8);
lean_ctor_set(x_82, 1, x_9);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_84 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_76);
lean_ctor_set(x_8, 0, x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_8);
lean_ctor_set(x_86, 1, x_9);
return x_86;
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; 
lean_free_object(x_8);
x_87 = 0;
x_88 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_89 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_90 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4(x_75, x_87, x_88, x_89, x_2, x_3, x_76, x_5, x_74, x_9);
lean_dec(x_75);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
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
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
if (lean_is_scalar(x_96)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_96;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_95);
if (lean_is_scalar(x_94)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_94;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_93);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_90, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_105 = x_90;
} else {
 lean_dec_ref(x_90);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_91, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_91, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_108 = x_91;
} else {
 lean_dec_ref(x_91);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
if (lean_is_scalar(x_105)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_105;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_104);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_90, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_90, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_113 = x_90;
} else {
 lean_dec_ref(x_90);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_115 = lean_ctor_get(x_8, 0);
x_116 = lean_ctor_get(x_8, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_8);
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
x_120 = lean_array_get_size(x_117);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_nat_dec_lt(x_121, x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_123 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_119;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_118);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_116);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_9);
return x_126;
}
else
{
uint8_t x_127; 
x_127 = lean_nat_dec_le(x_120, x_120);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_128 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_119)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_119;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_118);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_116);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_9);
return x_131;
}
else
{
size_t x_132; size_t x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_119);
x_132 = 0;
x_133 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_134 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_135 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4(x_117, x_132, x_133, x_134, x_2, x_3, x_118, x_5, x_116, x_9);
lean_dec(x_117);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_141 = x_136;
} else {
 lean_dec_ref(x_136);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_137, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_137, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_144 = x_137;
} else {
 lean_dec_ref(x_137);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
if (lean_is_scalar(x_141)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_141;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_140);
if (lean_is_scalar(x_139)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_139;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_138);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_135, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_150 = x_135;
} else {
 lean_dec_ref(x_135);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_136, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_136, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_153 = x_136;
} else {
 lean_dec_ref(x_136);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_150;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_149);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_135, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_158 = x_135;
} else {
 lean_dec_ref(x_135);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_8);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_8);
lean_ctor_set(x_161, 1, x_9);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_8, 0);
x_163 = lean_ctor_get(x_8, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_8);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_9);
return x_165;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_1 = lean_alloc_closure((void*)(l_Lake_Module_importsFacetConfig___elambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_importsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_importsFacetConfig___closed__1;
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
x_1 = l_Lake_Module_importsFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2(x_2, x_7, x_8, x_1);
lean_dec(x_2);
return x_9;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("transImports", 12);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__2;
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_6);
x_15 = lean_apply_6(x_5, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
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
x_22 = l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(x_4, x_20);
x_23 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_22, x_12);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_4 = x_23;
x_7 = x_21;
x_9 = x_19;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_15, 0, x_32);
return x_15;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_36 = x_16;
} else {
 lean_dec_ref(x_16);
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
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_9);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_10);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recComputeTransImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_2);
lean_inc(x_5);
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
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
x_22 = lean_array_get_size(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
lean_ctor_set(x_12, 0, x_25);
return x_10;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
lean_ctor_set(x_12, 0, x_27);
return x_10;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_31 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3(x_20, x_28, x_29, x_30, x_2, x_3, x_21, x_5, x_17, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_ctor_set(x_33, 0, x_40);
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_48 = x_33;
} else {
 lean_dec_ref(x_33);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_31, 0, x_51);
return x_31;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_dec(x_31);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_54 = x_32;
} else {
 lean_dec_ref(x_32);
 x_54 = lean_box(0);
}
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
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_52);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_31, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
return x_31;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_32, 0);
x_66 = lean_ctor_get(x_32, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_32);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_31, 0, x_67);
return x_31;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_31, 1);
lean_inc(x_68);
lean_dec(x_31);
x_69 = lean_ctor_get(x_32, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_32, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_71 = x_32;
} else {
 lean_dec_ref(x_32);
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
x_74 = !lean_is_exclusive(x_31);
if (x_74 == 0)
{
return x_31;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_31, 0);
x_76 = lean_ctor_get(x_31, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_31);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_12, 0);
x_79 = lean_ctor_get(x_12, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_12);
x_80 = lean_array_get_size(x_78);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_nat_dec_lt(x_81, x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_83 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
lean_ctor_set(x_11, 0, x_84);
return x_10;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_80, x_80);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_86 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_11, 0, x_87);
return x_10;
}
else
{
size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_11);
lean_free_object(x_10);
x_88 = 0;
x_89 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_90 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_91 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3(x_78, x_88, x_89, x_90, x_2, x_3, x_79, x_5, x_17, x_14);
lean_dec(x_78);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_97 = x_92;
} else {
 lean_dec_ref(x_92);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_100 = x_93;
} else {
 lean_dec_ref(x_93);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_97;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
if (lean_is_scalar(x_95)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_95;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_94);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_91, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_106 = x_91;
} else {
 lean_dec_ref(x_91);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_92, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_92, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_109 = x_92;
} else {
 lean_dec_ref(x_92);
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
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_91, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_91, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_114 = x_91;
} else {
 lean_dec_ref(x_91);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_116 = lean_ctor_get(x_11, 1);
lean_inc(x_116);
lean_dec(x_11);
x_117 = lean_ctor_get(x_12, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_12, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_119 = x_12;
} else {
 lean_dec_ref(x_12);
 x_119 = lean_box(0);
}
x_120 = lean_array_get_size(x_117);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_nat_dec_lt(x_121, x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_123 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_119;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_118);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_116);
lean_ctor_set(x_10, 0, x_125);
return x_10;
}
else
{
uint8_t x_126; 
x_126 = lean_nat_dec_le(x_120, x_120);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_127 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_119)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_119;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_118);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_116);
lean_ctor_set(x_10, 0, x_129);
return x_10;
}
else
{
size_t x_130; size_t x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_119);
lean_free_object(x_10);
x_130 = 0;
x_131 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_132 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_133 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3(x_117, x_130, x_131, x_132, x_2, x_3, x_118, x_5, x_116, x_14);
lean_dec(x_117);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_139 = x_134;
} else {
 lean_dec_ref(x_134);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_142 = x_135;
} else {
 lean_dec_ref(x_135);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_141);
if (lean_is_scalar(x_139)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_139;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_138);
if (lean_is_scalar(x_137)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_137;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_136);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_147 = lean_ctor_get(x_133, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_148 = x_133;
} else {
 lean_dec_ref(x_133);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_134, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_134, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_151 = x_134;
} else {
 lean_dec_ref(x_134);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
if (lean_is_scalar(x_148)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_148;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_147);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_133, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_133, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_156 = x_133;
} else {
 lean_dec_ref(x_133);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_158 = lean_ctor_get(x_10, 1);
lean_inc(x_158);
lean_dec(x_10);
x_159 = lean_ctor_get(x_11, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_160 = x_11;
} else {
 lean_dec_ref(x_11);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_12, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_12, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_163 = x_12;
} else {
 lean_dec_ref(x_12);
 x_163 = lean_box(0);
}
x_164 = lean_array_get_size(x_161);
x_165 = lean_unsigned_to_nat(0u);
x_166 = lean_nat_dec_lt(x_165, x_164);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_167 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_163)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_163;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_162);
if (lean_is_scalar(x_160)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_160;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_159);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_158);
return x_170;
}
else
{
uint8_t x_171; 
x_171 = lean_nat_dec_le(x_164, x_164);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_172 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_163)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_163;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_162);
if (lean_is_scalar(x_160)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_160;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_159);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_158);
return x_175;
}
else
{
size_t x_176; size_t x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_163);
lean_dec(x_160);
x_176 = 0;
x_177 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_178 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_179 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3(x_161, x_176, x_177, x_178, x_2, x_3, x_162, x_5, x_159, x_158);
lean_dec(x_161);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_183 = x_179;
} else {
 lean_dec_ref(x_179);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_185 = x_180;
} else {
 lean_dec_ref(x_180);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_181, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_181, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_188 = x_181;
} else {
 lean_dec_ref(x_181);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
if (lean_is_scalar(x_185)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_185;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_184);
if (lean_is_scalar(x_183)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_183;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_182);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_193 = lean_ctor_get(x_179, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_194 = x_179;
} else {
 lean_dec_ref(x_179);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_180, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_180, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_197 = x_180;
} else {
 lean_dec_ref(x_180);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
if (lean_is_scalar(x_194)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_194;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_193);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_179, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_179, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_202 = x_179;
} else {
 lean_dec_ref(x_179);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_204 = !lean_is_exclusive(x_10);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_10, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_11);
if (x_206 == 0)
{
return x_10;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_11, 0);
x_208 = lean_ctor_get(x_11, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_11);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_10, 0, x_209);
return x_10;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_10, 1);
lean_inc(x_210);
lean_dec(x_10);
x_211 = lean_ctor_get(x_11, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_11, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_213 = x_11;
} else {
 lean_dec_ref(x_11);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_210);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_216 = !lean_is_exclusive(x_10);
if (x_216 == 0)
{
return x_10;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_10, 0);
x_218 = lean_ctor_get(x_10, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_10);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("precompileImports", 17);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_27; 
x_27 = lean_usize_dec_eq(x_2, x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_array_uget(x_1, x_2);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*17);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*9);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__2;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_6);
x_37 = lean_apply_6(x_5, x_36, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(x_4, x_44);
lean_ctor_set(x_39, 0, x_45);
x_11 = x_38;
x_12 = x_40;
goto block_26;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(x_4, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_38, 0, x_49);
x_11 = x_38;
x_12 = x_40;
goto block_26;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_53 = x_39;
} else {
 lean_dec_ref(x_39);
 x_53 = lean_box(0);
}
x_54 = l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(x_4, x_51);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
x_11 = x_56;
x_12 = x_40;
goto block_26;
}
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_4);
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_dec(x_37);
x_58 = !lean_is_exclusive(x_38);
if (x_58 == 0)
{
x_11 = x_38;
x_12 = x_57;
goto block_26;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_38, 0);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_38);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_11 = x_61;
x_12 = x_57;
goto block_26;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_37);
if (x_62 == 0)
{
return x_37;
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
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__2;
lean_inc(x_28);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_28);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_6);
x_68 = lean_apply_6(x_5, x_67, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_69, 0);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_70, 0);
x_76 = l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(x_4, x_75);
x_77 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_76, x_28);
lean_ctor_set(x_70, 0, x_77);
x_11 = x_69;
x_12 = x_71;
goto block_26;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_70, 0);
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_70);
x_80 = l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(x_4, x_78);
x_81 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_80, x_28);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
lean_ctor_set(x_69, 0, x_82);
x_11 = x_69;
x_12 = x_71;
goto block_26;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_69, 1);
lean_inc(x_83);
lean_dec(x_69);
x_84 = lean_ctor_get(x_70, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_70, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_86 = x_70;
} else {
 lean_dec_ref(x_70);
 x_86 = lean_box(0);
}
x_87 = l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(x_4, x_84);
x_88 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_87, x_28);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
x_11 = x_90;
x_12 = x_71;
goto block_26;
}
}
else
{
lean_object* x_91; uint8_t x_92; 
lean_dec(x_28);
lean_dec(x_4);
x_91 = lean_ctor_get(x_68, 1);
lean_inc(x_91);
lean_dec(x_68);
x_92 = !lean_is_exclusive(x_69);
if (x_92 == 0)
{
x_11 = x_69;
x_12 = x_91;
goto block_26;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_69, 0);
x_94 = lean_ctor_get(x_69, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_69);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_11 = x_95;
x_12 = x_91;
goto block_26;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_96 = !lean_is_exclusive(x_68);
if (x_96 == 0)
{
return x_68;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_68, 0);
x_98 = lean_ctor_get(x_68, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_68);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_29);
x_100 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__2;
lean_inc(x_28);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_28);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_6);
x_102 = lean_apply_6(x_5, x_101, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_103, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_104);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_104, 0);
x_110 = l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(x_4, x_109);
x_111 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_110, x_28);
lean_ctor_set(x_104, 0, x_111);
x_11 = x_103;
x_12 = x_105;
goto block_26;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_104, 0);
x_113 = lean_ctor_get(x_104, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_104);
x_114 = l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(x_4, x_112);
x_115 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_114, x_28);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
lean_ctor_set(x_103, 0, x_116);
x_11 = x_103;
x_12 = x_105;
goto block_26;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_103, 1);
lean_inc(x_117);
lean_dec(x_103);
x_118 = lean_ctor_get(x_104, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_104, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_120 = x_104;
} else {
 lean_dec_ref(x_104);
 x_120 = lean_box(0);
}
x_121 = l_Lake_OrdHashSet_appendArray___at_Lake_Module_recComputeTransImports___spec__1(x_4, x_118);
x_122 = l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2(x_121, x_28);
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_120;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_119);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_117);
x_11 = x_124;
x_12 = x_105;
goto block_26;
}
}
else
{
lean_object* x_125; uint8_t x_126; 
lean_dec(x_28);
lean_dec(x_4);
x_125 = lean_ctor_get(x_102, 1);
lean_inc(x_125);
lean_dec(x_102);
x_126 = !lean_is_exclusive(x_103);
if (x_126 == 0)
{
x_11 = x_103;
x_12 = x_125;
goto block_26;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_103, 0);
x_128 = lean_ctor_get(x_103, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_103);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_11 = x_129;
x_12 = x_125;
goto block_26;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_4);
lean_ctor_set(x_134, 1, x_7);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_9);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_10);
return x_136;
}
block_26:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
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
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_7 = x_16;
x_9 = x_14;
x_10 = x_12;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recComputePrecompileImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_2);
lean_inc(x_5);
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
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
x_22 = lean_array_get_size(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
lean_ctor_set(x_12, 0, x_25);
return x_10;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
lean_ctor_set(x_12, 0, x_27);
return x_10;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_12);
lean_free_object(x_11);
lean_free_object(x_10);
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_31 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(x_20, x_28, x_29, x_30, x_2, x_3, x_21, x_5, x_17, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_ctor_set(x_33, 0, x_40);
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_32, 0, x_44);
return x_31;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_48 = x_33;
} else {
 lean_dec_ref(x_33);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_31, 0, x_51);
return x_31;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_dec(x_31);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_54 = x_32;
} else {
 lean_dec_ref(x_32);
 x_54 = lean_box(0);
}
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
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_52);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_31, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
return x_31;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_32, 0);
x_66 = lean_ctor_get(x_32, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_32);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_31, 0, x_67);
return x_31;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_31, 1);
lean_inc(x_68);
lean_dec(x_31);
x_69 = lean_ctor_get(x_32, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_32, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_71 = x_32;
} else {
 lean_dec_ref(x_32);
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
x_74 = !lean_is_exclusive(x_31);
if (x_74 == 0)
{
return x_31;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_31, 0);
x_76 = lean_ctor_get(x_31, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_31);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_12, 0);
x_79 = lean_ctor_get(x_12, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_12);
x_80 = lean_array_get_size(x_78);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_nat_dec_lt(x_81, x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_83 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
lean_ctor_set(x_11, 0, x_84);
return x_10;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_80, x_80);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_86 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_11, 0, x_87);
return x_10;
}
else
{
size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_11);
lean_free_object(x_10);
x_88 = 0;
x_89 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_90 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_91 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(x_78, x_88, x_89, x_90, x_2, x_3, x_79, x_5, x_17, x_14);
lean_dec(x_78);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_97 = x_92;
} else {
 lean_dec_ref(x_92);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_100 = x_93;
} else {
 lean_dec_ref(x_93);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_97;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
if (lean_is_scalar(x_95)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_95;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_94);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_91, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_106 = x_91;
} else {
 lean_dec_ref(x_91);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_92, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_92, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_109 = x_92;
} else {
 lean_dec_ref(x_92);
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
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_91, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_91, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_114 = x_91;
} else {
 lean_dec_ref(x_91);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_116 = lean_ctor_get(x_11, 1);
lean_inc(x_116);
lean_dec(x_11);
x_117 = lean_ctor_get(x_12, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_12, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_119 = x_12;
} else {
 lean_dec_ref(x_12);
 x_119 = lean_box(0);
}
x_120 = lean_array_get_size(x_117);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_nat_dec_lt(x_121, x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_123 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_119;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_118);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_116);
lean_ctor_set(x_10, 0, x_125);
return x_10;
}
else
{
uint8_t x_126; 
x_126 = lean_nat_dec_le(x_120, x_120);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_127 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_119)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_119;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_118);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_116);
lean_ctor_set(x_10, 0, x_129);
return x_10;
}
else
{
size_t x_130; size_t x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_119);
lean_free_object(x_10);
x_130 = 0;
x_131 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_132 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_133 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(x_117, x_130, x_131, x_132, x_2, x_3, x_118, x_5, x_116, x_14);
lean_dec(x_117);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_139 = x_134;
} else {
 lean_dec_ref(x_134);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_142 = x_135;
} else {
 lean_dec_ref(x_135);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_141);
if (lean_is_scalar(x_139)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_139;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_138);
if (lean_is_scalar(x_137)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_137;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_136);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_147 = lean_ctor_get(x_133, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_148 = x_133;
} else {
 lean_dec_ref(x_133);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_134, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_134, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_151 = x_134;
} else {
 lean_dec_ref(x_134);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
if (lean_is_scalar(x_148)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_148;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_147);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_133, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_133, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_156 = x_133;
} else {
 lean_dec_ref(x_133);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_158 = lean_ctor_get(x_10, 1);
lean_inc(x_158);
lean_dec(x_10);
x_159 = lean_ctor_get(x_11, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_160 = x_11;
} else {
 lean_dec_ref(x_11);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_12, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_12, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_163 = x_12;
} else {
 lean_dec_ref(x_12);
 x_163 = lean_box(0);
}
x_164 = lean_array_get_size(x_161);
x_165 = lean_unsigned_to_nat(0u);
x_166 = lean_nat_dec_lt(x_165, x_164);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_167 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_163)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_163;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_162);
if (lean_is_scalar(x_160)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_160;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_159);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_158);
return x_170;
}
else
{
uint8_t x_171; 
x_171 = lean_nat_dec_le(x_164, x_164);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_172 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
if (lean_is_scalar(x_163)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_163;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_162);
if (lean_is_scalar(x_160)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_160;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_159);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_158);
return x_175;
}
else
{
size_t x_176; size_t x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_163);
lean_dec(x_160);
x_176 = 0;
x_177 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_178 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_179 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(x_161, x_176, x_177, x_178, x_2, x_3, x_162, x_5, x_159, x_158);
lean_dec(x_161);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_183 = x_179;
} else {
 lean_dec_ref(x_179);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_185 = x_180;
} else {
 lean_dec_ref(x_180);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_181, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_181, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_188 = x_181;
} else {
 lean_dec_ref(x_181);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
if (lean_is_scalar(x_185)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_185;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_184);
if (lean_is_scalar(x_183)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_183;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_182);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_193 = lean_ctor_get(x_179, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_194 = x_179;
} else {
 lean_dec_ref(x_179);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_180, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_180, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_197 = x_180;
} else {
 lean_dec_ref(x_180);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
if (lean_is_scalar(x_194)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_194;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_193);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_179, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_179, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_202 = x_179;
} else {
 lean_dec_ref(x_179);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_204 = !lean_is_exclusive(x_10);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_10, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_11);
if (x_206 == 0)
{
return x_10;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_11, 0);
x_208 = lean_ctor_get(x_11, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_11);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_10, 0, x_209);
return x_10;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_10, 1);
lean_inc(x_210);
lean_dec(x_10);
x_211 = lean_ctor_get(x_11, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_11, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_213 = x_11;
} else {
 lean_dec_ref(x_11);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_210);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_216 = !lean_is_exclusive(x_10);
if (x_216 == 0)
{
return x_10;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_10, 0);
x_218 = lean_ctor_get(x_10, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_10);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_6);
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
x_17 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__2;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_5);
x_19 = lean_apply_6(x_4, x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_6 = x_25;
x_8 = x_23;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_7);
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
return x_19;
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
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_39 = x_20;
} else {
 lean_dec_ref(x_20);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("olean", 5);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_6);
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
lean_inc(x_7);
lean_inc(x_5);
x_19 = lean_apply_6(x_4, x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_6 = x_25;
x_8 = x_23;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_7);
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
return x_19;
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
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_39 = x_20;
} else {
 lean_dec_ref(x_20);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
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
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_9 = l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8(x_4, x_8);
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lake_BuildTrace_mix(x_1, x_2);
x_14 = l_Lake_BuildTrace_mix(x_3, x_13);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_16, 8);
x_18 = lean_array_get_size(x_11);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
x_20 = l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(x_11, x_19, x_18);
x_21 = l_Array_append___rarg(x_5, x_20);
x_22 = lean_array_to_list(lean_box(0), x_21);
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_24 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_23, x_6, x_11);
x_25 = lean_array_get_size(x_7);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_26, x_6, x_7);
x_28 = l_Array_append___rarg(x_24, x_27);
lean_ctor_set(x_9, 1, x_28);
lean_ctor_set(x_9, 0, x_22);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_8, 2);
x_30 = lean_ctor_get(x_29, 1);
x_31 = lean_ctor_get(x_30, 8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lake_BuildTrace_mix(x_14, x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_unbox(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lake_Module_recBuildDeps___lambda__1___closed__3;
x_37 = l_Lake_BuildTrace_mix(x_12, x_36);
x_38 = l_Lake_BuildTrace_mix(x_14, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_9);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_12);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_9);
lean_ctor_set(x_40, 1, x_14);
return x_40;
}
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = l_Lake_Module_recBuildDeps___lambda__1___closed__3;
x_44 = l_Lake_BuildTrace_mix(x_12, x_43);
x_45 = l_Lake_BuildTrace_mix(x_14, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_9);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_12);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_9);
lean_ctor_set(x_47, 1, x_14);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = l_Lake_BuildTrace_mix(x_1, x_2);
x_51 = l_Lake_BuildTrace_mix(x_3, x_50);
x_52 = lean_ctor_get(x_4, 1);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_ctor_get(x_53, 8);
x_55 = lean_array_get_size(x_48);
x_56 = lean_unsigned_to_nat(0u);
lean_inc(x_55);
x_57 = l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(x_48, x_56, x_55);
x_58 = l_Array_append___rarg(x_5, x_57);
x_59 = lean_array_to_list(lean_box(0), x_58);
x_60 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_61 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_60, x_6, x_48);
x_62 = lean_array_get_size(x_7);
x_63 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_64 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__5(x_63, x_6, x_7);
x_65 = l_Array_append___rarg(x_61, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_65);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_8, 2);
x_68 = lean_ctor_get(x_67, 1);
x_69 = lean_ctor_get(x_68, 8);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Lake_BuildTrace_mix(x_51, x_49);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_unbox(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = l_Lake_Module_recBuildDeps___lambda__1___closed__3;
x_75 = l_Lake_BuildTrace_mix(x_49, x_74);
x_76 = l_Lake_BuildTrace_mix(x_51, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
lean_object* x_78; 
lean_dec(x_49);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_66);
lean_ctor_set(x_78, 1, x_51);
return x_78;
}
}
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_54, 0);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = l_Lake_Module_recBuildDeps___lambda__1___closed__3;
x_82 = l_Lake_BuildTrace_mix(x_49, x_81);
x_83 = l_Lake_BuildTrace_mix(x_51, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_66);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_49);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_66);
lean_ctor_set(x_85, 1, x_51);
return x_85;
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
x_5 = l_Array_append___rarg(x_1, x_4);
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
x_8 = l_Array_append___rarg(x_1, x_7);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_add(x_13, x_11);
lean_dec(x_11);
lean_dec(x_13);
x_15 = l_Array_append___rarg(x_1, x_12);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_add(x_18, x_16);
lean_dec(x_16);
lean_dec(x_18);
x_20 = l_Array_append___rarg(x_1, x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box_usize(x_5);
x_15 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__1___boxed), 9, 8);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_14);
lean_closure_set(x_15, 6, x_12);
lean_closure_set(x_15, 7, x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = lean_task_map(x_16, x_7, x_17, x_18);
x_20 = l_Array_isEmpty___rarg(x_11);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_21, 0, x_11);
x_22 = 1;
x_23 = lean_task_map(x_21, x_19, x_17, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_task_pure(x_8);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_task_pure(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box_usize(x_4);
x_14 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__3___boxed), 9, 7);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_13);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_6);
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = lean_io_bind_task(x_7, x_14, x_15, x_16, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Array_isEmpty___rarg(x_11);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_21, 0, x_11);
x_22 = 1;
x_23 = lean_task_map(x_21, x_19, x_15, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_dec(x_11);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = l_Array_isEmpty___rarg(x_11);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_27, 0, x_11);
x_28 = 1;
x_29 = lean_task_map(x_27, x_24, x_15, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_11);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_task_pure(x_8);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_9);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_8, 0);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_task_pure(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_9);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box_usize(x_3);
x_14 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__4___boxed), 9, 7);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_6);
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = lean_io_bind_task(x_7, x_14, x_15, x_16, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Array_isEmpty___rarg(x_11);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_21, 0, x_11);
x_22 = 1;
x_23 = lean_task_map(x_21, x_19, x_15, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_dec(x_11);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = l_Array_isEmpty___rarg(x_11);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_27, 0, x_11);
x_28 = 1;
x_29 = lean_task_map(x_27, x_24, x_15, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_11);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_task_pure(x_8);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_9);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_8, 0);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_task_pure(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_9);
return x_43;
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildDeps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("extraDep", 8);
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
static lean_object* _init_l_Lake_Module_recBuildDeps___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__3;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lake_Module_recBuildDeps___closed__2;
lean_inc(x_17);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_3);
x_20 = lean_apply_6(x_2, x_19, x_3, x_16, x_5, x_14, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
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
x_27 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_3);
x_29 = lean_apply_6(x_2, x_28, x_3, x_26, x_5, x_24, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_array_get_size(x_34);
x_37 = lean_usize_of_nat(x_36);
x_38 = 0;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_34);
x_39 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(x_37, x_38, x_34, x_2, x_3, x_35, x_5, x_33, x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_lt(x_46, x_36);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_36);
lean_dec(x_34);
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
x_49 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
lean_inc(x_48);
x_50 = l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8(x_49, x_48);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_52 = l_Lake_recBuildExternDynlibs(x_51, x_2, x_3, x_45, x_5, x_43, x_42);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_array_get_size(x_15);
x_62 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_63 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(x_62, x_38, x_15, x_2, x_3, x_58, x_5, x_57, x_56);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_64, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_65);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; uint8_t x_85; 
x_70 = lean_ctor_get(x_65, 0);
x_71 = l_Lake_BuildJob_mixArray___rarg(x_70, x_66);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lake_BuildJob_collectArray___rarg(x_59, x_73);
lean_dec(x_59);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lake_BuildJob_collectArray___rarg(x_44, x_76);
lean_dec(x_44);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lake_Module_recBuildDeps___boxed__const__1;
x_81 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 9, 7);
lean_closure_set(x_81, 0, x_17);
lean_closure_set(x_81, 1, x_60);
lean_closure_set(x_81, 2, x_80);
lean_closure_set(x_81, 3, x_48);
lean_closure_set(x_81, 4, x_75);
lean_closure_set(x_81, 5, x_78);
lean_closure_set(x_81, 6, x_72);
x_82 = l_Task_Priority_default;
x_83 = 0;
x_84 = lean_io_bind_task(x_25, x_81, x_82, x_83, x_79);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_ctor_set(x_65, 0, x_86);
lean_ctor_set(x_84, 0, x_64);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_84);
lean_ctor_set(x_65, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_64);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_90 = lean_ctor_get(x_65, 0);
x_91 = lean_ctor_get(x_65, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_65);
x_92 = l_Lake_BuildJob_mixArray___rarg(x_90, x_66);
lean_dec(x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lake_BuildJob_collectArray___rarg(x_59, x_94);
lean_dec(x_59);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lake_BuildJob_collectArray___rarg(x_44, x_97);
lean_dec(x_44);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lake_Module_recBuildDeps___boxed__const__1;
x_102 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 9, 7);
lean_closure_set(x_102, 0, x_17);
lean_closure_set(x_102, 1, x_60);
lean_closure_set(x_102, 2, x_101);
lean_closure_set(x_102, 3, x_48);
lean_closure_set(x_102, 4, x_96);
lean_closure_set(x_102, 5, x_99);
lean_closure_set(x_102, 6, x_93);
x_103 = l_Task_Priority_default;
x_104 = 0;
x_105 = lean_io_bind_task(x_25, x_102, x_103, x_104, x_100);
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
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_91);
lean_ctor_set(x_64, 0, x_109);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_64);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_111 = lean_ctor_get(x_64, 1);
lean_inc(x_111);
lean_dec(x_64);
x_112 = lean_ctor_get(x_65, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_65, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_114 = x_65;
} else {
 lean_dec_ref(x_65);
 x_114 = lean_box(0);
}
x_115 = l_Lake_BuildJob_mixArray___rarg(x_112, x_66);
lean_dec(x_112);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lake_BuildJob_collectArray___rarg(x_59, x_117);
lean_dec(x_59);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_Lake_BuildJob_collectArray___rarg(x_44, x_120);
lean_dec(x_44);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lake_Module_recBuildDeps___boxed__const__1;
x_125 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 9, 7);
lean_closure_set(x_125, 0, x_17);
lean_closure_set(x_125, 1, x_60);
lean_closure_set(x_125, 2, x_124);
lean_closure_set(x_125, 3, x_48);
lean_closure_set(x_125, 4, x_119);
lean_closure_set(x_125, 5, x_122);
lean_closure_set(x_125, 6, x_116);
x_126 = l_Task_Priority_default;
x_127 = 0;
x_128 = lean_io_bind_task(x_25, x_125, x_126, x_127, x_123);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
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
if (lean_is_scalar(x_114)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_114;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_113);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_111);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_130);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
x_135 = !lean_is_exclusive(x_63);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_63, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_64);
if (x_137 == 0)
{
return x_63;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_64, 0);
x_139 = lean_ctor_get(x_64, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_64);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_63, 0, x_140);
return x_63;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_63, 1);
lean_inc(x_141);
lean_dec(x_63);
x_142 = lean_ctor_get(x_64, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_64, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_144 = x_64;
} else {
 lean_dec_ref(x_64);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_141);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
x_147 = !lean_is_exclusive(x_63);
if (x_147 == 0)
{
return x_63;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_63, 0);
x_149 = lean_ctor_get(x_63, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_63);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_151 = !lean_is_exclusive(x_52);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_52, 0);
lean_dec(x_152);
x_153 = !lean_is_exclusive(x_53);
if (x_153 == 0)
{
return x_52;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_53, 0);
x_155 = lean_ctor_get(x_53, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_53);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set(x_52, 0, x_156);
return x_52;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_52, 1);
lean_inc(x_157);
lean_dec(x_52);
x_158 = lean_ctor_get(x_53, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_53, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_160 = x_53;
} else {
 lean_dec_ref(x_53);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_157);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_163 = !lean_is_exclusive(x_52);
if (x_163 == 0)
{
return x_52;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_52, 0);
x_165 = lean_ctor_get(x_52, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_52);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; uint8_t x_168; 
x_167 = lean_ctor_get(x_17, 0);
lean_inc(x_167);
x_168 = lean_nat_dec_le(x_36, x_36);
lean_dec(x_36);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_34);
x_169 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
lean_inc(x_167);
x_170 = l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8(x_169, x_167);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_172 = l_Lake_recBuildExternDynlibs(x_171, x_2, x_3, x_45, x_5, x_43, x_42);
lean_dec(x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; size_t x_182; lean_object* x_183; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
lean_dec(x_172);
x_177 = lean_ctor_get(x_173, 1);
lean_inc(x_177);
lean_dec(x_173);
x_178 = lean_ctor_get(x_174, 1);
lean_inc(x_178);
lean_dec(x_174);
x_179 = lean_ctor_get(x_175, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
lean_dec(x_175);
x_181 = lean_array_get_size(x_15);
x_182 = lean_usize_of_nat(x_181);
lean_dec(x_181);
x_183 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(x_182, x_38, x_15, x_2, x_3, x_178, x_5, x_177, x_176);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_187 = !lean_is_exclusive(x_184);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_184, 0);
lean_dec(x_188);
x_189 = !lean_is_exclusive(x_185);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; uint8_t x_205; 
x_190 = lean_ctor_get(x_185, 0);
x_191 = l_Lake_BuildJob_mixArray___rarg(x_190, x_186);
lean_dec(x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lake_BuildJob_collectArray___rarg(x_179, x_193);
lean_dec(x_179);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = l_Lake_BuildJob_collectArray___rarg(x_44, x_196);
lean_dec(x_44);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = l_Lake_Module_recBuildDeps___boxed__const__1;
x_201 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 9, 7);
lean_closure_set(x_201, 0, x_17);
lean_closure_set(x_201, 1, x_180);
lean_closure_set(x_201, 2, x_200);
lean_closure_set(x_201, 3, x_167);
lean_closure_set(x_201, 4, x_195);
lean_closure_set(x_201, 5, x_198);
lean_closure_set(x_201, 6, x_192);
x_202 = l_Task_Priority_default;
x_203 = 0;
x_204 = lean_io_bind_task(x_25, x_201, x_202, x_203, x_199);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 0);
lean_ctor_set(x_185, 0, x_206);
lean_ctor_set(x_204, 0, x_184);
return x_204;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_204, 0);
x_208 = lean_ctor_get(x_204, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_204);
lean_ctor_set(x_185, 0, x_207);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_184);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_210 = lean_ctor_get(x_185, 0);
x_211 = lean_ctor_get(x_185, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_185);
x_212 = l_Lake_BuildJob_mixArray___rarg(x_210, x_186);
lean_dec(x_210);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = l_Lake_BuildJob_collectArray___rarg(x_179, x_214);
lean_dec(x_179);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l_Lake_BuildJob_collectArray___rarg(x_44, x_217);
lean_dec(x_44);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = l_Lake_Module_recBuildDeps___boxed__const__1;
x_222 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 9, 7);
lean_closure_set(x_222, 0, x_17);
lean_closure_set(x_222, 1, x_180);
lean_closure_set(x_222, 2, x_221);
lean_closure_set(x_222, 3, x_167);
lean_closure_set(x_222, 4, x_216);
lean_closure_set(x_222, 5, x_219);
lean_closure_set(x_222, 6, x_213);
x_223 = l_Task_Priority_default;
x_224 = 0;
x_225 = lean_io_bind_task(x_25, x_222, x_223, x_224, x_220);
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
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_211);
lean_ctor_set(x_184, 0, x_229);
if (lean_is_scalar(x_228)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_228;
}
lean_ctor_set(x_230, 0, x_184);
lean_ctor_set(x_230, 1, x_227);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_231 = lean_ctor_get(x_184, 1);
lean_inc(x_231);
lean_dec(x_184);
x_232 = lean_ctor_get(x_185, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_185, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_234 = x_185;
} else {
 lean_dec_ref(x_185);
 x_234 = lean_box(0);
}
x_235 = l_Lake_BuildJob_mixArray___rarg(x_232, x_186);
lean_dec(x_232);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = l_Lake_BuildJob_collectArray___rarg(x_179, x_237);
lean_dec(x_179);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = l_Lake_BuildJob_collectArray___rarg(x_44, x_240);
lean_dec(x_44);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lake_Module_recBuildDeps___boxed__const__1;
x_245 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 9, 7);
lean_closure_set(x_245, 0, x_17);
lean_closure_set(x_245, 1, x_180);
lean_closure_set(x_245, 2, x_244);
lean_closure_set(x_245, 3, x_167);
lean_closure_set(x_245, 4, x_239);
lean_closure_set(x_245, 5, x_242);
lean_closure_set(x_245, 6, x_236);
x_246 = l_Task_Priority_default;
x_247 = 0;
x_248 = lean_io_bind_task(x_25, x_245, x_246, x_247, x_243);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_251 = x_248;
} else {
 lean_dec_ref(x_248);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_234;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_233);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_231);
if (lean_is_scalar(x_251)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_251;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_250);
return x_254;
}
}
else
{
uint8_t x_255; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_167);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
x_255 = !lean_is_exclusive(x_183);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_183, 0);
lean_dec(x_256);
x_257 = !lean_is_exclusive(x_184);
if (x_257 == 0)
{
return x_183;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_184, 0);
x_259 = lean_ctor_get(x_184, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_184);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
lean_ctor_set(x_183, 0, x_260);
return x_183;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_261 = lean_ctor_get(x_183, 1);
lean_inc(x_261);
lean_dec(x_183);
x_262 = lean_ctor_get(x_184, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_184, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_264 = x_184;
} else {
 lean_dec_ref(x_184);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_261);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_167);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
x_267 = !lean_is_exclusive(x_183);
if (x_267 == 0)
{
return x_183;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_183, 0);
x_269 = lean_ctor_get(x_183, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_183);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_167);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_271 = !lean_is_exclusive(x_172);
if (x_271 == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_172, 0);
lean_dec(x_272);
x_273 = !lean_is_exclusive(x_173);
if (x_273 == 0)
{
return x_172;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_173, 0);
x_275 = lean_ctor_get(x_173, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_173);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
lean_ctor_set(x_172, 0, x_276);
return x_172;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_277 = lean_ctor_get(x_172, 1);
lean_inc(x_277);
lean_dec(x_172);
x_278 = lean_ctor_get(x_173, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_173, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_280 = x_173;
} else {
 lean_dec_ref(x_173);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_277);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_167);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_283 = !lean_is_exclusive(x_172);
if (x_283 == 0)
{
return x_172;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_172, 0);
x_285 = lean_ctor_get(x_172, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_172);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_287 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_288 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__6(x_34, x_38, x_37, x_287);
lean_dec(x_34);
lean_inc(x_167);
x_289 = l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8(x_288, x_167);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_291 = l_Lake_recBuildExternDynlibs(x_290, x_2, x_3, x_45, x_5, x_43, x_42);
lean_dec(x_290);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; size_t x_301; lean_object* x_302; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_291, 1);
lean_inc(x_295);
lean_dec(x_291);
x_296 = lean_ctor_get(x_292, 1);
lean_inc(x_296);
lean_dec(x_292);
x_297 = lean_ctor_get(x_293, 1);
lean_inc(x_297);
lean_dec(x_293);
x_298 = lean_ctor_get(x_294, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_294, 1);
lean_inc(x_299);
lean_dec(x_294);
x_300 = lean_array_get_size(x_15);
x_301 = lean_usize_of_nat(x_300);
lean_dec(x_300);
x_302 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2(x_301, x_38, x_15, x_2, x_3, x_297, x_5, x_296, x_295);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_302, 1);
lean_inc(x_305);
lean_dec(x_302);
x_306 = !lean_is_exclusive(x_303);
if (x_306 == 0)
{
lean_object* x_307; uint8_t x_308; 
x_307 = lean_ctor_get(x_303, 0);
lean_dec(x_307);
x_308 = !lean_is_exclusive(x_304);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; uint8_t x_324; 
x_309 = lean_ctor_get(x_304, 0);
x_310 = l_Lake_BuildJob_mixArray___rarg(x_309, x_305);
lean_dec(x_309);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = l_Lake_BuildJob_collectArray___rarg(x_298, x_312);
lean_dec(x_298);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = l_Lake_BuildJob_collectArray___rarg(x_44, x_315);
lean_dec(x_44);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = l_Lake_Module_recBuildDeps___boxed__const__1;
x_320 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 9, 7);
lean_closure_set(x_320, 0, x_17);
lean_closure_set(x_320, 1, x_299);
lean_closure_set(x_320, 2, x_319);
lean_closure_set(x_320, 3, x_167);
lean_closure_set(x_320, 4, x_314);
lean_closure_set(x_320, 5, x_317);
lean_closure_set(x_320, 6, x_311);
x_321 = l_Task_Priority_default;
x_322 = 0;
x_323 = lean_io_bind_task(x_25, x_320, x_321, x_322, x_318);
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_323, 0);
lean_ctor_set(x_304, 0, x_325);
lean_ctor_set(x_323, 0, x_303);
return x_323;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_323, 0);
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_323);
lean_ctor_set(x_304, 0, x_326);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_303);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_329 = lean_ctor_get(x_304, 0);
x_330 = lean_ctor_get(x_304, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_304);
x_331 = l_Lake_BuildJob_mixArray___rarg(x_329, x_305);
lean_dec(x_329);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = l_Lake_BuildJob_collectArray___rarg(x_298, x_333);
lean_dec(x_298);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = l_Lake_BuildJob_collectArray___rarg(x_44, x_336);
lean_dec(x_44);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = l_Lake_Module_recBuildDeps___boxed__const__1;
x_341 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 9, 7);
lean_closure_set(x_341, 0, x_17);
lean_closure_set(x_341, 1, x_299);
lean_closure_set(x_341, 2, x_340);
lean_closure_set(x_341, 3, x_167);
lean_closure_set(x_341, 4, x_335);
lean_closure_set(x_341, 5, x_338);
lean_closure_set(x_341, 6, x_332);
x_342 = l_Task_Priority_default;
x_343 = 0;
x_344 = lean_io_bind_task(x_25, x_341, x_342, x_343, x_339);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_347 = x_344;
} else {
 lean_dec_ref(x_344);
 x_347 = lean_box(0);
}
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_330);
lean_ctor_set(x_303, 0, x_348);
if (lean_is_scalar(x_347)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_347;
}
lean_ctor_set(x_349, 0, x_303);
lean_ctor_set(x_349, 1, x_346);
return x_349;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_350 = lean_ctor_get(x_303, 1);
lean_inc(x_350);
lean_dec(x_303);
x_351 = lean_ctor_get(x_304, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_304, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_353 = x_304;
} else {
 lean_dec_ref(x_304);
 x_353 = lean_box(0);
}
x_354 = l_Lake_BuildJob_mixArray___rarg(x_351, x_305);
lean_dec(x_351);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
x_357 = l_Lake_BuildJob_collectArray___rarg(x_298, x_356);
lean_dec(x_298);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = l_Lake_BuildJob_collectArray___rarg(x_44, x_359);
lean_dec(x_44);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = l_Lake_Module_recBuildDeps___boxed__const__1;
x_364 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__5___boxed), 9, 7);
lean_closure_set(x_364, 0, x_17);
lean_closure_set(x_364, 1, x_299);
lean_closure_set(x_364, 2, x_363);
lean_closure_set(x_364, 3, x_167);
lean_closure_set(x_364, 4, x_358);
lean_closure_set(x_364, 5, x_361);
lean_closure_set(x_364, 6, x_355);
x_365 = l_Task_Priority_default;
x_366 = 0;
x_367 = lean_io_bind_task(x_25, x_364, x_365, x_366, x_362);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_370 = x_367;
} else {
 lean_dec_ref(x_367);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_353;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_352);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_350);
if (lean_is_scalar(x_370)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_370;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_369);
return x_373;
}
}
else
{
uint8_t x_374; 
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_167);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
x_374 = !lean_is_exclusive(x_302);
if (x_374 == 0)
{
lean_object* x_375; uint8_t x_376; 
x_375 = lean_ctor_get(x_302, 0);
lean_dec(x_375);
x_376 = !lean_is_exclusive(x_303);
if (x_376 == 0)
{
return x_302;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_303, 0);
x_378 = lean_ctor_get(x_303, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_303);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
lean_ctor_set(x_302, 0, x_379);
return x_302;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_380 = lean_ctor_get(x_302, 1);
lean_inc(x_380);
lean_dec(x_302);
x_381 = lean_ctor_get(x_303, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_303, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_383 = x_303;
} else {
 lean_dec_ref(x_303);
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
return x_385;
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_167);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
x_386 = !lean_is_exclusive(x_302);
if (x_386 == 0)
{
return x_302;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_302, 0);
x_388 = lean_ctor_get(x_302, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_302);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
else
{
uint8_t x_390; 
lean_dec(x_167);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_390 = !lean_is_exclusive(x_291);
if (x_390 == 0)
{
lean_object* x_391; uint8_t x_392; 
x_391 = lean_ctor_get(x_291, 0);
lean_dec(x_391);
x_392 = !lean_is_exclusive(x_292);
if (x_392 == 0)
{
return x_291;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_292, 0);
x_394 = lean_ctor_get(x_292, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_292);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
lean_ctor_set(x_291, 0, x_395);
return x_291;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_396 = lean_ctor_get(x_291, 1);
lean_inc(x_396);
lean_dec(x_291);
x_397 = lean_ctor_get(x_292, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_292, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_399 = x_292;
} else {
 lean_dec_ref(x_292);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_398);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_396);
return x_401;
}
}
}
else
{
uint8_t x_402; 
lean_dec(x_167);
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_402 = !lean_is_exclusive(x_291);
if (x_402 == 0)
{
return x_291;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_291, 0);
x_404 = lean_ctor_get(x_291, 1);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_291);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
}
}
}
else
{
uint8_t x_406; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_406 = !lean_is_exclusive(x_39);
if (x_406 == 0)
{
lean_object* x_407; uint8_t x_408; 
x_407 = lean_ctor_get(x_39, 0);
lean_dec(x_407);
x_408 = !lean_is_exclusive(x_40);
if (x_408 == 0)
{
return x_39;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_40, 0);
x_410 = lean_ctor_get(x_40, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_40);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
lean_ctor_set(x_39, 0, x_411);
return x_39;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_412 = lean_ctor_get(x_39, 1);
lean_inc(x_412);
lean_dec(x_39);
x_413 = lean_ctor_get(x_40, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_40, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_415 = x_40;
} else {
 lean_dec_ref(x_40);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_414);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_412);
return x_417;
}
}
}
else
{
uint8_t x_418; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_418 = !lean_is_exclusive(x_39);
if (x_418 == 0)
{
return x_39;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_39, 0);
x_420 = lean_ctor_get(x_39, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_39);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
else
{
uint8_t x_422; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_422 = !lean_is_exclusive(x_29);
if (x_422 == 0)
{
lean_object* x_423; uint8_t x_424; 
x_423 = lean_ctor_get(x_29, 0);
lean_dec(x_423);
x_424 = !lean_is_exclusive(x_30);
if (x_424 == 0)
{
return x_29;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_30, 0);
x_426 = lean_ctor_get(x_30, 1);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_30);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
lean_ctor_set(x_29, 0, x_427);
return x_29;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_29, 1);
lean_inc(x_428);
lean_dec(x_29);
x_429 = lean_ctor_get(x_30, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_30, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_431 = x_30;
} else {
 lean_dec_ref(x_30);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_430);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_428);
return x_433;
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_434 = !lean_is_exclusive(x_29);
if (x_434 == 0)
{
return x_29;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_29, 0);
x_436 = lean_ctor_get(x_29, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_29);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
else
{
uint8_t x_438; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_438 = !lean_is_exclusive(x_20);
if (x_438 == 0)
{
lean_object* x_439; uint8_t x_440; 
x_439 = lean_ctor_get(x_20, 0);
lean_dec(x_439);
x_440 = !lean_is_exclusive(x_21);
if (x_440 == 0)
{
return x_20;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_21, 0);
x_442 = lean_ctor_get(x_21, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_21);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
lean_ctor_set(x_20, 0, x_443);
return x_20;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_444 = lean_ctor_get(x_20, 1);
lean_inc(x_444);
lean_dec(x_20);
x_445 = lean_ctor_get(x_21, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_21, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_447 = x_21;
} else {
 lean_dec_ref(x_21);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_444);
return x_449;
}
}
}
else
{
uint8_t x_450; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_450 = !lean_is_exclusive(x_20);
if (x_450 == 0)
{
return x_20;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_20, 0);
x_452 = lean_ctor_get(x_20, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_20);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
else
{
uint8_t x_454; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_454 = !lean_is_exclusive(x_10);
if (x_454 == 0)
{
lean_object* x_455; uint8_t x_456; 
x_455 = lean_ctor_get(x_10, 0);
lean_dec(x_455);
x_456 = !lean_is_exclusive(x_11);
if (x_456 == 0)
{
return x_10;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_11, 0);
x_458 = lean_ctor_get(x_11, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_11);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
lean_ctor_set(x_10, 0, x_459);
return x_10;
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_460 = lean_ctor_get(x_10, 1);
lean_inc(x_460);
lean_dec(x_10);
x_461 = lean_ctor_get(x_11, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_11, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_463 = x_11;
} else {
 lean_dec_ref(x_11);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 2, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_461);
lean_ctor_set(x_464, 1, x_462);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_460);
return x_465;
}
}
}
else
{
uint8_t x_466; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_466 = !lean_is_exclusive(x_10);
if (x_466 == 0)
{
return x_10;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_10, 0);
x_468 = lean_ctor_get(x_10, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_10);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; 
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Lake_Module_recBuildDeps___lambda__1(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Lake_Module_recBuildDeps___lambda__3(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Lake_Module_recBuildDeps___lambda__4(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDeps___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Lake_Module_recBuildDeps___lambda__5(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_3 = l_Task_Priority_default;
x_4 = 0;
x_5 = lean_task_map(x_2, x_1, x_3, x_4);
return x_5;
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
x_1 = lean_mk_string_from_bytes("deps", 4);
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
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___at_Lake_Module_recBuildLean___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get_uint8(x_7, 0);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lake_Hash_load_x3f(x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lake_Module_getMTime(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lake_MTime_instOrd;
x_17 = l_instDecidableRelLt___rarg(x_16, x_15, x_14);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lake_MTime_instOrd;
x_24 = l_instDecidableRelLt___rarg(x_23, x_22, x_20);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_12, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_32);
return x_12;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_9, 1);
x_40 = lean_ctor_get(x_9, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_10, 0);
lean_inc(x_41);
lean_dec(x_10);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_unbox_uint64(x_41);
lean_dec(x_41);
x_44 = lean_unbox_uint64(x_42);
lean_dec(x_42);
x_45 = lean_uint64_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_5);
lean_ctor_set(x_9, 0, x_47);
return x_9;
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_free_object(x_9);
x_48 = l_Lake_Module_checkExists(x_1, x_39);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_5);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; uint64_t x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_9, 1);
lean_inc(x_56);
lean_dec(x_9);
x_57 = lean_ctor_get(x_10, 0);
lean_inc(x_57);
lean_dec(x_10);
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
lean_dec(x_2);
x_59 = lean_unbox_uint64(x_57);
lean_dec(x_57);
x_60 = lean_unbox_uint64(x_58);
lean_dec(x_58);
x_61 = lean_uint64_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_5);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_56);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = l_Lake_Module_checkExists(x_1, x_56);
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
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_5);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
}
}
else
{
lean_object* x_71; 
x_71 = l_Lake_Module_getMTime(x_1, x_6);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
lean_dec(x_2);
x_75 = l_Lake_MTime_instOrd;
x_76 = l_instDecidableRelLt___rarg(x_75, x_74, x_73);
x_77 = lean_box(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_5);
lean_ctor_set(x_71, 0, x_78);
return x_71;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_71, 0);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_71);
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
lean_dec(x_2);
x_82 = l_Lake_MTime_instOrd;
x_83 = l_instDecidableRelLt___rarg(x_82, x_81, x_79);
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_5);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_71);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_71, 0);
lean_dec(x_88);
x_89 = 0;
x_90 = lean_box(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_5);
lean_ctor_set_tag(x_71, 0);
lean_ctor_set(x_71, 0, x_91);
return x_71;
}
else
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_71, 1);
lean_inc(x_92);
lean_dec(x_71);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_Module_recBuildLean___spec__2(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lake_Module_recBuildLean___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Array_forInUnsafe_loop___at_Lake_recBuildExternDynlibs___spec__3___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lake_Module_recBuildLean___lambda__1___closed__1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Lake_Module_recBuildLean___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ilean", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("c", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 7);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_modToFilePath(x_1, x_2, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lake_Module_recBuildLean___lambda__4___closed__1;
lean_inc(x_2);
x_25 = l_Lean_modToFilePath(x_1, x_2, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_ctor_get(x_3, 12);
lean_inc(x_27);
lean_dec(x_3);
x_28 = l_System_FilePath_join(x_4, x_27);
x_29 = l_Lake_Module_recBuildLean___lambda__4___closed__2;
x_30 = l_Lean_modToFilePath(x_28, x_2, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_ctor_get(x_5, 2);
lean_inc(x_32);
lean_dec(x_5);
x_33 = lean_ctor_get(x_6, 2);
lean_inc(x_33);
lean_dec(x_6);
x_34 = l_Array_append___rarg(x_32, x_33);
x_35 = l_Array_append___rarg(x_34, x_7);
x_36 = l_Lake_compileLeanModule(x_8, x_23, x_26, x_31, x_9, x_13, x_10, x_11, x_12, x_35, x_20, x_14, x_15, x_16);
return x_36;
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trace", 5);
return x_1;
}
}
static uint8_t _init_l_Lake_Module_recBuildLean___lambda__5___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_has_llvm_backend(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("log.json", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___lambda__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("bc", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__2), 3, 0);
return x_1;
}
}
static uint8_t _init_l_Lake_Module_recBuildLean___lambda__5___closed__6() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = l_Lake_noBuildCode;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_369; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_20, x_21, x_18);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
x_24 = l_Array_append___rarg(x_22, x_23);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_array_get_size(x_27);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_29, x_21, x_27);
x_31 = l_Array_append___rarg(x_24, x_30);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
x_33 = l_Array_append___rarg(x_31, x_32);
x_34 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_33);
x_35 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
x_36 = lean_box_uint64(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
lean_dec(x_15);
x_39 = lean_ctor_get(x_16, 7);
lean_inc(x_39);
lean_inc(x_38);
x_40 = l_System_FilePath_join(x_38, x_39);
x_41 = lean_ctor_get(x_25, 2);
lean_inc(x_41);
lean_dec(x_25);
x_42 = l_System_FilePath_join(x_40, x_41);
x_43 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1;
lean_inc(x_2);
lean_inc(x_42);
x_44 = l_Lean_modToFilePath(x_42, x_2, x_43);
x_369 = l_Lake_BuildTrace_compute___at_Lake_Module_recBuildLean___spec__2(x_44, x_5);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
lean_ctor_set(x_4, 0, x_370);
x_45 = x_4;
x_46 = x_371;
goto block_368;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_372 = lean_ctor_get(x_369, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_369, 1);
lean_inc(x_373);
lean_dec(x_369);
x_374 = lean_io_error_to_string(x_372);
x_375 = 3;
x_376 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*1, x_375);
x_377 = lean_array_get_size(x_9);
x_378 = lean_array_push(x_9, x_376);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_378);
lean_ctor_set(x_4, 0, x_377);
x_45 = x_4;
x_46 = x_373;
goto block_368;
}
block_368:
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_82; lean_object* x_83; lean_object* x_133; uint8_t x_134; uint8_t x_359; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_ctor_get(x_3, 2);
lean_inc(x_49);
lean_inc(x_11);
x_50 = l_Lake_BuildTrace_mix(x_47, x_11);
x_51 = l_Lake_BuildTrace_mix(x_37, x_50);
x_52 = l_Lake_BuildTrace_mix(x_49, x_51);
x_53 = lean_ctor_get(x_16, 8);
lean_inc(x_53);
x_54 = l_System_FilePath_join(x_38, x_53);
x_55 = lean_ctor_get(x_16, 9);
lean_inc(x_55);
lean_inc(x_54);
x_56 = l_System_FilePath_join(x_54, x_55);
x_57 = l_Lake_Module_recBuildLean___lambda__5___closed__1;
lean_inc(x_2);
lean_inc(x_56);
x_58 = l_Lean_modToFilePath(x_56, x_2, x_57);
x_59 = l_Lake_Module_recBuildLean___lambda__5___closed__3;
lean_inc(x_2);
lean_inc(x_56);
x_60 = l_Lean_modToFilePath(x_56, x_2, x_59);
lean_inc(x_52);
x_133 = l_Lake_BuildTrace_checkUpToDate___at_Lake_Module_recBuildLean___spec__1(x_1, x_52, x_58, x_3, x_48, x_46);
x_359 = l_Lake_Module_recBuildLean___lambda__5___closed__2;
if (x_359 == 0)
{
uint8_t x_360; 
x_360 = 0;
x_134 = x_360;
goto block_358;
}
else
{
uint8_t x_361; 
x_361 = 1;
x_134 = x_361;
goto block_358;
}
block_81:
{
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_box(0);
x_67 = l_Lake_Module_recBuildLean___lambda__3(x_11, x_66, x_3, x_65, x_62);
lean_dec(x_3);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_dec(x_61);
x_69 = l_Lake_replayBuildLog(x_60, x_68, x_62);
lean_dec(x_60);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l_Lake_Module_recBuildLean___lambda__3(x_11, x_72, x_3, x_73, x_71);
lean_dec(x_3);
lean_dec(x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_60);
lean_dec(x_11);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_61);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_61);
lean_ctor_set(x_76, 1, x_62);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_61, 0);
x_78 = lean_ctor_get(x_61, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_61);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_62);
return x_80;
}
}
}
block_132:
{
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_99; 
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
lean_inc(x_58);
x_99 = l_System_FilePath_parent(x_58);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; uint64_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_52, 0);
lean_inc(x_100);
lean_dec(x_52);
x_101 = lean_unbox_uint64(x_100);
lean_dec(x_100);
x_102 = lean_uint64_to_nat(x_101);
x_103 = l___private_Init_Data_Repr_0__Nat_reprFast(x_102);
x_104 = l_IO_FS_writeFile(x_58, x_103, x_83);
lean_dec(x_103);
lean_dec(x_58);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_105);
x_86 = x_107;
x_87 = x_106;
goto block_98;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
lean_dec(x_104);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_108);
x_86 = x_110;
x_87 = x_109;
goto block_98;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
lean_dec(x_99);
x_112 = l_IO_FS_createDirAll(x_111, x_83);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_ctor_get(x_52, 0);
lean_inc(x_114);
lean_dec(x_52);
x_115 = lean_unbox_uint64(x_114);
lean_dec(x_114);
x_116 = lean_uint64_to_nat(x_115);
x_117 = l___private_Init_Data_Repr_0__Nat_reprFast(x_116);
x_118 = l_IO_FS_writeFile(x_58, x_117, x_113);
lean_dec(x_117);
lean_dec(x_58);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_119);
x_86 = x_121;
x_87 = x_120;
goto block_98;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_dec(x_118);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_122);
x_86 = x_124;
x_87 = x_123;
goto block_98;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_58);
lean_dec(x_52);
x_125 = lean_ctor_get(x_112, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_112, 1);
lean_inc(x_126);
lean_dec(x_112);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_125);
x_86 = x_127;
x_87 = x_126;
goto block_98;
}
}
block_98:
{
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_io_error_to_string(x_88);
x_90 = 3;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_get_size(x_84);
x_93 = lean_array_push(x_84, x_91);
if (lean_is_scalar(x_85)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_85;
 lean_ctor_set_tag(x_94, 1);
}
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_61 = x_94;
x_62 = x_87;
goto block_81;
}
else
{
uint8_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_86);
x_95 = 0;
x_96 = lean_box(x_95);
if (lean_is_scalar(x_85)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_85;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_84);
x_61 = x_97;
x_62 = x_87;
goto block_81;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_58);
lean_dec(x_52);
x_128 = !lean_is_exclusive(x_82);
if (x_128 == 0)
{
x_61 = x_82;
x_62 = x_83;
goto block_81;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_82, 0);
x_130 = lean_ctor_get(x_82, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_82);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_61 = x_131;
x_62 = x_83;
goto block_81;
}
}
}
block_358:
{
lean_object* x_135; lean_object* x_136; lean_object* x_182; lean_object* x_183; lean_object* x_223; lean_object* x_224; lean_object* x_260; 
if (x_134 == 0)
{
lean_object* x_352; 
x_352 = lean_box(0);
x_260 = x_352;
goto block_351;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_16, 12);
lean_inc(x_353);
lean_inc(x_54);
x_354 = l_System_FilePath_join(x_54, x_353);
x_355 = l_Lake_Module_recBuildLean___lambda__5___closed__4;
lean_inc(x_2);
x_356 = l_Lean_modToFilePath(x_354, x_2, x_355);
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_356);
x_260 = x_357;
goto block_351;
}
block_181:
{
if (lean_obj_tag(x_135) == 0)
{
if (x_134 == 0)
{
uint8_t x_137; 
lean_dec(x_54);
lean_dec(x_16);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 0);
lean_dec(x_138);
x_139 = lean_box(0);
lean_ctor_set(x_135, 0, x_139);
x_82 = x_135;
x_83 = x_136;
goto block_132;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
lean_dec(x_135);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_82 = x_142;
x_83 = x_136;
goto block_132;
}
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_135);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_144 = lean_ctor_get(x_135, 1);
x_145 = lean_ctor_get(x_135, 0);
lean_dec(x_145);
x_146 = lean_ctor_get(x_16, 12);
lean_inc(x_146);
lean_dec(x_16);
x_147 = l_System_FilePath_join(x_54, x_146);
x_148 = l_Lake_Module_recBuildLean___lambda__5___closed__4;
x_149 = l_Lean_modToFilePath(x_147, x_2, x_148);
x_150 = l_Lake_cacheFileHash(x_149, x_136);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_box(0);
lean_ctor_set(x_135, 0, x_152);
x_82 = x_135;
x_83 = x_151;
goto block_132;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
lean_dec(x_150);
x_155 = lean_io_error_to_string(x_153);
x_156 = 3;
x_157 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_156);
x_158 = lean_array_get_size(x_144);
x_159 = lean_array_push(x_144, x_157);
lean_ctor_set_tag(x_135, 1);
lean_ctor_set(x_135, 1, x_159);
lean_ctor_set(x_135, 0, x_158);
x_82 = x_135;
x_83 = x_154;
goto block_132;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = lean_ctor_get(x_135, 1);
lean_inc(x_160);
lean_dec(x_135);
x_161 = lean_ctor_get(x_16, 12);
lean_inc(x_161);
lean_dec(x_16);
x_162 = l_System_FilePath_join(x_54, x_161);
x_163 = l_Lake_Module_recBuildLean___lambda__5___closed__4;
x_164 = l_Lean_modToFilePath(x_162, x_2, x_163);
x_165 = l_Lake_cacheFileHash(x_164, x_136);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_160);
x_82 = x_168;
x_83 = x_166;
goto block_132;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_169 = lean_ctor_get(x_165, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
lean_dec(x_165);
x_171 = lean_io_error_to_string(x_169);
x_172 = 3;
x_173 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_172);
x_174 = lean_array_get_size(x_160);
x_175 = lean_array_push(x_160, x_173);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_82 = x_176;
x_83 = x_170;
goto block_132;
}
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_54);
lean_dec(x_16);
lean_dec(x_2);
x_177 = !lean_is_exclusive(x_135);
if (x_177 == 0)
{
x_82 = x_135;
x_83 = x_136;
goto block_132;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_135, 0);
x_179 = lean_ctor_get(x_135, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_135);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_82 = x_180;
x_83 = x_136;
goto block_132;
}
}
}
block_222:
{
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_185 = lean_ctor_get(x_182, 1);
x_186 = lean_ctor_get(x_182, 0);
lean_dec(x_186);
x_187 = lean_ctor_get(x_16, 12);
lean_inc(x_187);
lean_inc(x_54);
x_188 = l_System_FilePath_join(x_54, x_187);
x_189 = l_Lake_Module_recBuildLean___lambda__4___closed__2;
lean_inc(x_2);
x_190 = l_Lean_modToFilePath(x_188, x_2, x_189);
x_191 = l_Lake_cacheFileHash(x_190, x_183);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_box(0);
lean_ctor_set(x_182, 0, x_193);
x_135 = x_182;
x_136 = x_192;
goto block_181;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_dec(x_191);
x_196 = lean_io_error_to_string(x_194);
x_197 = 3;
x_198 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*1, x_197);
x_199 = lean_array_get_size(x_185);
x_200 = lean_array_push(x_185, x_198);
lean_ctor_set_tag(x_182, 1);
lean_ctor_set(x_182, 1, x_200);
lean_ctor_set(x_182, 0, x_199);
x_135 = x_182;
x_136 = x_195;
goto block_181;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
lean_dec(x_182);
x_202 = lean_ctor_get(x_16, 12);
lean_inc(x_202);
lean_inc(x_54);
x_203 = l_System_FilePath_join(x_54, x_202);
x_204 = l_Lake_Module_recBuildLean___lambda__4___closed__2;
lean_inc(x_2);
x_205 = l_Lean_modToFilePath(x_203, x_2, x_204);
x_206 = l_Lake_cacheFileHash(x_205, x_183);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_201);
x_135 = x_209;
x_136 = x_207;
goto block_181;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_206, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_206, 1);
lean_inc(x_211);
lean_dec(x_206);
x_212 = lean_io_error_to_string(x_210);
x_213 = 3;
x_214 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_213);
x_215 = lean_array_get_size(x_201);
x_216 = lean_array_push(x_201, x_214);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_135 = x_217;
x_136 = x_211;
goto block_181;
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_54);
lean_dec(x_16);
lean_dec(x_2);
x_218 = !lean_is_exclusive(x_182);
if (x_218 == 0)
{
x_82 = x_182;
x_83 = x_183;
goto block_132;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_182, 0);
x_220 = lean_ctor_get(x_182, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_182);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_82 = x_221;
x_83 = x_183;
goto block_132;
}
}
}
block_259:
{
if (lean_obj_tag(x_223) == 0)
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_223);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_223, 1);
x_227 = lean_ctor_get(x_223, 0);
lean_dec(x_227);
x_228 = l_Lake_Module_recBuildLean___lambda__4___closed__1;
lean_inc(x_2);
x_229 = l_Lean_modToFilePath(x_56, x_2, x_228);
x_230 = l_Lake_cacheFileHash(x_229, x_224);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_box(0);
lean_ctor_set(x_223, 0, x_232);
x_182 = x_223;
x_183 = x_231;
goto block_222;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_230, 1);
lean_inc(x_234);
lean_dec(x_230);
x_235 = lean_io_error_to_string(x_233);
x_236 = 3;
x_237 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set_uint8(x_237, sizeof(void*)*1, x_236);
x_238 = lean_array_get_size(x_226);
x_239 = lean_array_push(x_226, x_237);
lean_ctor_set_tag(x_223, 1);
lean_ctor_set(x_223, 1, x_239);
lean_ctor_set(x_223, 0, x_238);
x_182 = x_223;
x_183 = x_234;
goto block_222;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_240 = lean_ctor_get(x_223, 1);
lean_inc(x_240);
lean_dec(x_223);
x_241 = l_Lake_Module_recBuildLean___lambda__4___closed__1;
lean_inc(x_2);
x_242 = l_Lean_modToFilePath(x_56, x_2, x_241);
x_243 = l_Lake_cacheFileHash(x_242, x_224);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_box(0);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_240);
x_182 = x_246;
x_183 = x_244;
goto block_222;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_247 = lean_ctor_get(x_243, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_243, 1);
lean_inc(x_248);
lean_dec(x_243);
x_249 = lean_io_error_to_string(x_247);
x_250 = 3;
x_251 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set_uint8(x_251, sizeof(void*)*1, x_250);
x_252 = lean_array_get_size(x_240);
x_253 = lean_array_push(x_240, x_251);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_182 = x_254;
x_183 = x_248;
goto block_222;
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_16);
lean_dec(x_2);
x_255 = !lean_is_exclusive(x_223);
if (x_255 == 0)
{
x_82 = x_223;
x_83 = x_224;
goto block_132;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_223, 0);
x_257 = lean_ctor_get(x_223, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_223);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_82 = x_258;
x_83 = x_224;
goto block_132;
}
}
}
block_351:
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_261 = lean_ctor_get(x_133, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_unbox(x_262);
lean_dec(x_262);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_3, 0);
lean_inc(x_264);
x_265 = lean_ctor_get_uint8(x_264, 2);
lean_dec(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_133, 1);
lean_inc(x_266);
lean_dec(x_133);
x_267 = lean_ctor_get(x_261, 1);
lean_inc(x_267);
lean_dec(x_261);
lean_inc(x_54);
lean_inc(x_16);
lean_inc(x_2);
lean_inc(x_56);
x_268 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__4), 16, 12);
lean_closure_set(x_268, 0, x_56);
lean_closure_set(x_268, 1, x_2);
lean_closure_set(x_268, 2, x_16);
lean_closure_set(x_268, 3, x_54);
lean_closure_set(x_268, 4, x_17);
lean_closure_set(x_268, 5, x_26);
lean_closure_set(x_268, 6, x_33);
lean_closure_set(x_268, 7, x_44);
lean_closure_set(x_268, 8, x_260);
lean_closure_set(x_268, 9, x_42);
lean_closure_set(x_268, 10, x_13);
lean_closure_set(x_268, 11, x_12);
x_269 = l_Lake_Module_recBuildLean___lambda__5___closed__5;
x_270 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_270, 0, x_269);
lean_closure_set(x_270, 1, x_268);
lean_inc(x_3);
x_271 = l_Lake_cacheBuildLog(x_60, x_270, x_3, x_267, x_266);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = !lean_is_exclusive(x_272);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_275 = lean_ctor_get(x_272, 1);
x_276 = lean_ctor_get(x_272, 0);
lean_dec(x_276);
x_277 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
lean_inc(x_2);
lean_inc(x_56);
x_278 = l_Lean_modToFilePath(x_56, x_2, x_277);
x_279 = l_Lake_cacheFileHash(x_278, x_273);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_281 = lean_box(0);
lean_ctor_set(x_272, 0, x_281);
x_223 = x_272;
x_224 = x_280;
goto block_259;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_282 = lean_ctor_get(x_279, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_279, 1);
lean_inc(x_283);
lean_dec(x_279);
x_284 = lean_io_error_to_string(x_282);
x_285 = 3;
x_286 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set_uint8(x_286, sizeof(void*)*1, x_285);
x_287 = lean_array_get_size(x_275);
x_288 = lean_array_push(x_275, x_286);
lean_ctor_set_tag(x_272, 1);
lean_ctor_set(x_272, 1, x_288);
lean_ctor_set(x_272, 0, x_287);
x_223 = x_272;
x_224 = x_283;
goto block_259;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_272, 1);
lean_inc(x_289);
lean_dec(x_272);
x_290 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
lean_inc(x_2);
lean_inc(x_56);
x_291 = l_Lean_modToFilePath(x_56, x_2, x_290);
x_292 = l_Lake_cacheFileHash(x_291, x_273);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
x_294 = lean_box(0);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_289);
x_223 = x_295;
x_224 = x_293;
goto block_259;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_296 = lean_ctor_get(x_292, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_292, 1);
lean_inc(x_297);
lean_dec(x_292);
x_298 = lean_io_error_to_string(x_296);
x_299 = 3;
x_300 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set_uint8(x_300, sizeof(void*)*1, x_299);
x_301 = lean_array_get_size(x_289);
x_302 = lean_array_push(x_289, x_300);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_223 = x_303;
x_224 = x_297;
goto block_259;
}
}
}
else
{
lean_object* x_304; uint8_t x_305; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_16);
lean_dec(x_2);
x_304 = lean_ctor_get(x_271, 1);
lean_inc(x_304);
lean_dec(x_271);
x_305 = !lean_is_exclusive(x_272);
if (x_305 == 0)
{
x_82 = x_272;
x_83 = x_304;
goto block_132;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_272, 0);
x_307 = lean_ctor_get(x_272, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_272);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_82 = x_308;
x_83 = x_304;
goto block_132;
}
}
}
else
{
uint8_t x_309; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_309 = !lean_is_exclusive(x_271);
if (x_309 == 0)
{
return x_271;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_271, 0);
x_311 = lean_ctor_get(x_271, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_271);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
else
{
lean_object* x_313; uint8_t x_314; 
lean_dec(x_260);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_313 = lean_ctor_get(x_133, 1);
lean_inc(x_313);
lean_dec(x_133);
x_314 = !lean_is_exclusive(x_261);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; 
x_315 = lean_ctor_get(x_261, 1);
x_316 = lean_ctor_get(x_261, 0);
lean_dec(x_316);
x_317 = l_Lake_Module_recBuildLean___lambda__5___closed__6;
x_318 = lean_io_exit(x_317, x_313);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
lean_ctor_set(x_261, 0, x_319);
x_61 = x_261;
x_62 = x_320;
goto block_81;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_321 = lean_ctor_get(x_318, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
lean_dec(x_318);
x_323 = lean_io_error_to_string(x_321);
x_324 = 3;
x_325 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set_uint8(x_325, sizeof(void*)*1, x_324);
x_326 = lean_array_get_size(x_315);
x_327 = lean_array_push(x_315, x_325);
lean_ctor_set_tag(x_261, 1);
lean_ctor_set(x_261, 1, x_327);
lean_ctor_set(x_261, 0, x_326);
x_61 = x_261;
x_62 = x_322;
goto block_81;
}
}
else
{
lean_object* x_328; uint8_t x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_261, 1);
lean_inc(x_328);
lean_dec(x_261);
x_329 = l_Lake_Module_recBuildLean___lambda__5___closed__6;
x_330 = lean_io_exit(x_329, x_313);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_328);
x_61 = x_333;
x_62 = x_332;
goto block_81;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_334 = lean_ctor_get(x_330, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_330, 1);
lean_inc(x_335);
lean_dec(x_330);
x_336 = lean_io_error_to_string(x_334);
x_337 = 3;
x_338 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*1, x_337);
x_339 = lean_array_get_size(x_328);
x_340 = lean_array_push(x_328, x_338);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
x_61 = x_341;
x_62 = x_335;
goto block_81;
}
}
}
}
else
{
lean_object* x_342; uint8_t x_343; 
lean_dec(x_260);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_342 = lean_ctor_get(x_133, 1);
lean_inc(x_342);
lean_dec(x_133);
x_343 = !lean_is_exclusive(x_261);
if (x_343 == 0)
{
lean_object* x_344; uint8_t x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_261, 0);
lean_dec(x_344);
x_345 = 1;
x_346 = lean_box(x_345);
lean_ctor_set(x_261, 0, x_346);
x_61 = x_261;
x_62 = x_342;
goto block_81;
}
else
{
lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; 
x_347 = lean_ctor_get(x_261, 1);
lean_inc(x_347);
lean_dec(x_261);
x_348 = 1;
x_349 = lean_box(x_348);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_347);
x_61 = x_350;
x_62 = x_342;
goto block_81;
}
}
}
}
}
else
{
uint8_t x_362; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_362 = !lean_is_exclusive(x_45);
if (x_362 == 0)
{
lean_object* x_363; 
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_45);
lean_ctor_set(x_363, 1, x_46);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_45, 0);
x_365 = lean_ctor_get(x_45, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_45);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_46);
return x_367;
}
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; size_t x_389; size_t x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; size_t x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint64_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_658; 
x_379 = lean_ctor_get(x_4, 1);
lean_inc(x_379);
lean_dec(x_4);
x_380 = lean_ctor_get(x_6, 1);
lean_inc(x_380);
lean_dec(x_6);
x_381 = lean_ctor_get(x_7, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_7, 1);
lean_inc(x_382);
lean_dec(x_7);
x_383 = lean_ctor_get(x_1, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_384, 2);
lean_inc(x_385);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_array_get_size(x_387);
x_389 = lean_usize_of_nat(x_388);
lean_dec(x_388);
x_390 = 0;
x_391 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_389, x_390, x_387);
x_392 = lean_ctor_get(x_386, 1);
lean_inc(x_392);
x_393 = l_Array_append___rarg(x_391, x_392);
x_394 = lean_ctor_get(x_383, 1);
lean_inc(x_394);
lean_dec(x_383);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_array_get_size(x_396);
x_398 = lean_usize_of_nat(x_397);
lean_dec(x_397);
x_399 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_398, x_390, x_396);
x_400 = l_Array_append___rarg(x_393, x_399);
x_401 = lean_ctor_get(x_395, 1);
lean_inc(x_401);
x_402 = l_Array_append___rarg(x_400, x_401);
x_403 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_402);
x_404 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
x_405 = lean_box_uint64(x_403);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_404);
x_407 = lean_ctor_get(x_384, 0);
lean_inc(x_407);
lean_dec(x_384);
x_408 = lean_ctor_get(x_385, 7);
lean_inc(x_408);
lean_inc(x_407);
x_409 = l_System_FilePath_join(x_407, x_408);
x_410 = lean_ctor_get(x_394, 2);
lean_inc(x_410);
lean_dec(x_394);
x_411 = l_System_FilePath_join(x_409, x_410);
x_412 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1;
lean_inc(x_2);
lean_inc(x_411);
x_413 = l_Lean_modToFilePath(x_411, x_2, x_412);
x_658 = l_Lake_BuildTrace_compute___at_Lake_Module_recBuildLean___spec__2(x_413, x_5);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
lean_dec(x_658);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_379);
x_414 = x_661;
x_415 = x_660;
goto block_657;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_662 = lean_ctor_get(x_658, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_658, 1);
lean_inc(x_663);
lean_dec(x_658);
x_664 = lean_io_error_to_string(x_662);
x_665 = 3;
x_666 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_666, 0, x_664);
lean_ctor_set_uint8(x_666, sizeof(void*)*1, x_665);
x_667 = lean_array_get_size(x_379);
x_668 = lean_array_push(x_379, x_666);
x_669 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_669, 0, x_667);
lean_ctor_set(x_669, 1, x_668);
x_414 = x_669;
x_415 = x_663;
goto block_657;
}
block_657:
{
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_450; lean_object* x_451; lean_object* x_501; uint8_t x_502; uint8_t x_649; 
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_414, 1);
lean_inc(x_417);
lean_dec(x_414);
x_418 = lean_ctor_get(x_3, 2);
lean_inc(x_418);
lean_inc(x_380);
x_419 = l_Lake_BuildTrace_mix(x_416, x_380);
x_420 = l_Lake_BuildTrace_mix(x_406, x_419);
x_421 = l_Lake_BuildTrace_mix(x_418, x_420);
x_422 = lean_ctor_get(x_385, 8);
lean_inc(x_422);
x_423 = l_System_FilePath_join(x_407, x_422);
x_424 = lean_ctor_get(x_385, 9);
lean_inc(x_424);
lean_inc(x_423);
x_425 = l_System_FilePath_join(x_423, x_424);
x_426 = l_Lake_Module_recBuildLean___lambda__5___closed__1;
lean_inc(x_2);
lean_inc(x_425);
x_427 = l_Lean_modToFilePath(x_425, x_2, x_426);
x_428 = l_Lake_Module_recBuildLean___lambda__5___closed__3;
lean_inc(x_2);
lean_inc(x_425);
x_429 = l_Lean_modToFilePath(x_425, x_2, x_428);
lean_inc(x_421);
x_501 = l_Lake_BuildTrace_checkUpToDate___at_Lake_Module_recBuildLean___spec__1(x_1, x_421, x_427, x_3, x_417, x_415);
x_649 = l_Lake_Module_recBuildLean___lambda__5___closed__2;
if (x_649 == 0)
{
uint8_t x_650; 
x_650 = 0;
x_502 = x_650;
goto block_648;
}
else
{
uint8_t x_651; 
x_651 = 1;
x_502 = x_651;
goto block_648;
}
block_449:
{
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = lean_ctor_get(x_430, 0);
lean_inc(x_432);
x_433 = lean_unbox(x_432);
lean_dec(x_432);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_429);
x_434 = lean_ctor_get(x_430, 1);
lean_inc(x_434);
lean_dec(x_430);
x_435 = lean_box(0);
x_436 = l_Lake_Module_recBuildLean___lambda__3(x_380, x_435, x_3, x_434, x_431);
lean_dec(x_3);
return x_436;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_437 = lean_ctor_get(x_430, 1);
lean_inc(x_437);
lean_dec(x_430);
x_438 = l_Lake_replayBuildLog(x_429, x_437, x_431);
lean_dec(x_429);
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = lean_ctor_get(x_439, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_439, 1);
lean_inc(x_442);
lean_dec(x_439);
x_443 = l_Lake_Module_recBuildLean___lambda__3(x_380, x_441, x_3, x_442, x_440);
lean_dec(x_3);
lean_dec(x_441);
return x_443;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_429);
lean_dec(x_380);
lean_dec(x_3);
x_444 = lean_ctor_get(x_430, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_430, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_446 = x_430;
} else {
 lean_dec_ref(x_430);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 2, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_445);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_431);
return x_448;
}
}
block_500:
{
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_467; 
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_453 = x_450;
} else {
 lean_dec_ref(x_450);
 x_453 = lean_box(0);
}
lean_inc(x_427);
x_467 = l_System_FilePath_parent(x_427);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; uint64_t x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_468 = lean_ctor_get(x_421, 0);
lean_inc(x_468);
lean_dec(x_421);
x_469 = lean_unbox_uint64(x_468);
lean_dec(x_468);
x_470 = lean_uint64_to_nat(x_469);
x_471 = l___private_Init_Data_Repr_0__Nat_reprFast(x_470);
x_472 = l_IO_FS_writeFile(x_427, x_471, x_451);
lean_dec(x_471);
lean_dec(x_427);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_475 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_475, 0, x_473);
x_454 = x_475;
x_455 = x_474;
goto block_466;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_472, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_472, 1);
lean_inc(x_477);
lean_dec(x_472);
x_478 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_478, 0, x_476);
x_454 = x_478;
x_455 = x_477;
goto block_466;
}
}
else
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_467, 0);
lean_inc(x_479);
lean_dec(x_467);
x_480 = l_IO_FS_createDirAll(x_479, x_451);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; uint64_t x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
lean_dec(x_480);
x_482 = lean_ctor_get(x_421, 0);
lean_inc(x_482);
lean_dec(x_421);
x_483 = lean_unbox_uint64(x_482);
lean_dec(x_482);
x_484 = lean_uint64_to_nat(x_483);
x_485 = l___private_Init_Data_Repr_0__Nat_reprFast(x_484);
x_486 = l_IO_FS_writeFile(x_427, x_485, x_481);
lean_dec(x_485);
lean_dec(x_427);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_489, 0, x_487);
x_454 = x_489;
x_455 = x_488;
goto block_466;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_486, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_486, 1);
lean_inc(x_491);
lean_dec(x_486);
x_492 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_492, 0, x_490);
x_454 = x_492;
x_455 = x_491;
goto block_466;
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_427);
lean_dec(x_421);
x_493 = lean_ctor_get(x_480, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_480, 1);
lean_inc(x_494);
lean_dec(x_480);
x_495 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_495, 0, x_493);
x_454 = x_495;
x_455 = x_494;
goto block_466;
}
}
block_466:
{
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_456 = lean_ctor_get(x_454, 0);
lean_inc(x_456);
lean_dec(x_454);
x_457 = lean_io_error_to_string(x_456);
x_458 = 3;
x_459 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set_uint8(x_459, sizeof(void*)*1, x_458);
x_460 = lean_array_get_size(x_452);
x_461 = lean_array_push(x_452, x_459);
if (lean_is_scalar(x_453)) {
 x_462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_462 = x_453;
 lean_ctor_set_tag(x_462, 1);
}
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
x_430 = x_462;
x_431 = x_455;
goto block_449;
}
else
{
uint8_t x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_454);
x_463 = 0;
x_464 = lean_box(x_463);
if (lean_is_scalar(x_453)) {
 x_465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_465 = x_453;
}
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_452);
x_430 = x_465;
x_431 = x_455;
goto block_449;
}
}
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_427);
lean_dec(x_421);
x_496 = lean_ctor_get(x_450, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_450, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_498 = x_450;
} else {
 lean_dec_ref(x_450);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(1, 2, 0);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_496);
lean_ctor_set(x_499, 1, x_497);
x_430 = x_499;
x_431 = x_451;
goto block_449;
}
}
block_648:
{
lean_object* x_503; lean_object* x_504; lean_object* x_532; lean_object* x_533; lean_object* x_557; lean_object* x_558; lean_object* x_580; 
if (x_502 == 0)
{
lean_object* x_642; 
x_642 = lean_box(0);
x_580 = x_642;
goto block_641;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_643 = lean_ctor_get(x_385, 12);
lean_inc(x_643);
lean_inc(x_423);
x_644 = l_System_FilePath_join(x_423, x_643);
x_645 = l_Lake_Module_recBuildLean___lambda__5___closed__4;
lean_inc(x_2);
x_646 = l_Lean_modToFilePath(x_644, x_2, x_645);
x_647 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_647, 0, x_646);
x_580 = x_647;
goto block_641;
}
block_531:
{
if (lean_obj_tag(x_503) == 0)
{
if (x_502 == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_423);
lean_dec(x_385);
lean_dec(x_2);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_506 = x_503;
} else {
 lean_dec_ref(x_503);
 x_506 = lean_box(0);
}
x_507 = lean_box(0);
if (lean_is_scalar(x_506)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_506;
}
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_505);
x_450 = x_508;
x_451 = x_504;
goto block_500;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_509 = lean_ctor_get(x_503, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_510 = x_503;
} else {
 lean_dec_ref(x_503);
 x_510 = lean_box(0);
}
x_511 = lean_ctor_get(x_385, 12);
lean_inc(x_511);
lean_dec(x_385);
x_512 = l_System_FilePath_join(x_423, x_511);
x_513 = l_Lake_Module_recBuildLean___lambda__5___closed__4;
x_514 = l_Lean_modToFilePath(x_512, x_2, x_513);
x_515 = l_Lake_cacheFileHash(x_514, x_504);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
lean_dec(x_515);
x_517 = lean_box(0);
if (lean_is_scalar(x_510)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_510;
}
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_509);
x_450 = x_518;
x_451 = x_516;
goto block_500;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_519 = lean_ctor_get(x_515, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_515, 1);
lean_inc(x_520);
lean_dec(x_515);
x_521 = lean_io_error_to_string(x_519);
x_522 = 3;
x_523 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set_uint8(x_523, sizeof(void*)*1, x_522);
x_524 = lean_array_get_size(x_509);
x_525 = lean_array_push(x_509, x_523);
if (lean_is_scalar(x_510)) {
 x_526 = lean_alloc_ctor(1, 2, 0);
} else {
 x_526 = x_510;
 lean_ctor_set_tag(x_526, 1);
}
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
x_450 = x_526;
x_451 = x_520;
goto block_500;
}
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_423);
lean_dec(x_385);
lean_dec(x_2);
x_527 = lean_ctor_get(x_503, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_503, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_529 = x_503;
} else {
 lean_dec_ref(x_503);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_528);
x_450 = x_530;
x_451 = x_504;
goto block_500;
}
}
block_556:
{
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_535 = x_532;
} else {
 lean_dec_ref(x_532);
 x_535 = lean_box(0);
}
x_536 = lean_ctor_get(x_385, 12);
lean_inc(x_536);
lean_inc(x_423);
x_537 = l_System_FilePath_join(x_423, x_536);
x_538 = l_Lake_Module_recBuildLean___lambda__4___closed__2;
lean_inc(x_2);
x_539 = l_Lean_modToFilePath(x_537, x_2, x_538);
x_540 = l_Lake_cacheFileHash(x_539, x_533);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_540, 1);
lean_inc(x_541);
lean_dec(x_540);
x_542 = lean_box(0);
if (lean_is_scalar(x_535)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_535;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_534);
x_503 = x_543;
x_504 = x_541;
goto block_531;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; uint8_t x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_544 = lean_ctor_get(x_540, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_540, 1);
lean_inc(x_545);
lean_dec(x_540);
x_546 = lean_io_error_to_string(x_544);
x_547 = 3;
x_548 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set_uint8(x_548, sizeof(void*)*1, x_547);
x_549 = lean_array_get_size(x_534);
x_550 = lean_array_push(x_534, x_548);
if (lean_is_scalar(x_535)) {
 x_551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_551 = x_535;
 lean_ctor_set_tag(x_551, 1);
}
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
x_503 = x_551;
x_504 = x_545;
goto block_531;
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_423);
lean_dec(x_385);
lean_dec(x_2);
x_552 = lean_ctor_get(x_532, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_532, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_554 = x_532;
} else {
 lean_dec_ref(x_532);
 x_554 = lean_box(0);
}
if (lean_is_scalar(x_554)) {
 x_555 = lean_alloc_ctor(1, 2, 0);
} else {
 x_555 = x_554;
}
lean_ctor_set(x_555, 0, x_552);
lean_ctor_set(x_555, 1, x_553);
x_450 = x_555;
x_451 = x_533;
goto block_500;
}
}
block_579:
{
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_560 = x_557;
} else {
 lean_dec_ref(x_557);
 x_560 = lean_box(0);
}
x_561 = l_Lake_Module_recBuildLean___lambda__4___closed__1;
lean_inc(x_2);
x_562 = l_Lean_modToFilePath(x_425, x_2, x_561);
x_563 = l_Lake_cacheFileHash(x_562, x_558);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_563, 1);
lean_inc(x_564);
lean_dec(x_563);
x_565 = lean_box(0);
if (lean_is_scalar(x_560)) {
 x_566 = lean_alloc_ctor(0, 2, 0);
} else {
 x_566 = x_560;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_559);
x_532 = x_566;
x_533 = x_564;
goto block_556;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_567 = lean_ctor_get(x_563, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_563, 1);
lean_inc(x_568);
lean_dec(x_563);
x_569 = lean_io_error_to_string(x_567);
x_570 = 3;
x_571 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set_uint8(x_571, sizeof(void*)*1, x_570);
x_572 = lean_array_get_size(x_559);
x_573 = lean_array_push(x_559, x_571);
if (lean_is_scalar(x_560)) {
 x_574 = lean_alloc_ctor(1, 2, 0);
} else {
 x_574 = x_560;
 lean_ctor_set_tag(x_574, 1);
}
lean_ctor_set(x_574, 0, x_572);
lean_ctor_set(x_574, 1, x_573);
x_532 = x_574;
x_533 = x_568;
goto block_556;
}
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_425);
lean_dec(x_423);
lean_dec(x_385);
lean_dec(x_2);
x_575 = lean_ctor_get(x_557, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_557, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_577 = x_557;
} else {
 lean_dec_ref(x_557);
 x_577 = lean_box(0);
}
if (lean_is_scalar(x_577)) {
 x_578 = lean_alloc_ctor(1, 2, 0);
} else {
 x_578 = x_577;
}
lean_ctor_set(x_578, 0, x_575);
lean_ctor_set(x_578, 1, x_576);
x_450 = x_578;
x_451 = x_558;
goto block_500;
}
}
block_641:
{
lean_object* x_581; lean_object* x_582; uint8_t x_583; 
x_581 = lean_ctor_get(x_501, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_unbox(x_582);
lean_dec(x_582);
if (x_583 == 0)
{
lean_object* x_584; uint8_t x_585; 
x_584 = lean_ctor_get(x_3, 0);
lean_inc(x_584);
x_585 = lean_ctor_get_uint8(x_584, 2);
lean_dec(x_584);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_586 = lean_ctor_get(x_501, 1);
lean_inc(x_586);
lean_dec(x_501);
x_587 = lean_ctor_get(x_581, 1);
lean_inc(x_587);
lean_dec(x_581);
lean_inc(x_423);
lean_inc(x_385);
lean_inc(x_2);
lean_inc(x_425);
x_588 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__4), 16, 12);
lean_closure_set(x_588, 0, x_425);
lean_closure_set(x_588, 1, x_2);
lean_closure_set(x_588, 2, x_385);
lean_closure_set(x_588, 3, x_423);
lean_closure_set(x_588, 4, x_386);
lean_closure_set(x_588, 5, x_395);
lean_closure_set(x_588, 6, x_402);
lean_closure_set(x_588, 7, x_413);
lean_closure_set(x_588, 8, x_580);
lean_closure_set(x_588, 9, x_411);
lean_closure_set(x_588, 10, x_382);
lean_closure_set(x_588, 11, x_381);
x_589 = l_Lake_Module_recBuildLean___lambda__5___closed__5;
x_590 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_590, 0, x_589);
lean_closure_set(x_590, 1, x_588);
lean_inc(x_3);
x_591 = l_Lake_cacheBuildLog(x_429, x_590, x_3, x_587, x_586);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; 
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
lean_dec(x_591);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_595 = x_592;
} else {
 lean_dec_ref(x_592);
 x_595 = lean_box(0);
}
x_596 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
lean_inc(x_2);
lean_inc(x_425);
x_597 = l_Lean_modToFilePath(x_425, x_2, x_596);
x_598 = l_Lake_cacheFileHash(x_597, x_593);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = lean_ctor_get(x_598, 1);
lean_inc(x_599);
lean_dec(x_598);
x_600 = lean_box(0);
if (lean_is_scalar(x_595)) {
 x_601 = lean_alloc_ctor(0, 2, 0);
} else {
 x_601 = x_595;
}
lean_ctor_set(x_601, 0, x_600);
lean_ctor_set(x_601, 1, x_594);
x_557 = x_601;
x_558 = x_599;
goto block_579;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_602 = lean_ctor_get(x_598, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_598, 1);
lean_inc(x_603);
lean_dec(x_598);
x_604 = lean_io_error_to_string(x_602);
x_605 = 3;
x_606 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set_uint8(x_606, sizeof(void*)*1, x_605);
x_607 = lean_array_get_size(x_594);
x_608 = lean_array_push(x_594, x_606);
if (lean_is_scalar(x_595)) {
 x_609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_609 = x_595;
 lean_ctor_set_tag(x_609, 1);
}
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
x_557 = x_609;
x_558 = x_603;
goto block_579;
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_dec(x_425);
lean_dec(x_423);
lean_dec(x_385);
lean_dec(x_2);
x_610 = lean_ctor_get(x_591, 1);
lean_inc(x_610);
lean_dec(x_591);
x_611 = lean_ctor_get(x_592, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_592, 1);
lean_inc(x_612);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_613 = x_592;
} else {
 lean_dec_ref(x_592);
 x_613 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_614 = lean_alloc_ctor(1, 2, 0);
} else {
 x_614 = x_613;
}
lean_ctor_set(x_614, 0, x_611);
lean_ctor_set(x_614, 1, x_612);
x_450 = x_614;
x_451 = x_610;
goto block_500;
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec(x_429);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_385);
lean_dec(x_380);
lean_dec(x_3);
lean_dec(x_2);
x_615 = lean_ctor_get(x_591, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_591, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_617 = x_591;
} else {
 lean_dec_ref(x_591);
 x_617 = lean_box(0);
}
if (lean_is_scalar(x_617)) {
 x_618 = lean_alloc_ctor(1, 2, 0);
} else {
 x_618 = x_617;
}
lean_ctor_set(x_618, 0, x_615);
lean_ctor_set(x_618, 1, x_616);
return x_618;
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; uint8_t x_622; lean_object* x_623; 
lean_dec(x_580);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_413);
lean_dec(x_411);
lean_dec(x_402);
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_2);
x_619 = lean_ctor_get(x_501, 1);
lean_inc(x_619);
lean_dec(x_501);
x_620 = lean_ctor_get(x_581, 1);
lean_inc(x_620);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_621 = x_581;
} else {
 lean_dec_ref(x_581);
 x_621 = lean_box(0);
}
x_622 = l_Lake_Module_recBuildLean___lambda__5___closed__6;
x_623 = lean_io_exit(x_622, x_619);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
lean_dec(x_623);
if (lean_is_scalar(x_621)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_621;
}
lean_ctor_set(x_626, 0, x_624);
lean_ctor_set(x_626, 1, x_620);
x_430 = x_626;
x_431 = x_625;
goto block_449;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_627 = lean_ctor_get(x_623, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_623, 1);
lean_inc(x_628);
lean_dec(x_623);
x_629 = lean_io_error_to_string(x_627);
x_630 = 3;
x_631 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set_uint8(x_631, sizeof(void*)*1, x_630);
x_632 = lean_array_get_size(x_620);
x_633 = lean_array_push(x_620, x_631);
if (lean_is_scalar(x_621)) {
 x_634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_634 = x_621;
 lean_ctor_set_tag(x_634, 1);
}
lean_ctor_set(x_634, 0, x_632);
lean_ctor_set(x_634, 1, x_633);
x_430 = x_634;
x_431 = x_628;
goto block_449;
}
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; lean_object* x_639; lean_object* x_640; 
lean_dec(x_580);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_413);
lean_dec(x_411);
lean_dec(x_402);
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_2);
x_635 = lean_ctor_get(x_501, 1);
lean_inc(x_635);
lean_dec(x_501);
x_636 = lean_ctor_get(x_581, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_637 = x_581;
} else {
 lean_dec_ref(x_581);
 x_637 = lean_box(0);
}
x_638 = 1;
x_639 = lean_box(x_638);
if (lean_is_scalar(x_637)) {
 x_640 = lean_alloc_ctor(0, 2, 0);
} else {
 x_640 = x_637;
}
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_640, 1, x_636);
x_430 = x_640;
x_431 = x_635;
goto block_449;
}
}
}
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_413);
lean_dec(x_411);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_402);
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_652 = lean_ctor_get(x_414, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_414, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_654 = x_414;
} else {
 lean_dec_ref(x_414);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(1, 2, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_653);
x_656 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_415);
return x_656;
}
}
}
}
else
{
uint8_t x_670; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_670 = !lean_is_exclusive(x_4);
if (x_670 == 0)
{
lean_object* x_671; 
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_4);
lean_ctor_set(x_671, 1, x_5);
return x_671;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_672 = lean_ctor_get(x_4, 0);
x_673 = lean_ctor_get(x_4, 1);
lean_inc(x_673);
lean_inc(x_672);
lean_dec(x_4);
x_674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_674, 0, x_672);
lean_ctor_set(x_674, 1, x_673);
x_675 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_5);
return x_675;
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Building ", 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Function_const___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Module_recBuildLean___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_recBuildLean___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = l_Lake_Module_recBuildLean___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Module_recParseImports___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_91 = l_Lake_Module_depsFacetConfig___closed__4;
lean_inc(x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_inc(x_5);
x_93 = lean_apply_6(x_2, x_92, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_94, 0);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_5);
x_101 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__5), 5, 3);
lean_closure_set(x_101, 0, x_1);
lean_closure_set(x_101, 1, x_8);
lean_closure_set(x_101, 2, x_5);
x_102 = l_Task_Priority_default;
x_103 = 0;
x_104 = lean_io_map_task(x_101, x_100, x_102, x_103, x_96);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_ctor_set(x_95, 0, x_105);
x_15 = x_94;
x_16 = x_106;
goto block_90;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_107 = lean_ctor_get(x_95, 0);
x_108 = lean_ctor_get(x_95, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_95);
lean_inc(x_5);
x_109 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__5), 5, 3);
lean_closure_set(x_109, 0, x_1);
lean_closure_set(x_109, 1, x_8);
lean_closure_set(x_109, 2, x_5);
x_110 = l_Task_Priority_default;
x_111 = 0;
x_112 = lean_io_map_task(x_109, x_107, x_110, x_111, x_96);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_108);
lean_ctor_set(x_94, 0, x_115);
x_15 = x_94;
x_16 = x_114;
goto block_90;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_116 = lean_ctor_get(x_94, 1);
lean_inc(x_116);
lean_dec(x_94);
x_117 = lean_ctor_get(x_95, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_95, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_119 = x_95;
} else {
 lean_dec_ref(x_95);
 x_119 = lean_box(0);
}
lean_inc(x_5);
x_120 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLean___lambda__5), 5, 3);
lean_closure_set(x_120, 0, x_1);
lean_closure_set(x_120, 1, x_8);
lean_closure_set(x_120, 2, x_5);
x_121 = l_Task_Priority_default;
x_122 = 0;
x_123 = lean_io_map_task(x_120, x_117, x_121, x_122, x_96);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
if (lean_is_scalar(x_119)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_119;
}
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_118);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_116);
x_15 = x_127;
x_16 = x_125;
goto block_90;
}
}
else
{
lean_object* x_128; uint8_t x_129; 
lean_dec(x_8);
lean_dec(x_1);
x_128 = lean_ctor_get(x_93, 1);
lean_inc(x_128);
lean_dec(x_93);
x_129 = !lean_is_exclusive(x_94);
if (x_129 == 0)
{
x_15 = x_94;
x_16 = x_128;
goto block_90;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_94, 0);
x_131 = lean_ctor_get(x_94, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_94);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_15 = x_132;
x_16 = x_128;
goto block_90;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_93);
if (x_133 == 0)
{
return x_93;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_93, 0);
x_135 = lean_ctor_get(x_93, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_93);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
block_90:
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_5, 3);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_st_ref_take(x_22, x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lake_Module_recBuildLean___closed__3;
x_27 = l_Task_Priority_default;
x_28 = 0;
lean_inc(x_20);
x_29 = lean_task_map(x_26, x_20, x_27, x_28);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_14);
x_30 = lean_array_push(x_24, x_18);
x_31 = lean_st_ref_set(x_22, x_30, x_25);
lean_dec(x_22);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lake_Module_recBuildLean___closed__4;
x_35 = lean_task_map(x_34, x_20, x_27, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_15, 0, x_36);
lean_ctor_set(x_31, 0, x_15);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lake_Module_recBuildLean___closed__4;
x_39 = lean_task_map(x_38, x_20, x_27, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_21);
lean_ctor_set(x_15, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_ctor_get(x_5, 3);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_st_ref_take(x_44, x_16);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lake_Module_recBuildLean___closed__3;
x_49 = l_Task_Priority_default;
x_50 = 0;
lean_inc(x_42);
x_51 = lean_task_map(x_48, x_42, x_49, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_14);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_46, x_52);
x_54 = lean_st_ref_set(x_44, x_53, x_47);
lean_dec(x_44);
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
x_57 = l_Lake_Module_recBuildLean___closed__4;
x_58 = lean_task_map(x_57, x_42, x_49, x_9);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_15, 0, x_59);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_5, 3);
lean_inc(x_66);
lean_dec(x_5);
x_67 = lean_st_ref_take(x_66, x_16);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lake_Module_recBuildLean___closed__3;
x_71 = l_Task_Priority_default;
x_72 = 0;
lean_inc(x_63);
x_73 = lean_task_map(x_70, x_63, x_71, x_72);
if (lean_is_scalar(x_65)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_65;
}
lean_ctor_set(x_74, 0, x_14);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_68, x_74);
x_76 = lean_st_ref_set(x_66, x_75, x_69);
lean_dec(x_66);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = l_Lake_Module_recBuildLean___closed__4;
x_80 = lean_task_map(x_79, x_63, x_71, x_9);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_64);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_62);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_14);
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_15);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_15);
lean_ctor_set(x_85, 1, x_16);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_15, 0);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_15);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_16);
return x_89;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkUpToDate___at_Lake_Module_recBuildLean___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_BuildTrace_checkUpToDate___at_Lake_Module_recBuildLean___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_Module_recBuildLean___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_compute___at_Lake_Module_recBuildLean___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLean___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Module_recBuildLean___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_3 = l_Task_Priority_default;
x_4 = 0;
x_5 = lean_task_map(x_2, x_1, x_3, x_4);
return x_5;
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
x_1 = lean_mk_string_from_bytes("leanArts", 8);
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
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 8);
lean_inc(x_14);
x_15 = l_System_FilePath_join(x_12, x_14);
x_16 = lean_ctor_get(x_13, 9);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_System_FilePath_join(x_15, x_16);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
x_20 = l_Lean_modToFilePath(x_17, x_18, x_19);
lean_inc(x_20);
x_21 = l_Lake_fetchFileTrace(x_20, x_2, x_6, x_4);
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
x_27 = l_Lake_BuildTrace_mix(x_26, x_8);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_20);
lean_ctor_set(x_22, 0, x_5);
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
x_30 = l_Lake_BuildTrace_mix(x_28, x_8);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_20);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
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
x_36 = l_Lake_BuildTrace_mix(x_33, x_8);
lean_ctor_set(x_5, 1, x_36);
lean_ctor_set(x_5, 0, x_20);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_5);
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
lean_dec(x_20);
lean_free_object(x_5);
lean_dec(x_8);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_dec(x_5);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 2);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_55, 8);
lean_inc(x_56);
x_57 = l_System_FilePath_join(x_54, x_56);
x_58 = lean_ctor_get(x_55, 9);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l_System_FilePath_join(x_57, x_58);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_dec(x_1);
x_61 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1;
x_62 = l_Lean_modToFilePath(x_59, x_60, x_61);
lean_inc(x_62);
x_63 = l_Lake_fetchFileTrace(x_62, x_2, x_6, x_4);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
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
x_70 = l_Lake_BuildTrace_mix(x_67, x_51);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_51);
x_74 = lean_ctor_get(x_63, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_75 = x_63;
} else {
 lean_dec_ref(x_63);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_64, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_64, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_78 = x_64;
} else {
 lean_dec_ref(x_64);
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
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_3);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_3);
lean_ctor_set(x_82, 1, x_4);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_3, 0);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_3);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_4);
return x_86;
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
lean_inc(x_5);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_5);
x_19 = l_Task_Priority_default;
x_20 = 0;
x_21 = lean_io_map_task(x_18, x_17, x_19, x_20, x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_12, 0, x_23);
lean_ctor_set(x_21, 0, x_11);
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
lean_ctor_set(x_12, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_5);
x_30 = l_Task_Priority_default;
x_31 = 0;
x_32 = lean_io_map_task(x_29, x_27, x_30, x_31, x_13);
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
lean_ctor_set(x_11, 0, x_36);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_41 = x_12;
} else {
 lean_dec_ref(x_12);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_closure((void*)(l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_5);
x_43 = l_Task_Priority_default;
x_44 = 0;
x_45 = lean_io_map_task(x_42, x_39, x_43, x_44, x_13);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
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
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_38);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_10);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_10, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
return x_10;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_10, 0, x_57);
return x_10;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
lean_dec(x_10);
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_61 = x_11;
} else {
 lean_dec_ref(x_11);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_5);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_10);
if (x_64 == 0)
{
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_oleanFacetConfig___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_3 = l_Task_Priority_default;
x_4 = 0;
x_5 = lean_task_map(x_2, x_1, x_3, x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Module_oleanFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 8);
lean_inc(x_14);
x_15 = l_System_FilePath_join(x_12, x_14);
x_16 = lean_ctor_get(x_13, 9);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_System_FilePath_join(x_15, x_16);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lake_Module_recBuildLean___lambda__4___closed__1;
x_20 = l_Lean_modToFilePath(x_17, x_18, x_19);
lean_inc(x_20);
x_21 = l_Lake_fetchFileTrace(x_20, x_2, x_6, x_4);
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
x_27 = l_Lake_BuildTrace_mix(x_26, x_8);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_20);
lean_ctor_set(x_22, 0, x_5);
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
x_30 = l_Lake_BuildTrace_mix(x_28, x_8);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_20);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
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
x_36 = l_Lake_BuildTrace_mix(x_33, x_8);
lean_ctor_set(x_5, 1, x_36);
lean_ctor_set(x_5, 0, x_20);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_5);
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
lean_dec(x_20);
lean_free_object(x_5);
lean_dec(x_8);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_dec(x_5);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 2);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_55, 8);
lean_inc(x_56);
x_57 = l_System_FilePath_join(x_54, x_56);
x_58 = lean_ctor_get(x_55, 9);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l_System_FilePath_join(x_57, x_58);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_dec(x_1);
x_61 = l_Lake_Module_recBuildLean___lambda__4___closed__1;
x_62 = l_Lean_modToFilePath(x_59, x_60, x_61);
lean_inc(x_62);
x_63 = l_Lake_fetchFileTrace(x_62, x_2, x_6, x_4);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
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
x_70 = l_Lake_BuildTrace_mix(x_67, x_51);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_51);
x_74 = lean_ctor_get(x_63, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_75 = x_63;
} else {
 lean_dec_ref(x_63);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_64, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_64, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_78 = x_64;
} else {
 lean_dec_ref(x_64);
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
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_3);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_3);
lean_ctor_set(x_82, 1, x_4);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_3, 0);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_3);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_4);
return x_86;
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
lean_inc(x_5);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_5);
x_19 = l_Task_Priority_default;
x_20 = 0;
x_21 = lean_io_map_task(x_18, x_17, x_19, x_20, x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_12, 0, x_23);
lean_ctor_set(x_21, 0, x_11);
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
lean_ctor_set(x_12, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_5);
x_30 = l_Task_Priority_default;
x_31 = 0;
x_32 = lean_io_map_task(x_29, x_27, x_30, x_31, x_13);
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
lean_ctor_set(x_11, 0, x_36);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_41 = x_12;
} else {
 lean_dec_ref(x_12);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_closure((void*)(l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_5);
x_43 = l_Task_Priority_default;
x_44 = 0;
x_45 = lean_io_map_task(x_42, x_39, x_43, x_44, x_13);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
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
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_38);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_10);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_10, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
return x_10;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_10, 0, x_57);
return x_10;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
lean_dec(x_10);
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_61 = x_11;
} else {
 lean_dec_ref(x_11);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_5);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_10);
if (x_64 == 0)
{
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lake_Module_ileanFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_recBuildLean___lambda__4___closed__1;
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
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Module_ileanFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_15 = l_Lake_Module_recBuildLean___lambda__4___closed__2;
x_16 = l_Lean_modToFilePath(x_13, x_14, x_15);
lean_inc(x_16);
x_17 = l_Lake_fetchFileTrace(x_16, x_2, x_5, x_4);
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
lean_ctor_set(x_23, 0, x_16);
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
lean_ctor_set(x_26, 0, x_16);
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
lean_ctor_set(x_32, 0, x_16);
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
lean_dec(x_16);
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
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_3);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_4);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
return x_52;
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
lean_inc(x_5);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_5);
x_19 = l_Task_Priority_default;
x_20 = 0;
x_21 = lean_io_map_task(x_18, x_17, x_19, x_20, x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_12, 0, x_23);
lean_ctor_set(x_21, 0, x_11);
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
lean_ctor_set(x_12, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_5);
x_30 = l_Task_Priority_default;
x_31 = 0;
x_32 = lean_io_map_task(x_29, x_27, x_30, x_31, x_13);
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
lean_ctor_set(x_11, 0, x_36);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_41 = x_12;
} else {
 lean_dec_ref(x_12);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_closure((void*)(l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_5);
x_43 = l_Task_Priority_default;
x_44 = 0;
x_45 = lean_io_map_task(x_42, x_39, x_43, x_44, x_13);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
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
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_38);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_10);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_10, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
return x_10;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_10, 0, x_57);
return x_10;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
lean_dec(x_10);
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_61 = x_11;
} else {
 lean_dec_ref(x_11);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_5);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_10);
if (x_64 == 0)
{
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lake_Module_cFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_recBuildLean___lambda__4___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_Module_cFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Module_cFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_15 = l_Lake_Module_recBuildLean___lambda__5___closed__4;
x_16 = l_Lean_modToFilePath(x_13, x_14, x_15);
lean_inc(x_16);
x_17 = l_Lake_fetchFileTrace(x_16, x_2, x_5, x_4);
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
lean_ctor_set(x_23, 0, x_16);
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
lean_ctor_set(x_26, 0, x_16);
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
lean_ctor_set(x_32, 0, x_16);
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
lean_dec(x_16);
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
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_3);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_4);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
return x_52;
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
lean_inc(x_5);
x_10 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_5);
x_19 = l_Task_Priority_default;
x_20 = 0;
x_21 = lean_io_map_task(x_18, x_17, x_19, x_20, x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_12, 0, x_23);
lean_ctor_set(x_21, 0, x_11);
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
lean_ctor_set(x_12, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_5);
x_30 = l_Task_Priority_default;
x_31 = 0;
x_32 = lean_io_map_task(x_29, x_27, x_30, x_31, x_13);
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
lean_ctor_set(x_11, 0, x_36);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_41 = x_12;
} else {
 lean_dec_ref(x_12);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_closure((void*)(l_Lake_Module_bcFacetConfig___elambda__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_5);
x_43 = l_Task_Priority_default;
x_44 = 0;
x_45 = lean_io_map_task(x_42, x_39, x_43, x_44, x_13);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
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
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_38);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_10);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_10, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
return x_10;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_10, 0, x_57);
return x_10;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
lean_dec(x_10);
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_61 = x_11;
} else {
 lean_dec_ref(x_11);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_5);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_10);
if (x_64 == 0)
{
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lake_Module_bcFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Module_recBuildLean___lambda__5___closed__4;
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
LEAN_EXPORT lean_object* l_Lake_Module_bcFacetConfig___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Module_bcFacetConfig___elambda__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Array_append___rarg(x_1, x_2);
x_10 = l_Lake_compileO(x_3, x_4, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_14 = l_Lake_platformTrace;
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
x_17 = lean_box_uint64(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lake_BuildTrace_mix(x_12, x_18);
x_20 = l_Lake_BuildTrace_mix(x_11, x_19);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__2___boxed), 8, 4);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_4);
lean_closure_set(x_21, 3, x_10);
x_22 = l_Lake_Module_recBuildLeanCToOExport___lambda__3___closed__1;
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
lean_inc(x_4);
x_24 = l_Lake_buildFileUnlessUpToDate(x_4, x_20, x_23, x_1, x_8, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_7, 1, x_29);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_25, 0, x_7);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_24, 0, x_32);
return x_24;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_36 = x_25;
} else {
 lean_dec_ref(x_25);
 x_36 = lean_box(0);
}
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_4);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_7);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_24, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_24, 0, x_44);
return x_24;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_dec(x_24);
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_48 = x_25;
} else {
 lean_dec_ref(x_25);
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
lean_free_object(x_7);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
return x_24;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_24, 0);
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_24);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_55 = lean_ctor_get(x_7, 0);
x_56 = lean_ctor_get(x_7, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_7);
x_57 = lean_ctor_get(x_1, 2);
lean_inc(x_57);
x_58 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_2);
x_59 = l_Lake_platformTrace;
x_60 = lean_uint64_mix_hash(x_58, x_59);
x_61 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
x_62 = lean_box_uint64(x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lake_BuildTrace_mix(x_57, x_63);
x_65 = l_Lake_BuildTrace_mix(x_56, x_64);
lean_inc(x_4);
x_66 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__2___boxed), 8, 4);
lean_closure_set(x_66, 0, x_3);
lean_closure_set(x_66, 1, x_2);
lean_closure_set(x_66, 2, x_4);
lean_closure_set(x_66, 3, x_55);
x_67 = l_Lake_Module_recBuildLeanCToOExport___lambda__3___closed__1;
x_68 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_68, 0, x_67);
lean_closure_set(x_68, 1, x_66);
lean_inc(x_4);
x_69 = l_Lake_buildFileUnlessUpToDate(x_4, x_65, x_68, x_1, x_8, x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
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
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_75 = x_70;
} else {
 lean_dec_ref(x_70);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_4);
lean_ctor_set(x_76, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
if (lean_is_scalar(x_72)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_72;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_4);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_80 = x_69;
} else {
 lean_dec_ref(x_69);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_83 = x_70;
} else {
 lean_dec_ref(x_70);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_4);
x_86 = lean_ctor_get(x_69, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_88 = x_69;
} else {
 lean_dec_ref(x_69);
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
uint8_t x_90; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_5);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_5);
lean_ctor_set(x_91, 1, x_6);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildLeanCToOExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiling ", 10);
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
x_1 = lean_mk_string_from_bytes("-DLEAN_EXPORTING", 16);
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
x_1 = lean_mk_string_from_bytes("c.o.export", 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = l_Lake_Module_recBuildLeanCToOExport___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Module_recParseImports___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = lean_ctor_get_uint8(x_94, sizeof(void*)*9);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_ctor_get_uint8(x_97, sizeof(void*)*9);
x_99 = l_Lake_instOrdBuildType;
x_100 = lean_box(x_95);
x_101 = lean_box(x_98);
x_102 = l_instDecidableRelLe___rarg(x_99, x_100, x_101);
x_103 = lean_ctor_get(x_94, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 3);
lean_inc(x_104);
x_105 = l_Lake_Module_cFacetConfig___closed__1;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_1);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_5);
x_107 = lean_apply_6(x_2, x_106, x_3, x_4, x_5, x_6, x_7);
if (x_102 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = l_Lake_BuildType_leancArgs(x_98);
x_188 = l_Array_append___rarg(x_187, x_103);
x_189 = l_Array_append___rarg(x_188, x_104);
x_108 = x_189;
goto block_186;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = l_Lake_BuildType_leancArgs(x_95);
x_191 = l_Array_append___rarg(x_190, x_103);
x_192 = l_Array_append___rarg(x_191, x_104);
x_108 = x_192;
goto block_186;
}
block_90:
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_5, 3);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_st_ref_take(x_22, x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lake_Module_recBuildLean___closed__3;
x_27 = l_Task_Priority_default;
x_28 = 0;
lean_inc(x_20);
x_29 = lean_task_map(x_26, x_20, x_27, x_28);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_14);
x_30 = lean_array_push(x_24, x_18);
x_31 = lean_st_ref_set(x_22, x_30, x_25);
lean_dec(x_22);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lake_Module_recBuildLean___closed__4;
x_35 = lean_task_map(x_34, x_20, x_27, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_15, 0, x_36);
lean_ctor_set(x_31, 0, x_15);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lake_Module_recBuildLean___closed__4;
x_39 = lean_task_map(x_38, x_20, x_27, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_21);
lean_ctor_set(x_15, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_ctor_get(x_5, 3);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_st_ref_take(x_44, x_16);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lake_Module_recBuildLean___closed__3;
x_49 = l_Task_Priority_default;
x_50 = 0;
lean_inc(x_42);
x_51 = lean_task_map(x_48, x_42, x_49, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_14);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_46, x_52);
x_54 = lean_st_ref_set(x_44, x_53, x_47);
lean_dec(x_44);
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
x_57 = l_Lake_Module_recBuildLean___closed__4;
x_58 = lean_task_map(x_57, x_42, x_49, x_9);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_15, 0, x_59);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_5, 3);
lean_inc(x_66);
lean_dec(x_5);
x_67 = lean_st_ref_take(x_66, x_16);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lake_Module_recBuildLean___closed__3;
x_71 = l_Task_Priority_default;
x_72 = 0;
lean_inc(x_63);
x_73 = lean_task_map(x_70, x_63, x_71, x_72);
if (lean_is_scalar(x_65)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_65;
}
lean_ctor_set(x_74, 0, x_14);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_68, x_74);
x_76 = lean_st_ref_set(x_66, x_75, x_69);
lean_dec(x_66);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = l_Lake_Module_recBuildLean___closed__4;
x_80 = lean_task_map(x_79, x_63, x_71, x_9);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_64);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_62);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_14);
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_15);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_15);
lean_ctor_set(x_85, 1, x_16);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_15, 0);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_15);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_16);
return x_89;
}
}
}
block_186:
{
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_109, 0);
x_113 = l_Lake_Module_recBuildLeanCToOExport___closed__4;
x_114 = l_Array_append___rarg(x_108, x_113);
x_115 = !lean_is_exclusive(x_112);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_116 = lean_ctor_get(x_112, 0);
x_117 = lean_ctor_get(x_92, 0);
lean_inc(x_117);
lean_dec(x_92);
x_118 = lean_ctor_get(x_93, 8);
lean_inc(x_118);
x_119 = l_System_FilePath_join(x_117, x_118);
x_120 = lean_ctor_get(x_93, 12);
lean_inc(x_120);
lean_dec(x_93);
x_121 = l_System_FilePath_join(x_119, x_120);
x_122 = l_Lake_Module_recBuildLeanCToOExport___closed__5;
x_123 = l_Lean_modToFilePath(x_121, x_8, x_122);
x_124 = lean_ctor_get(x_94, 5);
lean_inc(x_124);
lean_dec(x_94);
x_125 = lean_ctor_get(x_97, 5);
lean_inc(x_125);
lean_dec(x_97);
x_126 = l_Array_append___rarg(x_124, x_125);
lean_inc(x_5);
x_127 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__3), 6, 4);
lean_closure_set(x_127, 0, x_5);
lean_closure_set(x_127, 1, x_114);
lean_closure_set(x_127, 2, x_126);
lean_closure_set(x_127, 3, x_123);
x_128 = l_Task_Priority_default;
x_129 = 0;
x_130 = lean_io_map_task(x_127, x_116, x_128, x_129, x_110);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_ctor_set(x_112, 0, x_131);
x_15 = x_109;
x_16 = x_132;
goto block_90;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_133 = lean_ctor_get(x_112, 0);
x_134 = lean_ctor_get(x_112, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_112);
x_135 = lean_ctor_get(x_92, 0);
lean_inc(x_135);
lean_dec(x_92);
x_136 = lean_ctor_get(x_93, 8);
lean_inc(x_136);
x_137 = l_System_FilePath_join(x_135, x_136);
x_138 = lean_ctor_get(x_93, 12);
lean_inc(x_138);
lean_dec(x_93);
x_139 = l_System_FilePath_join(x_137, x_138);
x_140 = l_Lake_Module_recBuildLeanCToOExport___closed__5;
x_141 = l_Lean_modToFilePath(x_139, x_8, x_140);
x_142 = lean_ctor_get(x_94, 5);
lean_inc(x_142);
lean_dec(x_94);
x_143 = lean_ctor_get(x_97, 5);
lean_inc(x_143);
lean_dec(x_97);
x_144 = l_Array_append___rarg(x_142, x_143);
lean_inc(x_5);
x_145 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__3), 6, 4);
lean_closure_set(x_145, 0, x_5);
lean_closure_set(x_145, 1, x_114);
lean_closure_set(x_145, 2, x_144);
lean_closure_set(x_145, 3, x_141);
x_146 = l_Task_Priority_default;
x_147 = 0;
x_148 = lean_io_map_task(x_145, x_133, x_146, x_147, x_110);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_134);
lean_ctor_set(x_109, 0, x_151);
x_15 = x_109;
x_16 = x_150;
goto block_90;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_152 = lean_ctor_get(x_109, 0);
x_153 = lean_ctor_get(x_109, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_109);
x_154 = l_Lake_Module_recBuildLeanCToOExport___closed__4;
x_155 = l_Array_append___rarg(x_108, x_154);
x_156 = lean_ctor_get(x_152, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_158 = x_152;
} else {
 lean_dec_ref(x_152);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_92, 0);
lean_inc(x_159);
lean_dec(x_92);
x_160 = lean_ctor_get(x_93, 8);
lean_inc(x_160);
x_161 = l_System_FilePath_join(x_159, x_160);
x_162 = lean_ctor_get(x_93, 12);
lean_inc(x_162);
lean_dec(x_93);
x_163 = l_System_FilePath_join(x_161, x_162);
x_164 = l_Lake_Module_recBuildLeanCToOExport___closed__5;
x_165 = l_Lean_modToFilePath(x_163, x_8, x_164);
x_166 = lean_ctor_get(x_94, 5);
lean_inc(x_166);
lean_dec(x_94);
x_167 = lean_ctor_get(x_97, 5);
lean_inc(x_167);
lean_dec(x_97);
x_168 = l_Array_append___rarg(x_166, x_167);
lean_inc(x_5);
x_169 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__3), 6, 4);
lean_closure_set(x_169, 0, x_5);
lean_closure_set(x_169, 1, x_155);
lean_closure_set(x_169, 2, x_168);
lean_closure_set(x_169, 3, x_165);
x_170 = l_Task_Priority_default;
x_171 = 0;
x_172 = lean_io_map_task(x_169, x_156, x_170, x_171, x_110);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
if (lean_is_scalar(x_158)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_158;
}
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_157);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_153);
x_15 = x_176;
x_16 = x_174;
goto block_90;
}
}
else
{
lean_object* x_177; uint8_t x_178; 
lean_dec(x_108);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_8);
x_177 = lean_ctor_get(x_107, 1);
lean_inc(x_177);
lean_dec(x_107);
x_178 = !lean_is_exclusive(x_109);
if (x_178 == 0)
{
x_15 = x_109;
x_16 = x_177;
goto block_90;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_109, 0);
x_180 = lean_ctor_get(x_109, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_109);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_15 = x_181;
x_16 = x_177;
goto block_90;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_108);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
x_182 = !lean_is_exclusive(x_107);
if (x_182 == 0)
{
return x_107;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_107, 0);
x_184 = lean_ctor_get(x_107, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_107);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
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
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToOExport___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Module_recBuildLeanCToOExport___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("o", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("export", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coExportFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_recBuildLean___lambda__4___closed__2;
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
static lean_object* _init_l_Lake_Module_recBuildLeanCToONoExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("c.o.noexport", 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanCToONoExport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = l_Lake_Module_recBuildLeanCToOExport___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Module_recParseImports___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_91 = l_Lake_Module_cFacetConfig___closed__1;
lean_inc(x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_inc(x_5);
x_93 = lean_apply_6(x_2, x_92, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_98 = x_94;
} else {
 lean_dec_ref(x_94);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_101 = x_95;
} else {
 lean_dec_ref(x_95);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
lean_dec(x_1);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 2);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_105, 8);
lean_inc(x_106);
x_107 = l_System_FilePath_join(x_104, x_106);
x_108 = lean_ctor_get(x_105, 12);
lean_inc(x_108);
x_109 = l_System_FilePath_join(x_107, x_108);
x_110 = l_Lake_Module_recBuildLeanCToONoExport___closed__1;
x_111 = l_Lean_modToFilePath(x_109, x_8, x_110);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_113 = lean_ctor_get(x_112, 5);
lean_inc(x_113);
x_114 = lean_ctor_get(x_102, 1);
lean_inc(x_114);
lean_dec(x_102);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_ctor_get(x_115, 5);
lean_inc(x_116);
x_117 = l_Array_append___rarg(x_113, x_116);
x_128 = lean_ctor_get_uint8(x_112, sizeof(void*)*9);
x_129 = lean_ctor_get_uint8(x_115, sizeof(void*)*9);
x_130 = l_Lake_instOrdBuildType;
x_131 = lean_box(x_128);
x_132 = lean_box(x_129);
x_133 = l_instDecidableRelLe___rarg(x_130, x_131, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_112, 3);
lean_inc(x_134);
lean_dec(x_112);
x_135 = lean_ctor_get(x_115, 3);
lean_inc(x_135);
lean_dec(x_115);
x_136 = l_Lake_BuildType_leancArgs(x_129);
x_137 = l_Array_append___rarg(x_136, x_134);
x_138 = l_Array_append___rarg(x_137, x_135);
x_118 = x_138;
goto block_127;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_112, 3);
lean_inc(x_139);
lean_dec(x_112);
x_140 = lean_ctor_get(x_115, 3);
lean_inc(x_140);
lean_dec(x_115);
x_141 = l_Lake_BuildType_leancArgs(x_128);
x_142 = l_Array_append___rarg(x_141, x_139);
x_143 = l_Array_append___rarg(x_142, x_140);
x_118 = x_143;
goto block_127;
}
block_127:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_inc(x_5);
x_119 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__3), 6, 4);
lean_closure_set(x_119, 0, x_5);
lean_closure_set(x_119, 1, x_118);
lean_closure_set(x_119, 2, x_117);
lean_closure_set(x_119, 3, x_111);
x_120 = l_Task_Priority_default;
x_121 = 0;
x_122 = lean_io_map_task(x_119, x_99, x_120, x_121, x_96);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
if (lean_is_scalar(x_101)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_101;
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_100);
if (lean_is_scalar(x_98)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_98;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_97);
x_15 = x_126;
x_16 = x_124;
goto block_90;
}
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_8);
lean_dec(x_1);
x_144 = lean_ctor_get(x_93, 1);
lean_inc(x_144);
lean_dec(x_93);
x_145 = !lean_is_exclusive(x_94);
if (x_145 == 0)
{
x_15 = x_94;
x_16 = x_144;
goto block_90;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_94, 0);
x_147 = lean_ctor_get(x_94, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_94);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_15 = x_148;
x_16 = x_144;
goto block_90;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_93);
if (x_149 == 0)
{
return x_93;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_93, 0);
x_151 = lean_ctor_get(x_93, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_93);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
block_90:
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_5, 3);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_st_ref_take(x_22, x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lake_Module_recBuildLean___closed__3;
x_27 = l_Task_Priority_default;
x_28 = 0;
lean_inc(x_20);
x_29 = lean_task_map(x_26, x_20, x_27, x_28);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_14);
x_30 = lean_array_push(x_24, x_18);
x_31 = lean_st_ref_set(x_22, x_30, x_25);
lean_dec(x_22);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lake_Module_recBuildLean___closed__4;
x_35 = lean_task_map(x_34, x_20, x_27, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_15, 0, x_36);
lean_ctor_set(x_31, 0, x_15);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lake_Module_recBuildLean___closed__4;
x_39 = lean_task_map(x_38, x_20, x_27, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_21);
lean_ctor_set(x_15, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_ctor_get(x_5, 3);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_st_ref_take(x_44, x_16);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lake_Module_recBuildLean___closed__3;
x_49 = l_Task_Priority_default;
x_50 = 0;
lean_inc(x_42);
x_51 = lean_task_map(x_48, x_42, x_49, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_14);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_46, x_52);
x_54 = lean_st_ref_set(x_44, x_53, x_47);
lean_dec(x_44);
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
x_57 = l_Lake_Module_recBuildLean___closed__4;
x_58 = lean_task_map(x_57, x_42, x_49, x_9);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_15, 0, x_59);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_5, 3);
lean_inc(x_66);
lean_dec(x_5);
x_67 = lean_st_ref_take(x_66, x_16);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lake_Module_recBuildLean___closed__3;
x_71 = l_Task_Priority_default;
x_72 = 0;
lean_inc(x_63);
x_73 = lean_task_map(x_70, x_63, x_71, x_72);
if (lean_is_scalar(x_65)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_65;
}
lean_ctor_set(x_74, 0, x_14);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_68, x_74);
x_76 = lean_st_ref_set(x_66, x_75, x_69);
lean_dec(x_66);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = l_Lake_Module_recBuildLean___closed__4;
x_80 = lean_task_map(x_79, x_63, x_71, x_9);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_64);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_62);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_14);
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_15);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_15);
lean_ctor_set(x_85, 1, x_16);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_15, 0);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_15);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_16);
return x_89;
}
}
}
}
}
static lean_object* _init_l_Lake_Module_coNoExportFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("noexport", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_coNoExportFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Module_recBuildLean___lambda__4___closed__2;
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
x_1 = l_Lake_Module_recBuildLean___lambda__4___closed__2;
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
static lean_object* _init_l_Lake_Module_recBuildLeanBcToO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("bc.o", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildLeanBcToO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = l_Lake_Module_recBuildLeanCToOExport___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Module_recParseImports___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_91 = l_Lake_Module_bcFacetConfig___closed__1;
lean_inc(x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_inc(x_5);
x_93 = lean_apply_6(x_2, x_92, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_98 = x_94;
} else {
 lean_dec_ref(x_94);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_101 = x_95;
} else {
 lean_dec_ref(x_95);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
lean_dec(x_1);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 2);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_105, 8);
lean_inc(x_106);
x_107 = l_System_FilePath_join(x_104, x_106);
x_108 = lean_ctor_get(x_105, 12);
lean_inc(x_108);
x_109 = l_System_FilePath_join(x_107, x_108);
x_110 = l_Lake_Module_recBuildLeanBcToO___closed__1;
x_111 = l_Lean_modToFilePath(x_109, x_8, x_110);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_113 = lean_ctor_get(x_112, 5);
lean_inc(x_113);
x_114 = lean_ctor_get(x_102, 1);
lean_inc(x_114);
lean_dec(x_102);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_ctor_get(x_115, 5);
lean_inc(x_116);
x_117 = l_Array_append___rarg(x_113, x_116);
x_128 = lean_ctor_get_uint8(x_112, sizeof(void*)*9);
x_129 = lean_ctor_get_uint8(x_115, sizeof(void*)*9);
x_130 = l_Lake_instOrdBuildType;
x_131 = lean_box(x_128);
x_132 = lean_box(x_129);
x_133 = l_instDecidableRelLe___rarg(x_130, x_131, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_112, 3);
lean_inc(x_134);
lean_dec(x_112);
x_135 = lean_ctor_get(x_115, 3);
lean_inc(x_135);
lean_dec(x_115);
x_136 = l_Lake_BuildType_leancArgs(x_129);
x_137 = l_Array_append___rarg(x_136, x_134);
x_138 = l_Array_append___rarg(x_137, x_135);
x_118 = x_138;
goto block_127;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_112, 3);
lean_inc(x_139);
lean_dec(x_112);
x_140 = lean_ctor_get(x_115, 3);
lean_inc(x_140);
lean_dec(x_115);
x_141 = l_Lake_BuildType_leancArgs(x_128);
x_142 = l_Array_append___rarg(x_141, x_139);
x_143 = l_Array_append___rarg(x_142, x_140);
x_118 = x_143;
goto block_127;
}
block_127:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_inc(x_5);
x_119 = lean_alloc_closure((void*)(l_Lake_Module_recBuildLeanCToOExport___lambda__3), 6, 4);
lean_closure_set(x_119, 0, x_5);
lean_closure_set(x_119, 1, x_118);
lean_closure_set(x_119, 2, x_117);
lean_closure_set(x_119, 3, x_111);
x_120 = l_Task_Priority_default;
x_121 = 0;
x_122 = lean_io_map_task(x_119, x_99, x_120, x_121, x_96);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
if (lean_is_scalar(x_101)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_101;
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_100);
if (lean_is_scalar(x_98)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_98;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_97);
x_15 = x_126;
x_16 = x_124;
goto block_90;
}
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_8);
lean_dec(x_1);
x_144 = lean_ctor_get(x_93, 1);
lean_inc(x_144);
lean_dec(x_93);
x_145 = !lean_is_exclusive(x_94);
if (x_145 == 0)
{
x_15 = x_94;
x_16 = x_144;
goto block_90;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_94, 0);
x_147 = lean_ctor_get(x_94, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_94);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_15 = x_148;
x_16 = x_144;
goto block_90;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_93);
if (x_149 == 0)
{
return x_93;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_93, 0);
x_151 = lean_ctor_get(x_93, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_93);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
block_90:
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_5, 3);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_st_ref_take(x_22, x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lake_Module_recBuildLean___closed__3;
x_27 = l_Task_Priority_default;
x_28 = 0;
lean_inc(x_20);
x_29 = lean_task_map(x_26, x_20, x_27, x_28);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_14);
x_30 = lean_array_push(x_24, x_18);
x_31 = lean_st_ref_set(x_22, x_30, x_25);
lean_dec(x_22);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lake_Module_recBuildLean___closed__4;
x_35 = lean_task_map(x_34, x_20, x_27, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_15, 0, x_36);
lean_ctor_set(x_31, 0, x_15);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lake_Module_recBuildLean___closed__4;
x_39 = lean_task_map(x_38, x_20, x_27, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_21);
lean_ctor_set(x_15, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_ctor_get(x_5, 3);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_st_ref_take(x_44, x_16);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lake_Module_recBuildLean___closed__3;
x_49 = l_Task_Priority_default;
x_50 = 0;
lean_inc(x_42);
x_51 = lean_task_map(x_48, x_42, x_49, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_14);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_46, x_52);
x_54 = lean_st_ref_set(x_44, x_53, x_47);
lean_dec(x_44);
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
x_57 = l_Lake_Module_recBuildLean___closed__4;
x_58 = lean_task_map(x_57, x_42, x_49, x_9);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_15, 0, x_59);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_5, 3);
lean_inc(x_66);
lean_dec(x_5);
x_67 = lean_st_ref_take(x_66, x_16);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lake_Module_recBuildLean___closed__3;
x_71 = l_Task_Priority_default;
x_72 = 0;
lean_inc(x_63);
x_73 = lean_task_map(x_70, x_63, x_71, x_72);
if (lean_is_scalar(x_65)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_65;
}
lean_ctor_set(x_74, 0, x_14);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_68, x_74);
x_76 = lean_st_ref_set(x_66, x_75, x_69);
lean_dec(x_66);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = l_Lake_Module_recBuildLean___closed__4;
x_80 = lean_task_map(x_79, x_63, x_71, x_9);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_64);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_62);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_14);
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_15);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_15);
lean_ctor_set(x_85, 1, x_16);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_15, 0);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_15);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_16);
return x_89;
}
}
}
}
}
static lean_object* _init_l_Lake_Module_bcoFacetConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_recBuildLean___lambda__5___closed__4;
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
x_1 = lean_mk_string_from_bytes("the LLVM backend only supports exporting Lean symbols", 53);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_array_get_size(x_6);
x_19 = l_Lake_Module_oNoExportFacetConfig___elambda__1___closed__2;
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_7);
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
lean_inc(x_8);
lean_inc(x_6);
x_19 = lean_apply_6(x_5, x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_7 = x_25;
x_9 = x_23;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_8);
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
return x_19;
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
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_39 = x_20;
} else {
 lean_dec_ref(x_20);
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
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
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
x_1 = lean_mk_string_from_bytes("-L", 2);
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
x_10 = l_Lake_Module_recParseImports___closed__2;
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
x_1 = lean_mk_string_from_bytes("-l", 2);
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
x_10 = l_Lake_Module_recParseImports___closed__2;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_7);
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
lean_inc(x_8);
lean_inc(x_6);
x_19 = lean_apply_6(x_5, x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_7 = x_25;
x_9 = x_23;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_8);
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
return x_19;
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
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_39 = x_20;
} else {
 lean_dec_ref(x_20);
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
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_7);
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
lean_inc(x_8);
lean_inc(x_6);
x_19 = lean_apply_6(x_5, x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_7 = x_25;
x_9 = x_23;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_8);
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
return x_19;
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
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_39 = x_20;
} else {
 lean_dec_ref(x_20);
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
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; lean_object* x_59; lean_object* x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_array_get_size(x_1);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_19, x_2, x_1);
x_21 = lean_array_get_size(x_16);
x_22 = lean_usize_of_nat(x_21);
lean_inc(x_16);
x_23 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_22, x_2, x_16);
x_24 = l_Array_append___rarg(x_20, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(x_16, x_25, x_21);
lean_dec(x_16);
x_27 = l_Array_append___rarg(x_3, x_26);
x_28 = lean_ctor_get(x_4, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_5, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 6);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
x_33 = lean_ctor_get(x_32, 6);
lean_inc(x_33);
x_34 = l_Array_append___rarg(x_31, x_33);
x_35 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_34);
x_36 = l_Lake_platformTrace;
x_37 = lean_uint64_mix_hash(x_35, x_36);
x_38 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
x_39 = lean_box_uint64(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lake_BuildTrace_mix(x_28, x_40);
x_42 = l_Lake_BuildTrace_mix(x_17, x_41);
x_43 = l_Lake_BuildTrace_mix(x_7, x_42);
x_44 = l_Lake_BuildTrace_mix(x_8, x_43);
x_45 = lean_ctor_get(x_5, 0);
lean_inc(x_45);
lean_dec(x_5);
x_46 = lean_ctor_get(x_29, 8);
lean_inc(x_46);
x_47 = l_System_FilePath_join(x_45, x_46);
x_48 = lean_ctor_get(x_29, 10);
lean_inc(x_48);
lean_dec(x_29);
x_49 = l_System_FilePath_join(x_47, x_48);
x_50 = l_Lake_Module_recBuildDynlib___lambda__1___closed__1;
x_51 = 1;
x_52 = l_Lean_Name_toStringWithSep(x_50, x_51, x_9);
x_53 = l_Lake_Module_dynlibSuffix;
x_54 = lean_string_append(x_52, x_53);
x_55 = l_Lake_nameToSharedLib(x_54);
x_56 = l_System_FilePath_join(x_49, x_55);
x_57 = lean_array_get_size(x_10);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_58, x_2, x_10);
x_60 = lean_array_get_size(x_27);
x_61 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_62 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3(x_61, x_2, x_27);
x_63 = l_Array_append___rarg(x_59, x_62);
x_64 = lean_array_get_size(x_24);
x_65 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_66 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4(x_65, x_2, x_24);
x_67 = l_Array_append___rarg(x_63, x_66);
x_68 = lean_ctor_get(x_30, 7);
lean_inc(x_68);
lean_dec(x_30);
x_69 = lean_ctor_get(x_32, 7);
lean_inc(x_69);
lean_dec(x_32);
x_70 = l_Array_append___rarg(x_68, x_69);
x_71 = l_Array_append___rarg(x_67, x_70);
x_72 = l_Array_append___rarg(x_71, x_34);
lean_inc(x_56);
x_73 = lean_alloc_closure((void*)(l_Lake_compileSharedLib___boxed), 6, 2);
lean_closure_set(x_73, 0, x_56);
lean_closure_set(x_73, 1, x_72);
x_74 = l_Lake_Module_recBuildLeanCToOExport___lambda__3___closed__1;
x_75 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_75, 0, x_74);
lean_closure_set(x_75, 1, x_73);
lean_inc(x_56);
x_76 = l_Lake_buildFileUnlessUpToDate(x_56, x_44, x_75, x_4, x_14, x_12);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_76, 0);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_56);
lean_ctor_set(x_82, 1, x_54);
lean_ctor_set(x_13, 1, x_81);
lean_ctor_set(x_13, 0, x_82);
lean_ctor_set(x_77, 0, x_13);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_77, 0);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_56);
lean_ctor_set(x_85, 1, x_54);
lean_ctor_set(x_13, 1, x_83);
lean_ctor_set(x_13, 0, x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_13);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_76, 0, x_86);
return x_76;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
lean_dec(x_76);
x_88 = lean_ctor_get(x_77, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_90 = x_77;
} else {
 lean_dec_ref(x_77);
 x_90 = lean_box(0);
}
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_56);
lean_ctor_set(x_91, 1, x_54);
lean_ctor_set(x_13, 1, x_88);
lean_ctor_set(x_13, 0, x_91);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_13);
lean_ctor_set(x_92, 1, x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_87);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_56);
lean_dec(x_54);
lean_free_object(x_13);
x_94 = !lean_is_exclusive(x_76);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_76, 0);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_77);
if (x_96 == 0)
{
return x_76;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_77, 0);
x_98 = lean_ctor_get(x_77, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_77);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_76, 0, x_99);
return x_76;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_76, 1);
lean_inc(x_100);
lean_dec(x_76);
x_101 = lean_ctor_get(x_77, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_77, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_103 = x_77;
} else {
 lean_dec_ref(x_77);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_56);
lean_dec(x_54);
lean_free_object(x_13);
x_106 = !lean_is_exclusive(x_76);
if (x_106 == 0)
{
return x_76;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_76, 0);
x_108 = lean_ctor_get(x_76, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_76);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; size_t x_113; lean_object* x_114; lean_object* x_115; size_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; size_t x_152; lean_object* x_153; lean_object* x_154; size_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; size_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_110 = lean_ctor_get(x_13, 0);
x_111 = lean_ctor_get(x_13, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_13);
x_112 = lean_array_get_size(x_1);
x_113 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_114 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_113, x_2, x_1);
x_115 = lean_array_get_size(x_110);
x_116 = lean_usize_of_nat(x_115);
lean_inc(x_110);
x_117 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__2(x_116, x_2, x_110);
x_118 = l_Array_append___rarg(x_114, x_117);
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Array_filterMapM___at_Lake_Module_recBuildDeps___spec__3(x_110, x_119, x_115);
lean_dec(x_110);
x_121 = l_Array_append___rarg(x_3, x_120);
x_122 = lean_ctor_get(x_4, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_5, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 6);
lean_inc(x_125);
x_126 = lean_ctor_get(x_6, 0);
lean_inc(x_126);
lean_dec(x_6);
x_127 = lean_ctor_get(x_126, 6);
lean_inc(x_127);
x_128 = l_Array_append___rarg(x_125, x_127);
x_129 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_128);
x_130 = l_Lake_platformTrace;
x_131 = lean_uint64_mix_hash(x_129, x_130);
x_132 = l_Lake_Module_recBuildDeps___lambda__1___closed__2;
x_133 = lean_box_uint64(x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = l_Lake_BuildTrace_mix(x_122, x_134);
x_136 = l_Lake_BuildTrace_mix(x_111, x_135);
x_137 = l_Lake_BuildTrace_mix(x_7, x_136);
x_138 = l_Lake_BuildTrace_mix(x_8, x_137);
x_139 = lean_ctor_get(x_5, 0);
lean_inc(x_139);
lean_dec(x_5);
x_140 = lean_ctor_get(x_123, 8);
lean_inc(x_140);
x_141 = l_System_FilePath_join(x_139, x_140);
x_142 = lean_ctor_get(x_123, 10);
lean_inc(x_142);
lean_dec(x_123);
x_143 = l_System_FilePath_join(x_141, x_142);
x_144 = l_Lake_Module_recBuildDynlib___lambda__1___closed__1;
x_145 = 1;
x_146 = l_Lean_Name_toStringWithSep(x_144, x_145, x_9);
x_147 = l_Lake_Module_dynlibSuffix;
x_148 = lean_string_append(x_146, x_147);
x_149 = l_Lake_nameToSharedLib(x_148);
x_150 = l_System_FilePath_join(x_143, x_149);
x_151 = lean_array_get_size(x_10);
x_152 = lean_usize_of_nat(x_151);
lean_dec(x_151);
x_153 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_152, x_2, x_10);
x_154 = lean_array_get_size(x_121);
x_155 = lean_usize_of_nat(x_154);
lean_dec(x_154);
x_156 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__3(x_155, x_2, x_121);
x_157 = l_Array_append___rarg(x_153, x_156);
x_158 = lean_array_get_size(x_118);
x_159 = lean_usize_of_nat(x_158);
lean_dec(x_158);
x_160 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__4(x_159, x_2, x_118);
x_161 = l_Array_append___rarg(x_157, x_160);
x_162 = lean_ctor_get(x_124, 7);
lean_inc(x_162);
lean_dec(x_124);
x_163 = lean_ctor_get(x_126, 7);
lean_inc(x_163);
lean_dec(x_126);
x_164 = l_Array_append___rarg(x_162, x_163);
x_165 = l_Array_append___rarg(x_161, x_164);
x_166 = l_Array_append___rarg(x_165, x_128);
lean_inc(x_150);
x_167 = lean_alloc_closure((void*)(l_Lake_compileSharedLib___boxed), 6, 2);
lean_closure_set(x_167, 0, x_150);
lean_closure_set(x_167, 1, x_166);
x_168 = l_Lake_Module_recBuildLeanCToOExport___lambda__3___closed__1;
x_169 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildLeanO___spec__1___rarg), 5, 2);
lean_closure_set(x_169, 0, x_168);
lean_closure_set(x_169, 1, x_167);
lean_inc(x_150);
x_170 = l_Lake_buildFileUnlessUpToDate(x_150, x_138, x_169, x_4, x_14, x_12);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_176 = x_171;
} else {
 lean_dec_ref(x_171);
 x_176 = lean_box(0);
}
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_150);
lean_ctor_set(x_177, 1, x_148);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_174);
if (lean_is_scalar(x_176)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_176;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_175);
if (lean_is_scalar(x_173)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_173;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_172);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_150);
lean_dec(x_148);
x_181 = lean_ctor_get(x_170, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_182 = x_170;
} else {
 lean_dec_ref(x_170);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_171, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_171, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_185 = x_171;
} else {
 lean_dec_ref(x_171);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
if (lean_is_scalar(x_182)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_182;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_181);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_150);
lean_dec(x_148);
x_188 = lean_ctor_get(x_170, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_170, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_190 = x_170;
} else {
 lean_dec_ref(x_170);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_11);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_11);
lean_ctor_set(x_193, 1, x_12);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_11, 0);
x_195 = lean_ctor_get(x_11, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_11);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_12);
return x_197;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
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
x_16 = lean_box_usize(x_1);
x_17 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__1___boxed), 12, 10);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_15);
lean_closure_set(x_17, 7, x_6);
lean_closure_set(x_17, 8, x_7);
lean_closure_set(x_17, 9, x_8);
x_18 = l_Task_Priority_default;
x_19 = 0;
x_20 = lean_io_map_task(x_17, x_9, x_18, x_19, x_11);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Array_isEmpty___rarg(x_13);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_24, 0, x_13);
x_25 = 1;
x_26 = lean_task_map(x_24, x_22, x_18, x_25);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_dec(x_13);
return x_20;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = l_Array_isEmpty___rarg(x_13);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_30, 0, x_13);
x_31 = 1;
x_32 = lean_task_map(x_30, x_27, x_18, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_13);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_13);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_task_pure(x_10);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_task_pure(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_11);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
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
x_15 = lean_box_usize(x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__2___boxed), 11, 9);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_14);
lean_closure_set(x_16, 6, x_6);
lean_closure_set(x_16, 7, x_13);
lean_closure_set(x_16, 8, x_7);
x_17 = l_Task_Priority_default;
x_18 = 0;
x_19 = lean_io_bind_task(x_8, x_16, x_17, x_18, x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Array_isEmpty___rarg(x_12);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_23, 0, x_12);
x_24 = 1;
x_25 = lean_task_map(x_23, x_21, x_17, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_dec(x_12);
return x_19;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = l_Array_isEmpty___rarg(x_12);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDeps___lambda__2), 2, 1);
lean_closure_set(x_29, 0, x_12);
x_30 = 1;
x_31 = lean_task_map(x_29, x_26, x_17, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_12);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_task_pure(x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_task_pure(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_10);
return x_45;
}
}
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Linking ", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Module_recBuildDynlib___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" dynlib", 7);
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
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = l_Lake_Module_recBuildDynlib___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Module_recBuildDynlib___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_91 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__2;
lean_inc(x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_3);
x_93 = lean_apply_6(x_2, x_92, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_array_get_size(x_98);
x_101 = lean_usize_of_nat(x_100);
x_102 = 0;
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_98);
x_103 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__1(x_101, x_102, x_98, x_2, x_3, x_99, x_5, x_97, x_96);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_nat_dec_lt(x_110, x_100);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_100);
lean_dec(x_98);
x_112 = lean_ctor_get(x_1, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
lean_inc(x_113);
x_115 = l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8(x_114, x_113);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_117 = l_Lake_recBuildExternDynlibs(x_116, x_2, x_3, x_109, x_5, x_107, x_106);
lean_dec(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; size_t x_131; lean_object* x_132; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec(x_117);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
lean_dec(x_119);
x_124 = lean_ctor_get(x_120, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec(x_120);
x_126 = lean_ctor_get(x_112, 1);
lean_inc(x_126);
lean_dec(x_112);
x_127 = lean_ctor_get(x_126, 8);
lean_inc(x_127);
x_128 = lean_box(x_9);
x_129 = lean_apply_1(x_127, x_128);
x_130 = lean_array_get_size(x_129);
x_131 = lean_usize_of_nat(x_130);
lean_dec(x_130);
lean_inc(x_5);
x_132 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__1(x_1, x_131, x_102, x_129, x_2, x_3, x_123, x_5, x_122, x_121);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_136 = !lean_is_exclusive(x_133);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_133, 0);
lean_dec(x_137);
x_138 = !lean_is_exclusive(x_134);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_139 = lean_ctor_get(x_134, 0);
x_140 = l_Lake_BuildJob_collectArray___rarg(x_139, x_135);
lean_dec(x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lake_BuildJob_collectArray___rarg(x_108, x_142);
lean_dec(x_108);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lake_BuildJob_collectArray___rarg(x_124, x_145);
lean_dec(x_124);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lake_Module_recBuildDynlib___boxed__const__1;
lean_inc(x_5);
x_150 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 10, 8);
lean_closure_set(x_150, 0, x_149);
lean_closure_set(x_150, 1, x_125);
lean_closure_set(x_150, 2, x_5);
lean_closure_set(x_150, 3, x_113);
lean_closure_set(x_150, 4, x_126);
lean_closure_set(x_150, 5, x_8);
lean_closure_set(x_150, 6, x_147);
lean_closure_set(x_150, 7, x_144);
x_151 = l_Task_Priority_default;
x_152 = 0;
x_153 = lean_io_bind_task(x_141, x_150, x_151, x_152, x_148);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_ctor_set(x_134, 0, x_154);
x_15 = x_133;
x_16 = x_155;
goto block_90;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_156 = lean_ctor_get(x_134, 0);
x_157 = lean_ctor_get(x_134, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_134);
x_158 = l_Lake_BuildJob_collectArray___rarg(x_156, x_135);
lean_dec(x_156);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lake_BuildJob_collectArray___rarg(x_108, x_160);
lean_dec(x_108);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lake_BuildJob_collectArray___rarg(x_124, x_163);
lean_dec(x_124);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lake_Module_recBuildDynlib___boxed__const__1;
lean_inc(x_5);
x_168 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 10, 8);
lean_closure_set(x_168, 0, x_167);
lean_closure_set(x_168, 1, x_125);
lean_closure_set(x_168, 2, x_5);
lean_closure_set(x_168, 3, x_113);
lean_closure_set(x_168, 4, x_126);
lean_closure_set(x_168, 5, x_8);
lean_closure_set(x_168, 6, x_165);
lean_closure_set(x_168, 7, x_162);
x_169 = l_Task_Priority_default;
x_170 = 0;
x_171 = lean_io_bind_task(x_159, x_168, x_169, x_170, x_166);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_157);
lean_ctor_set(x_133, 0, x_174);
x_15 = x_133;
x_16 = x_173;
goto block_90;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_175 = lean_ctor_get(x_133, 1);
lean_inc(x_175);
lean_dec(x_133);
x_176 = lean_ctor_get(x_134, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_134, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_178 = x_134;
} else {
 lean_dec_ref(x_134);
 x_178 = lean_box(0);
}
x_179 = l_Lake_BuildJob_collectArray___rarg(x_176, x_135);
lean_dec(x_176);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lake_BuildJob_collectArray___rarg(x_108, x_181);
lean_dec(x_108);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lake_BuildJob_collectArray___rarg(x_124, x_184);
lean_dec(x_124);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lake_Module_recBuildDynlib___boxed__const__1;
lean_inc(x_5);
x_189 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 10, 8);
lean_closure_set(x_189, 0, x_188);
lean_closure_set(x_189, 1, x_125);
lean_closure_set(x_189, 2, x_5);
lean_closure_set(x_189, 3, x_113);
lean_closure_set(x_189, 4, x_126);
lean_closure_set(x_189, 5, x_8);
lean_closure_set(x_189, 6, x_186);
lean_closure_set(x_189, 7, x_183);
x_190 = l_Task_Priority_default;
x_191 = 0;
x_192 = lean_io_bind_task(x_180, x_189, x_190, x_191, x_187);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
if (lean_is_scalar(x_178)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_178;
}
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_177);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_175);
x_15 = x_196;
x_16 = x_194;
goto block_90;
}
}
else
{
lean_object* x_197; uint8_t x_198; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_113);
lean_dec(x_108);
lean_dec(x_8);
x_197 = lean_ctor_get(x_132, 1);
lean_inc(x_197);
lean_dec(x_132);
x_198 = !lean_is_exclusive(x_133);
if (x_198 == 0)
{
x_15 = x_133;
x_16 = x_197;
goto block_90;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_133, 0);
x_200 = lean_ctor_get(x_133, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_133);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_15 = x_201;
x_16 = x_197;
goto block_90;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_113);
lean_dec(x_108);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
x_202 = !lean_is_exclusive(x_132);
if (x_202 == 0)
{
return x_132;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_132, 0);
x_204 = lean_ctor_get(x_132, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_132);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; uint8_t x_207; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_206 = lean_ctor_get(x_117, 1);
lean_inc(x_206);
lean_dec(x_117);
x_207 = !lean_is_exclusive(x_118);
if (x_207 == 0)
{
x_15 = x_118;
x_16 = x_206;
goto block_90;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_118, 0);
x_209 = lean_ctor_get(x_118, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_118);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_15 = x_210;
x_16 = x_206;
goto block_90;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_117);
if (x_211 == 0)
{
return x_117;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_117, 0);
x_213 = lean_ctor_get(x_117, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_117);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_215 = lean_ctor_get(x_1, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_nat_dec_le(x_100, x_100);
lean_dec(x_100);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_98);
x_218 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
lean_inc(x_216);
x_219 = l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8(x_218, x_216);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_221 = l_Lake_recBuildExternDynlibs(x_220, x_2, x_3, x_109, x_5, x_107, x_106);
lean_dec(x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; size_t x_235; lean_object* x_236; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
lean_dec(x_221);
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
lean_dec(x_222);
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
lean_dec(x_223);
x_228 = lean_ctor_get(x_224, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 1);
lean_inc(x_229);
lean_dec(x_224);
x_230 = lean_ctor_get(x_215, 1);
lean_inc(x_230);
lean_dec(x_215);
x_231 = lean_ctor_get(x_230, 8);
lean_inc(x_231);
x_232 = lean_box(x_9);
x_233 = lean_apply_1(x_231, x_232);
x_234 = lean_array_get_size(x_233);
x_235 = lean_usize_of_nat(x_234);
lean_dec(x_234);
lean_inc(x_5);
x_236 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__5(x_1, x_235, x_102, x_233, x_2, x_3, x_227, x_5, x_226, x_225);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_239);
lean_dec(x_236);
x_240 = !lean_is_exclusive(x_237);
if (x_240 == 0)
{
lean_object* x_241; uint8_t x_242; 
x_241 = lean_ctor_get(x_237, 0);
lean_dec(x_241);
x_242 = !lean_is_exclusive(x_238);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_243 = lean_ctor_get(x_238, 0);
x_244 = l_Lake_BuildJob_collectArray___rarg(x_243, x_239);
lean_dec(x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lake_BuildJob_collectArray___rarg(x_108, x_246);
lean_dec(x_108);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = l_Lake_BuildJob_collectArray___rarg(x_228, x_249);
lean_dec(x_228);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = l_Lake_Module_recBuildDynlib___boxed__const__1;
lean_inc(x_5);
x_254 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 10, 8);
lean_closure_set(x_254, 0, x_253);
lean_closure_set(x_254, 1, x_229);
lean_closure_set(x_254, 2, x_5);
lean_closure_set(x_254, 3, x_216);
lean_closure_set(x_254, 4, x_230);
lean_closure_set(x_254, 5, x_8);
lean_closure_set(x_254, 6, x_251);
lean_closure_set(x_254, 7, x_248);
x_255 = l_Task_Priority_default;
x_256 = 0;
x_257 = lean_io_bind_task(x_245, x_254, x_255, x_256, x_252);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
lean_ctor_set(x_238, 0, x_258);
x_15 = x_237;
x_16 = x_259;
goto block_90;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_260 = lean_ctor_get(x_238, 0);
x_261 = lean_ctor_get(x_238, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_238);
x_262 = l_Lake_BuildJob_collectArray___rarg(x_260, x_239);
lean_dec(x_260);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = l_Lake_BuildJob_collectArray___rarg(x_108, x_264);
lean_dec(x_108);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = l_Lake_BuildJob_collectArray___rarg(x_228, x_267);
lean_dec(x_228);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = l_Lake_Module_recBuildDynlib___boxed__const__1;
lean_inc(x_5);
x_272 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 10, 8);
lean_closure_set(x_272, 0, x_271);
lean_closure_set(x_272, 1, x_229);
lean_closure_set(x_272, 2, x_5);
lean_closure_set(x_272, 3, x_216);
lean_closure_set(x_272, 4, x_230);
lean_closure_set(x_272, 5, x_8);
lean_closure_set(x_272, 6, x_269);
lean_closure_set(x_272, 7, x_266);
x_273 = l_Task_Priority_default;
x_274 = 0;
x_275 = lean_io_bind_task(x_263, x_272, x_273, x_274, x_270);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_261);
lean_ctor_set(x_237, 0, x_278);
x_15 = x_237;
x_16 = x_277;
goto block_90;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_279 = lean_ctor_get(x_237, 1);
lean_inc(x_279);
lean_dec(x_237);
x_280 = lean_ctor_get(x_238, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_238, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_282 = x_238;
} else {
 lean_dec_ref(x_238);
 x_282 = lean_box(0);
}
x_283 = l_Lake_BuildJob_collectArray___rarg(x_280, x_239);
lean_dec(x_280);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = l_Lake_BuildJob_collectArray___rarg(x_108, x_285);
lean_dec(x_108);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = l_Lake_BuildJob_collectArray___rarg(x_228, x_288);
lean_dec(x_228);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_292 = l_Lake_Module_recBuildDynlib___boxed__const__1;
lean_inc(x_5);
x_293 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 10, 8);
lean_closure_set(x_293, 0, x_292);
lean_closure_set(x_293, 1, x_229);
lean_closure_set(x_293, 2, x_5);
lean_closure_set(x_293, 3, x_216);
lean_closure_set(x_293, 4, x_230);
lean_closure_set(x_293, 5, x_8);
lean_closure_set(x_293, 6, x_290);
lean_closure_set(x_293, 7, x_287);
x_294 = l_Task_Priority_default;
x_295 = 0;
x_296 = lean_io_bind_task(x_284, x_293, x_294, x_295, x_291);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
if (lean_is_scalar(x_282)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_282;
}
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_281);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_279);
x_15 = x_300;
x_16 = x_298;
goto block_90;
}
}
else
{
lean_object* x_301; uint8_t x_302; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_216);
lean_dec(x_108);
lean_dec(x_8);
x_301 = lean_ctor_get(x_236, 1);
lean_inc(x_301);
lean_dec(x_236);
x_302 = !lean_is_exclusive(x_237);
if (x_302 == 0)
{
x_15 = x_237;
x_16 = x_301;
goto block_90;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_237, 0);
x_304 = lean_ctor_get(x_237, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_237);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_15 = x_305;
x_16 = x_301;
goto block_90;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_216);
lean_dec(x_108);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
x_306 = !lean_is_exclusive(x_236);
if (x_306 == 0)
{
return x_236;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_236, 0);
x_308 = lean_ctor_get(x_236, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_236);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
else
{
lean_object* x_310; uint8_t x_311; 
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_310 = lean_ctor_get(x_221, 1);
lean_inc(x_310);
lean_dec(x_221);
x_311 = !lean_is_exclusive(x_222);
if (x_311 == 0)
{
x_15 = x_222;
x_16 = x_310;
goto block_90;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_222, 0);
x_313 = lean_ctor_get(x_222, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_222);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_15 = x_314;
x_16 = x_310;
goto block_90;
}
}
}
else
{
uint8_t x_315; 
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_108);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_315 = !lean_is_exclusive(x_221);
if (x_315 == 0)
{
return x_221;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_221, 0);
x_317 = lean_ctor_get(x_221, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_221);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_319 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
x_320 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recBuildDeps___spec__6(x_98, x_102, x_101, x_319);
lean_dec(x_98);
lean_inc(x_216);
x_321 = l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8(x_320, x_216);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec(x_321);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_323 = l_Lake_recBuildExternDynlibs(x_322, x_2, x_3, x_109, x_5, x_107, x_106);
lean_dec(x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; size_t x_337; lean_object* x_338; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
x_328 = lean_ctor_get(x_324, 1);
lean_inc(x_328);
lean_dec(x_324);
x_329 = lean_ctor_get(x_325, 1);
lean_inc(x_329);
lean_dec(x_325);
x_330 = lean_ctor_get(x_326, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_326, 1);
lean_inc(x_331);
lean_dec(x_326);
x_332 = lean_ctor_get(x_215, 1);
lean_inc(x_332);
lean_dec(x_215);
x_333 = lean_ctor_get(x_332, 8);
lean_inc(x_333);
x_334 = lean_box(x_9);
x_335 = lean_apply_1(x_333, x_334);
x_336 = lean_array_get_size(x_335);
x_337 = lean_usize_of_nat(x_336);
lean_dec(x_336);
lean_inc(x_5);
x_338 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__6(x_1, x_337, x_102, x_335, x_2, x_3, x_329, x_5, x_328, x_327);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_dec(x_338);
x_342 = !lean_is_exclusive(x_339);
if (x_342 == 0)
{
lean_object* x_343; uint8_t x_344; 
x_343 = lean_ctor_get(x_339, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_340);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_345 = lean_ctor_get(x_340, 0);
x_346 = l_Lake_BuildJob_collectArray___rarg(x_345, x_341);
lean_dec(x_345);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_349 = l_Lake_BuildJob_collectArray___rarg(x_108, x_348);
lean_dec(x_108);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = l_Lake_BuildJob_collectArray___rarg(x_330, x_351);
lean_dec(x_330);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = l_Lake_Module_recBuildDynlib___boxed__const__1;
lean_inc(x_5);
x_356 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 10, 8);
lean_closure_set(x_356, 0, x_355);
lean_closure_set(x_356, 1, x_331);
lean_closure_set(x_356, 2, x_5);
lean_closure_set(x_356, 3, x_216);
lean_closure_set(x_356, 4, x_332);
lean_closure_set(x_356, 5, x_8);
lean_closure_set(x_356, 6, x_353);
lean_closure_set(x_356, 7, x_350);
x_357 = l_Task_Priority_default;
x_358 = 0;
x_359 = lean_io_bind_task(x_347, x_356, x_357, x_358, x_354);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
lean_ctor_set(x_340, 0, x_360);
x_15 = x_339;
x_16 = x_361;
goto block_90;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_362 = lean_ctor_get(x_340, 0);
x_363 = lean_ctor_get(x_340, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_340);
x_364 = l_Lake_BuildJob_collectArray___rarg(x_362, x_341);
lean_dec(x_362);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = l_Lake_BuildJob_collectArray___rarg(x_108, x_366);
lean_dec(x_108);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = l_Lake_BuildJob_collectArray___rarg(x_330, x_369);
lean_dec(x_330);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = l_Lake_Module_recBuildDynlib___boxed__const__1;
lean_inc(x_5);
x_374 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 10, 8);
lean_closure_set(x_374, 0, x_373);
lean_closure_set(x_374, 1, x_331);
lean_closure_set(x_374, 2, x_5);
lean_closure_set(x_374, 3, x_216);
lean_closure_set(x_374, 4, x_332);
lean_closure_set(x_374, 5, x_8);
lean_closure_set(x_374, 6, x_371);
lean_closure_set(x_374, 7, x_368);
x_375 = l_Task_Priority_default;
x_376 = 0;
x_377 = lean_io_bind_task(x_365, x_374, x_375, x_376, x_372);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
lean_ctor_set(x_339, 0, x_380);
x_15 = x_339;
x_16 = x_379;
goto block_90;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_381 = lean_ctor_get(x_339, 1);
lean_inc(x_381);
lean_dec(x_339);
x_382 = lean_ctor_get(x_340, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_340, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_384 = x_340;
} else {
 lean_dec_ref(x_340);
 x_384 = lean_box(0);
}
x_385 = l_Lake_BuildJob_collectArray___rarg(x_382, x_341);
lean_dec(x_382);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = l_Lake_BuildJob_collectArray___rarg(x_108, x_387);
lean_dec(x_108);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = l_Lake_BuildJob_collectArray___rarg(x_330, x_390);
lean_dec(x_330);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = l_Lake_Module_recBuildDynlib___boxed__const__1;
lean_inc(x_5);
x_395 = lean_alloc_closure((void*)(l_Lake_Module_recBuildDynlib___lambda__3___boxed), 10, 8);
lean_closure_set(x_395, 0, x_394);
lean_closure_set(x_395, 1, x_331);
lean_closure_set(x_395, 2, x_5);
lean_closure_set(x_395, 3, x_216);
lean_closure_set(x_395, 4, x_332);
lean_closure_set(x_395, 5, x_8);
lean_closure_set(x_395, 6, x_392);
lean_closure_set(x_395, 7, x_389);
x_396 = l_Task_Priority_default;
x_397 = 0;
x_398 = lean_io_bind_task(x_386, x_395, x_396, x_397, x_393);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
if (lean_is_scalar(x_384)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_384;
}
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_383);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_381);
x_15 = x_402;
x_16 = x_400;
goto block_90;
}
}
else
{
lean_object* x_403; uint8_t x_404; 
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_216);
lean_dec(x_108);
lean_dec(x_8);
x_403 = lean_ctor_get(x_338, 1);
lean_inc(x_403);
lean_dec(x_338);
x_404 = !lean_is_exclusive(x_339);
if (x_404 == 0)
{
x_15 = x_339;
x_16 = x_403;
goto block_90;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_339, 0);
x_406 = lean_ctor_get(x_339, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_339);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
x_15 = x_407;
x_16 = x_403;
goto block_90;
}
}
}
else
{
uint8_t x_408; 
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_216);
lean_dec(x_108);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
x_408 = !lean_is_exclusive(x_338);
if (x_408 == 0)
{
return x_338;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_338, 0);
x_410 = lean_ctor_get(x_338, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_338);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
else
{
lean_object* x_412; uint8_t x_413; 
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_412 = lean_ctor_get(x_323, 1);
lean_inc(x_412);
lean_dec(x_323);
x_413 = !lean_is_exclusive(x_324);
if (x_413 == 0)
{
x_15 = x_324;
x_16 = x_412;
goto block_90;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_324, 0);
x_415 = lean_ctor_get(x_324, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_324);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
x_15 = x_416;
x_16 = x_412;
goto block_90;
}
}
}
else
{
uint8_t x_417; 
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_108);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_417 = !lean_is_exclusive(x_323);
if (x_417 == 0)
{
return x_323;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_323, 0);
x_419 = lean_ctor_get(x_323, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_323);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
}
}
else
{
lean_object* x_421; uint8_t x_422; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_421 = lean_ctor_get(x_103, 1);
lean_inc(x_421);
lean_dec(x_103);
x_422 = !lean_is_exclusive(x_104);
if (x_422 == 0)
{
x_15 = x_104;
x_16 = x_421;
goto block_90;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_104, 0);
x_424 = lean_ctor_get(x_104, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_104);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
x_15 = x_425;
x_16 = x_421;
goto block_90;
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_426 = !lean_is_exclusive(x_103);
if (x_426 == 0)
{
return x_103;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_103, 0);
x_428 = lean_ctor_get(x_103, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_103);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
else
{
lean_object* x_430; uint8_t x_431; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_430 = lean_ctor_get(x_93, 1);
lean_inc(x_430);
lean_dec(x_93);
x_431 = !lean_is_exclusive(x_94);
if (x_431 == 0)
{
x_15 = x_94;
x_16 = x_430;
goto block_90;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_94, 0);
x_433 = lean_ctor_get(x_94, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_94);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
x_15 = x_434;
x_16 = x_430;
goto block_90;
}
}
}
else
{
uint8_t x_435; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_435 = !lean_is_exclusive(x_93);
if (x_435 == 0)
{
return x_93;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_93, 0);
x_437 = lean_ctor_get(x_93, 1);
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_93);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
return x_438;
}
}
block_90:
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_5, 3);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_st_ref_take(x_22, x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lake_Module_recBuildLean___closed__3;
x_27 = l_Task_Priority_default;
x_28 = 0;
lean_inc(x_20);
x_29 = lean_task_map(x_26, x_20, x_27, x_28);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_14);
x_30 = lean_array_push(x_24, x_18);
x_31 = lean_st_ref_set(x_22, x_30, x_25);
lean_dec(x_22);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lake_Module_recBuildLean___closed__4;
x_35 = lean_task_map(x_34, x_20, x_27, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_15, 0, x_36);
lean_ctor_set(x_31, 0, x_15);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lake_Module_recBuildLean___closed__4;
x_39 = lean_task_map(x_38, x_20, x_27, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_21);
lean_ctor_set(x_15, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_ctor_get(x_5, 3);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_st_ref_take(x_44, x_16);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lake_Module_recBuildLean___closed__3;
x_49 = l_Task_Priority_default;
x_50 = 0;
lean_inc(x_42);
x_51 = lean_task_map(x_48, x_42, x_49, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_14);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_46, x_52);
x_54 = lean_st_ref_set(x_44, x_53, x_47);
lean_dec(x_44);
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
x_57 = l_Lake_Module_recBuildLean___closed__4;
x_58 = lean_task_map(x_57, x_42, x_49, x_9);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_15, 0, x_59);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_5, 3);
lean_inc(x_66);
lean_dec(x_5);
x_67 = lean_st_ref_take(x_66, x_16);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lake_Module_recBuildLean___closed__3;
x_71 = l_Task_Priority_default;
x_72 = 0;
lean_inc(x_63);
x_73 = lean_task_map(x_70, x_63, x_71, x_72);
if (lean_is_scalar(x_65)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_65;
}
lean_ctor_set(x_74, 0, x_14);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_68, x_74);
x_76 = lean_st_ref_set(x_66, x_75, x_69);
lean_dec(x_66);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = l_Lake_Module_recBuildLean___closed__4;
x_80 = lean_task_map(x_79, x_63, x_71, x_9);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_64);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_62);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_14);
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_15);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_15);
lean_ctor_set(x_85, 1, x_16);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_15, 0);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_15);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_16);
return x_89;
}
}
}
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__5(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDynlib___spec__6(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Lake_Module_recBuildDynlib___lambda__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; lean_object* x_13; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = l_Lake_Module_recBuildDynlib___lambda__2(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_recBuildDynlib___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = l_Lake_Module_recBuildDynlib___lambda__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_Module_dynlibFacetConfig___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Functor_discard___at_Lake_Module_depsFacetConfig___spec__1___closed__2;
x_3 = l_Task_Priority_default;
x_4 = 0;
x_5 = lean_task_map(x_2, x_1, x_3, x_4);
return x_5;
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
x_2 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__3;
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
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__2;
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
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__2;
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
x_2 = l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2;
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
x_2 = l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__2;
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
l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_recBuildPrecompileDynlibs_go___spec__8___closed__2);
l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_recBuildPrecompileDynlibs_go___spec__18___lambda__2___closed__2);
l_Lake_recBuildPrecompileDynlibs___closed__1 = _init_l_Lake_recBuildPrecompileDynlibs___closed__1();
lean_mark_persistent(l_Lake_recBuildPrecompileDynlibs___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_Module_recParseImports___spec__2___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recParseImports___spec__4___closed__3);
l_List_filterMapTR_go___at_Lake_Module_recParseImports___spec__5___closed__1 = _init_l_List_filterMapTR_go___at_Lake_Module_recParseImports___spec__5___closed__1();
lean_mark_persistent(l_List_filterMapTR_go___at_Lake_Module_recParseImports___spec__5___closed__1);
l_Lake_Module_recParseImports___closed__1 = _init_l_Lake_Module_recParseImports___closed__1();
lean_mark_persistent(l_Lake_Module_recParseImports___closed__1);
l_Lake_Module_recParseImports___closed__2 = _init_l_Lake_Module_recParseImports___closed__2();
lean_mark_persistent(l_Lake_Module_recParseImports___closed__2);
l_Lake_Module_recParseImports___closed__3 = _init_l_Lake_Module_recParseImports___closed__3();
lean_mark_persistent(l_Lake_Module_recParseImports___closed__3);
l_Lake_Module_importsFacetConfig___closed__1 = _init_l_Lake_Module_importsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__1);
l_Lake_Module_importsFacetConfig___closed__2 = _init_l_Lake_Module_importsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_importsFacetConfig___closed__2);
l_Lake_Module_importsFacetConfig = _init_l_Lake_Module_importsFacetConfig();
lean_mark_persistent(l_Lake_Module_importsFacetConfig);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputeTransImports___spec__3___closed__2);
l_Lake_Module_transImportsFacetConfig___closed__1 = _init_l_Lake_Module_transImportsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig___closed__1);
l_Lake_Module_transImportsFacetConfig___closed__2 = _init_l_Lake_Module_transImportsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig___closed__2);
l_Lake_Module_transImportsFacetConfig = _init_l_Lake_Module_transImportsFacetConfig();
lean_mark_persistent(l_Lake_Module_transImportsFacetConfig);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Module_recComputePrecompileImports___spec__1___closed__2);
l_Lake_Module_precompileImportsFacetConfig___closed__1 = _init_l_Lake_Module_precompileImportsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_Module_precompileImportsFacetConfig___closed__1);
l_Lake_Module_precompileImportsFacetConfig___closed__2 = _init_l_Lake_Module_precompileImportsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_Module_precompileImportsFacetConfig___closed__2);
l_Lake_Module_precompileImportsFacetConfig = _init_l_Lake_Module_precompileImportsFacetConfig();
lean_mark_persistent(l_Lake_Module_precompileImportsFacetConfig);
l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Module_recBuildDeps___spec__2___closed__2);
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
l_Lake_Module_recBuildDeps___boxed__const__1 = _init_l_Lake_Module_recBuildDeps___boxed__const__1();
lean_mark_persistent(l_Lake_Module_recBuildDeps___boxed__const__1);
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
l_Lake_Module_recBuildLean___lambda__1___closed__1 = _init_l_Lake_Module_recBuildLean___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLean___lambda__1___closed__1);
l_Lake_Module_recBuildLean___lambda__4___closed__1 = _init_l_Lake_Module_recBuildLean___lambda__4___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLean___lambda__4___closed__1);
l_Lake_Module_recBuildLean___lambda__4___closed__2 = _init_l_Lake_Module_recBuildLean___lambda__4___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildLean___lambda__4___closed__2);
l_Lake_Module_recBuildLean___lambda__5___closed__1 = _init_l_Lake_Module_recBuildLean___lambda__5___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLean___lambda__5___closed__1);
l_Lake_Module_recBuildLean___lambda__5___closed__2 = _init_l_Lake_Module_recBuildLean___lambda__5___closed__2();
l_Lake_Module_recBuildLean___lambda__5___closed__3 = _init_l_Lake_Module_recBuildLean___lambda__5___closed__3();
lean_mark_persistent(l_Lake_Module_recBuildLean___lambda__5___closed__3);
l_Lake_Module_recBuildLean___lambda__5___closed__4 = _init_l_Lake_Module_recBuildLean___lambda__5___closed__4();
lean_mark_persistent(l_Lake_Module_recBuildLean___lambda__5___closed__4);
l_Lake_Module_recBuildLean___lambda__5___closed__5 = _init_l_Lake_Module_recBuildLean___lambda__5___closed__5();
lean_mark_persistent(l_Lake_Module_recBuildLean___lambda__5___closed__5);
l_Lake_Module_recBuildLean___lambda__5___closed__6 = _init_l_Lake_Module_recBuildLean___lambda__5___closed__6();
l_Lake_Module_recBuildLean___closed__1 = _init_l_Lake_Module_recBuildLean___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLean___closed__1);
l_Lake_Module_recBuildLean___closed__2 = _init_l_Lake_Module_recBuildLean___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildLean___closed__2);
l_Lake_Module_recBuildLean___closed__3 = _init_l_Lake_Module_recBuildLean___closed__3();
lean_mark_persistent(l_Lake_Module_recBuildLean___closed__3);
l_Lake_Module_recBuildLean___closed__4 = _init_l_Lake_Module_recBuildLean___closed__4();
lean_mark_persistent(l_Lake_Module_recBuildLean___closed__4);
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
l_Lake_Module_recBuildLeanCToOExport___lambda__3___closed__1 = _init_l_Lake_Module_recBuildLeanCToOExport___lambda__3___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildLeanCToOExport___lambda__3___closed__1);
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
l_Lake_Module_recBuildDynlib___lambda__1___closed__1 = _init_l_Lake_Module_recBuildDynlib___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___lambda__1___closed__1);
l_Lake_Module_recBuildDynlib___closed__1 = _init_l_Lake_Module_recBuildDynlib___closed__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___closed__1);
l_Lake_Module_recBuildDynlib___closed__2 = _init_l_Lake_Module_recBuildDynlib___closed__2();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___closed__2);
l_Lake_Module_recBuildDynlib___boxed__const__1 = _init_l_Lake_Module_recBuildDynlib___boxed__const__1();
lean_mark_persistent(l_Lake_Module_recBuildDynlib___boxed__const__1);
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

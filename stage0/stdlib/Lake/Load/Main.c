// Lean compiler output
// Module: Lake.Load.Main
// Imports: Init Lake.Util.EStateT Lake.Util.StoreInsts Lake.Config.Workspace Lake.Build.Topological Lake.Build.Module Lake.Build.Package Lake.Build.Library Lake.Load.Materialize Lake.Load.Package Lake.Load.Elab Lake.Load.Toml
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
lean_object* l_Lake_PackageEntry_setConfigFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadLeanConfig___closed__2;
extern lean_object* l_Lake_initPackageFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___closed__4;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___lambda__3___closed__1;
static lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_partition_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__2;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__7;
static lean_object* l_Lake_loadLeanConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_loadDepPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___closed__2;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_io_rename(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdMismatchError___boxed(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_inDirectory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_saveToFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_updateAndMaterialize___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__16___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__3;
static lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_map___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_setInherited(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
lean_object* l_Lake_RBArray_empty___rarg(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__5;
lean_object* l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_setManifestFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadDepPackage___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_stdMismatchError(lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11(lean_object*, uint8_t, lean_object*, size_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4;
static lean_object* l_Lake_stdMismatchError___closed__6;
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_initModuleFacetConfigs;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_updateAndMaterialize___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___at_Lake_Workspace_materializeDeps___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_initLibraryFacetConfigs;
LEAN_EXPORT lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___at_Lake_Workspace_updateAndMaterialize___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__10___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___closed__2;
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___closed__5;
LEAN_EXPORT lean_object* l_Lake_loadPackage___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__4;
static lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3___closed__1;
static lean_object* l_Lake_loadPackage___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_materializeDeps___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__6;
static lean_object* l_Lake_Workspace_materializeDeps___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lake_loadPackage___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__1;
static lean_object* l_Lake_Workspace_materializeDeps___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_configFileExists___closed__1;
lean_object* l_Lake_PackageConfig_loadFromEnv(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__2;
extern lean_object* l_Std_Format_defWidth;
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_importConfigFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__5;
static lean_object* l_Lake_stdMismatchError___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__9;
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__4;
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackage___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at_Lake_Workspace_materializeDeps___spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at_Lake_Workspace_materializeDeps___spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__4;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_configFileExists___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__10(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__8;
static lean_object* l_Lake_stdMismatchError___closed__1;
static lean_object* l_Lake_loadWorkspaceRoot___closed__1;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadDepPackage(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___closed__4;
static lean_object* l_Lake_loadWorkspaceRoot___closed__2;
static lean_object* l_Lake_Workspace_updateAndMaterialize___closed__1;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__4(lean_object*);
lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackage___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_Lake_loadLeanConfig___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___closed__3;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadPackage___closed__6;
static lean_object* l_Lake_stdMismatchError___closed__4;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__3;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_loadFromEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_loadPackage___closed__3;
LEAN_EXPORT lean_object* l_Lake_configFileExists(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_materializeDeps___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_OpenDecl_instToString___spec__1(lean_object*);
static lean_object* l_Lake_loadPackage___lambda__2___closed__2;
lean_object* l_Lake_Manifest_addPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__7;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
static lean_object* l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Lake_loadPackage___lambda__1(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__1;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_loadLeanConfig___closed__2;
x_2 = l_Lake_RBArray_empty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = l_Lake_importConfigFile(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_108; lean_object* x_109; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_9);
x_108 = l_Lake_PackageConfig_loadFromEnv(x_9, x_11);
x_109 = l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(x_108, x_6);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_ctor_set(x_5, 0, x_110);
x_12 = x_5;
x_13 = x_111;
goto block_107;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_dec(x_109);
x_114 = lean_io_error_to_string(x_112);
x_115 = 3;
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = lean_array_get_size(x_10);
x_118 = lean_array_push(x_10, x_116);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_118);
lean_ctor_set(x_5, 0, x_117);
x_12 = x_5;
x_13 = x_113;
goto block_107;
}
block_107:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_inc(x_17);
x_18 = l_System_FilePath_join(x_16, x_17);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 6);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lake_defaultManifestFile;
x_24 = l_Lake_loadLeanConfig___closed__1;
x_25 = l_Lake_loadLeanConfig___closed__3;
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_14);
lean_ctor_set(x_27, 3, x_19);
lean_ctor_set(x_27, 4, x_23);
lean_ctor_set(x_27, 5, x_21);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_24);
lean_ctor_set(x_27, 8, x_25);
lean_ctor_set(x_27, 9, x_25);
lean_ctor_set(x_27, 10, x_22);
lean_ctor_set(x_27, 11, x_22);
lean_ctor_set(x_27, 12, x_24);
lean_ctor_set(x_27, 13, x_22);
lean_ctor_set(x_27, 14, x_24);
lean_ctor_set(x_27, 15, x_24);
lean_ctor_set(x_27, 16, x_26);
lean_inc(x_9);
x_28 = l_Lake_Package_loadFromEnv(x_27, x_9, x_11, x_15, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_9);
lean_ctor_set(x_29, 0, x_34);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_28, 0, x_38);
return x_28;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_42 = x_29;
} else {
 lean_dec_ref(x_29);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_9);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_28);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_28, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
return x_28;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_28, 0, x_51);
return x_28;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
lean_dec(x_28);
x_53 = lean_ctor_get(x_29, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_29, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_55 = x_29;
} else {
 lean_dec_ref(x_29);
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
lean_dec(x_9);
x_58 = !lean_is_exclusive(x_28);
if (x_58 == 0)
{
return x_28;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_28, 0);
x_60 = lean_ctor_get(x_28, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_28);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_20, 0);
lean_inc(x_62);
lean_dec(x_20);
x_63 = l_Lake_loadLeanConfig___closed__1;
x_64 = l_Lake_loadLeanConfig___closed__3;
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_66, 0, x_18);
lean_ctor_set(x_66, 1, x_17);
lean_ctor_set(x_66, 2, x_14);
lean_ctor_set(x_66, 3, x_19);
lean_ctor_set(x_66, 4, x_62);
lean_ctor_set(x_66, 5, x_21);
lean_ctor_set(x_66, 6, x_63);
lean_ctor_set(x_66, 7, x_63);
lean_ctor_set(x_66, 8, x_64);
lean_ctor_set(x_66, 9, x_64);
lean_ctor_set(x_66, 10, x_22);
lean_ctor_set(x_66, 11, x_22);
lean_ctor_set(x_66, 12, x_63);
lean_ctor_set(x_66, 13, x_22);
lean_ctor_set(x_66, 14, x_63);
lean_ctor_set(x_66, 15, x_63);
lean_ctor_set(x_66, 16, x_65);
lean_inc(x_9);
x_67 = l_Lake_Package_loadFromEnv(x_66, x_9, x_11, x_15, x_13);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_9);
lean_ctor_set(x_68, 0, x_73);
return x_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_68, 0);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_9);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_67, 0, x_77);
return x_67;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_67, 1);
lean_inc(x_78);
lean_dec(x_67);
x_79 = lean_ctor_get(x_68, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_68, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_81 = x_68;
} else {
 lean_dec_ref(x_68);
 x_81 = lean_box(0);
}
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_9);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_78);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_9);
x_85 = !lean_is_exclusive(x_67);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_67, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_68);
if (x_87 == 0)
{
return x_67;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_68, 0);
x_89 = lean_ctor_get(x_68, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_68);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_67, 0, x_90);
return x_67;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_67, 1);
lean_inc(x_91);
lean_dec(x_67);
x_92 = lean_ctor_get(x_68, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_68, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_94 = x_68;
} else {
 lean_dec_ref(x_68);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_91);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_9);
x_97 = !lean_is_exclusive(x_67);
if (x_97 == 0)
{
return x_67;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_67, 0);
x_99 = lean_ctor_get(x_67, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_67);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_12);
if (x_101 == 0)
{
lean_object* x_102; 
if (lean_is_scalar(x_7)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_7;
}
lean_ctor_set(x_102, 0, x_12);
lean_ctor_set(x_102, 1, x_13);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_12, 0);
x_104 = lean_ctor_get(x_12, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_12);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
if (lean_is_scalar(x_7)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_7;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_13);
return x_106;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_191; lean_object* x_192; 
x_119 = lean_ctor_get(x_5, 0);
x_120 = lean_ctor_get(x_5, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_5);
x_121 = lean_ctor_get(x_1, 5);
lean_inc(x_121);
lean_inc(x_119);
x_191 = l_Lake_PackageConfig_loadFromEnv(x_119, x_121);
x_192 = l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(x_191, x_6);
lean_dec(x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_120);
x_122 = x_195;
x_123 = x_194;
goto block_190;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_io_error_to_string(x_196);
x_199 = 3;
x_200 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_199);
x_201 = lean_array_get_size(x_120);
x_202 = lean_array_push(x_120, x_200);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_122 = x_203;
x_123 = x_197;
goto block_190;
}
block_190:
{
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_7);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_ctor_get(x_1, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_1, 2);
lean_inc(x_127);
lean_inc(x_127);
x_128 = l_System_FilePath_join(x_126, x_127);
x_129 = lean_ctor_get(x_1, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_124, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_1, 6);
lean_inc(x_131);
lean_dec(x_1);
x_132 = lean_box(0);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = l_Lake_defaultManifestFile;
x_134 = l_Lake_loadLeanConfig___closed__1;
x_135 = l_Lake_loadLeanConfig___closed__3;
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_137, 0, x_128);
lean_ctor_set(x_137, 1, x_127);
lean_ctor_set(x_137, 2, x_124);
lean_ctor_set(x_137, 3, x_129);
lean_ctor_set(x_137, 4, x_133);
lean_ctor_set(x_137, 5, x_131);
lean_ctor_set(x_137, 6, x_134);
lean_ctor_set(x_137, 7, x_134);
lean_ctor_set(x_137, 8, x_135);
lean_ctor_set(x_137, 9, x_135);
lean_ctor_set(x_137, 10, x_132);
lean_ctor_set(x_137, 11, x_132);
lean_ctor_set(x_137, 12, x_134);
lean_ctor_set(x_137, 13, x_132);
lean_ctor_set(x_137, 14, x_134);
lean_ctor_set(x_137, 15, x_134);
lean_ctor_set(x_137, 16, x_136);
lean_inc(x_119);
x_138 = l_Lake_Package_loadFromEnv(x_137, x_119, x_121, x_125, x_123);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_144 = x_139;
} else {
 lean_dec_ref(x_139);
 x_144 = lean_box(0);
}
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_119);
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
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_119);
x_148 = lean_ctor_get(x_138, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_149 = x_138;
} else {
 lean_dec_ref(x_138);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_139, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_139, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_152 = x_139;
} else {
 lean_dec_ref(x_139);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
if (lean_is_scalar(x_149)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_149;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_148);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_119);
x_155 = lean_ctor_get(x_138, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_138, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_157 = x_138;
} else {
 lean_dec_ref(x_138);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_130, 0);
lean_inc(x_159);
lean_dec(x_130);
x_160 = l_Lake_loadLeanConfig___closed__1;
x_161 = l_Lake_loadLeanConfig___closed__3;
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_163, 0, x_128);
lean_ctor_set(x_163, 1, x_127);
lean_ctor_set(x_163, 2, x_124);
lean_ctor_set(x_163, 3, x_129);
lean_ctor_set(x_163, 4, x_159);
lean_ctor_set(x_163, 5, x_131);
lean_ctor_set(x_163, 6, x_160);
lean_ctor_set(x_163, 7, x_160);
lean_ctor_set(x_163, 8, x_161);
lean_ctor_set(x_163, 9, x_161);
lean_ctor_set(x_163, 10, x_132);
lean_ctor_set(x_163, 11, x_132);
lean_ctor_set(x_163, 12, x_160);
lean_ctor_set(x_163, 13, x_132);
lean_ctor_set(x_163, 14, x_160);
lean_ctor_set(x_163, 15, x_160);
lean_ctor_set(x_163, 16, x_162);
lean_inc(x_119);
x_164 = l_Lake_Package_loadFromEnv(x_163, x_119, x_121, x_125, x_123);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
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
x_168 = lean_ctor_get(x_165, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_170 = x_165;
} else {
 lean_dec_ref(x_165);
 x_170 = lean_box(0);
}
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_119);
if (lean_is_scalar(x_170)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_170;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_169);
if (lean_is_scalar(x_167)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_167;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_166);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_119);
x_174 = lean_ctor_get(x_164, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_175 = x_164;
} else {
 lean_dec_ref(x_164);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_165, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_165, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_178 = x_165;
} else {
 lean_dec_ref(x_165);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
if (lean_is_scalar(x_175)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_175;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_174);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_119);
x_181 = lean_ctor_get(x_164, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_164, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_183 = x_164;
} else {
 lean_dec_ref(x_164);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_1);
x_185 = lean_ctor_get(x_122, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_122, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_187 = x_122;
} else {
 lean_dec_ref(x_122);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
if (lean_is_scalar(x_7)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_7;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_123);
return x_189;
}
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_4);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_4, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_5);
if (x_206 == 0)
{
return x_4;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_5, 0);
x_208 = lean_ctor_get(x_5, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_5);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_4, 0, x_209);
return x_4;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_4, 1);
lean_inc(x_210);
lean_dec(x_4);
x_211 = lean_ctor_get(x_5, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_5, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_213 = x_5;
} else {
 lean_dec_ref(x_5);
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
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lake_loadLeanConfig___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_configFileExists___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_configFileExists___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("toml", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_configFileExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Lake_configFileExists___closed__1;
lean_inc(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
x_6 = l_Lake_configFileExists___closed__2;
x_7 = l_System_FilePath_addExtension(x_1, x_6);
x_8 = l_System_FilePath_pathExists(x_5, x_2);
lean_dec(x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_System_FilePath_pathExists(x_7, x_11);
lean_dec(x_7);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = l_System_FilePath_pathExists(x_1, x_2);
lean_dec(x_1);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_loadPackage___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackage___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_loadPackage___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set(x_12, 4, x_5);
lean_ctor_set(x_12, 5, x_6);
lean_ctor_set(x_12, 6, x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*7, x_7);
x_13 = l_Lake_loadLeanConfig(x_12, x_10, x_11);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = l_Lake_loadPackage___lambda__2___closed__1;
x_20 = l_Lake_loadPackage___lambda__2___closed__2;
x_21 = l_Prod_map___rarg(x_19, x_20, x_18);
lean_ctor_set(x_14, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = l_Lake_loadPackage___lambda__2___closed__1;
x_25 = l_Lake_loadPackage___lambda__2___closed__2;
x_26 = l_Prod_map___rarg(x_24, x_25, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_31 = x_14;
} else {
 lean_dec_ref(x_14);
 x_31 = lean_box(0);
}
x_32 = l_Lake_loadPackage___lambda__2___closed__1;
x_33 = l_Lake_loadPackage___lambda__2___closed__2;
x_34 = l_Prod_map___rarg(x_32, x_33, x_29);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_13, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_13, 0, x_42);
return x_13;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_dec(x_13);
x_44 = lean_ctor_get(x_14, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_46 = x_14;
} else {
 lean_dec_ref(x_14);
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
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
return x_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
static lean_object* _init_l_Lake_loadPackage___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackage___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": configuration has unsupported file extension: ", 48);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lake_configFileExists___closed__1;
x_12 = lean_string_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
x_13 = l_Lake_configFileExists___closed__2;
x_14 = lean_string_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = l_Lake_loadPackage___lambda__3___closed__1;
x_16 = lean_string_append(x_15, x_2);
x_17 = l_Lake_loadPackage___lambda__3___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_3);
x_20 = lean_string_append(x_19, x_15);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_9);
x_24 = lean_array_push(x_9, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = l_Lake_loadTomlConfig(x_4, x_5, x_6, x_9, x_10);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_28, 0, x_34);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_27, 0, x_39);
return x_27;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_43 = x_28;
} else {
 lean_dec_ref(x_28);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_27);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_27, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_28);
if (x_50 == 0)
{
return x_27;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_28, 0);
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_28);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_27, 0, x_53);
return x_27;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_dec(x_27);
x_55 = lean_ctor_get(x_28, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_28, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_57 = x_28;
} else {
 lean_dec_ref(x_28);
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
x_60 = !lean_is_exclusive(x_27);
if (x_60 == 0)
{
return x_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_64 = l_Lake_loadLeanConfig(x_7, x_9, x_10);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = l_Lake_loadPackage___lambda__2___closed__1;
x_71 = l_Lake_loadPackage___lambda__2___closed__2;
x_72 = l_Prod_map___rarg(x_70, x_71, x_69);
lean_ctor_set(x_65, 0, x_72);
return x_64;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_65, 0);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_65);
x_75 = l_Lake_loadPackage___lambda__2___closed__1;
x_76 = l_Lake_loadPackage___lambda__2___closed__2;
x_77 = l_Prod_map___rarg(x_75, x_76, x_73);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_64, 0, x_78);
return x_64;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_ctor_get(x_65, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_65, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_82 = x_65;
} else {
 lean_dec_ref(x_65);
 x_82 = lean_box(0);
}
x_83 = l_Lake_loadPackage___lambda__2___closed__1;
x_84 = l_Lake_loadPackage___lambda__2___closed__2;
x_85 = l_Prod_map___rarg(x_83, x_84, x_80);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
return x_87;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_64);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_64, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_65);
if (x_90 == 0)
{
return x_64;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_65, 0);
x_92 = lean_ctor_get(x_65, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_65);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_64, 0, x_93);
return x_64;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_64, 1);
lean_inc(x_94);
lean_dec(x_64);
x_95 = lean_ctor_get(x_65, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_65, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_97 = x_65;
} else {
 lean_dec_ref(x_65);
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
return x_99;
}
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_64);
if (x_100 == 0)
{
return x_64;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_64, 0);
x_102 = lean_ctor_get(x_64, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_64);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
static lean_object* _init_l_Lake_loadPackage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": no configuration file with a supported extension:\n", 52);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackage___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackage___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackage___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" and ", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackage___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" are both present; using ", 25);
return x_1;
}
}
static lean_object* _init_l_Lake_loadPackage___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": configuration file not found: ", 32);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_12 = lean_ctor_get(x_2, 6);
lean_inc(x_12);
lean_inc(x_8);
x_13 = l_System_FilePath_extension(x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_2);
x_14 = l_Lake_configFileExists___closed__1;
lean_inc(x_8);
x_15 = l_System_FilePath_addExtension(x_8, x_14);
x_16 = l_Lake_configFileExists___closed__2;
x_17 = l_System_FilePath_addExtension(x_8, x_16);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_System_FilePath_join(x_6, x_7);
lean_inc(x_15);
lean_inc(x_18);
x_19 = l_System_FilePath_join(x_18, x_15);
lean_inc(x_17);
lean_inc(x_18);
x_20 = l_System_FilePath_join(x_18, x_17);
x_21 = l_System_FilePath_pathExists(x_19, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_System_FilePath_pathExists(x_20, x_23);
x_25 = lean_unbox(x_22);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_24, 0);
lean_dec(x_29);
x_30 = l_Lake_loadPackage___lambda__3___closed__1;
x_31 = lean_string_append(x_30, x_1);
lean_dec(x_1);
x_32 = l_Lake_loadPackage___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_19);
lean_dec(x_19);
x_35 = l_Lake_loadPackage___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_20);
lean_dec(x_20);
x_38 = lean_string_append(x_37, x_30);
x_39 = 3;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_array_get_size(x_3);
x_42 = lean_array_push(x_3, x_40);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_24, 0, x_43);
return x_24;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_dec(x_24);
x_45 = l_Lake_loadPackage___lambda__3___closed__1;
x_46 = lean_string_append(x_45, x_1);
lean_dec(x_1);
x_47 = l_Lake_loadPackage___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_19);
lean_dec(x_19);
x_50 = l_Lake_loadPackage___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_20);
lean_dec(x_20);
x_53 = lean_string_append(x_52, x_45);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_3);
x_57 = lean_array_push(x_3, x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_44);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_dec(x_24);
x_61 = l_Lake_loadTomlConfig(x_18, x_7, x_17, x_3, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_62, 0, x_68);
return x_61;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_62, 0);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_62);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_61, 0, x_73);
return x_61;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_61, 1);
lean_inc(x_74);
lean_dec(x_61);
x_75 = lean_ctor_get(x_62, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_77 = x_62;
} else {
 lean_dec_ref(x_62);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
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
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_74);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_61);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_61, 0);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_62);
if (x_84 == 0)
{
return x_61;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_62, 0);
x_86 = lean_ctor_get(x_62, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_62);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_61, 0, x_87);
return x_61;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_61, 1);
lean_inc(x_88);
lean_dec(x_61);
x_89 = lean_ctor_get(x_62, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_62, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_91 = x_62;
} else {
 lean_dec_ref(x_62);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_88);
return x_93;
}
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_61);
if (x_94 == 0)
{
return x_61;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_61, 0);
x_96 = lean_ctor_get(x_61, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_61);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_98; uint8_t x_99; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_98 = lean_ctor_get(x_24, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_17);
lean_dec(x_1);
x_100 = lean_ctor_get(x_24, 1);
lean_inc(x_100);
lean_dec(x_24);
x_101 = lean_box(0);
x_102 = l_Lake_loadPackage___lambda__2(x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_101, x_3, x_100);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_103 = lean_ctor_get(x_24, 1);
lean_inc(x_103);
lean_dec(x_24);
x_104 = l_Lake_loadPackage___lambda__3___closed__1;
x_105 = lean_string_append(x_104, x_1);
lean_dec(x_1);
x_106 = l_Lake_loadPackage___closed__3;
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_string_append(x_107, x_15);
x_109 = l_Lake_loadPackage___closed__4;
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_string_append(x_110, x_17);
lean_dec(x_17);
x_112 = l_Lake_loadPackage___closed__5;
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_string_append(x_113, x_15);
x_115 = lean_string_append(x_114, x_104);
x_116 = 1;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = lean_array_push(x_3, x_117);
x_119 = lean_box(0);
x_120 = l_Lake_loadPackage___lambda__2(x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_119, x_118, x_103);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_121 = lean_ctor_get(x_13, 0);
lean_inc(x_121);
lean_dec(x_13);
lean_inc(x_7);
x_122 = l_System_FilePath_join(x_6, x_7);
lean_inc(x_8);
lean_inc(x_122);
x_123 = l_System_FilePath_join(x_122, x_8);
x_124 = l_System_FilePath_pathExists(x_123, x_4);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
x_129 = l_Lake_loadPackage___lambda__3___closed__1;
x_130 = lean_string_append(x_129, x_1);
lean_dec(x_1);
x_131 = l_Lake_loadPackage___closed__6;
x_132 = lean_string_append(x_130, x_131);
x_133 = lean_string_append(x_132, x_123);
lean_dec(x_123);
x_134 = lean_string_append(x_133, x_129);
x_135 = 3;
x_136 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_135);
x_137 = lean_array_get_size(x_3);
x_138 = lean_array_push(x_3, x_136);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_124, 0, x_139);
return x_124;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_140 = lean_ctor_get(x_124, 1);
lean_inc(x_140);
lean_dec(x_124);
x_141 = l_Lake_loadPackage___lambda__3___closed__1;
x_142 = lean_string_append(x_141, x_1);
lean_dec(x_1);
x_143 = l_Lake_loadPackage___closed__6;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_string_append(x_144, x_123);
lean_dec(x_123);
x_146 = lean_string_append(x_145, x_141);
x_147 = 3;
x_148 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_147);
x_149 = lean_array_get_size(x_3);
x_150 = lean_array_push(x_3, x_148);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_140);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_124, 1);
lean_inc(x_153);
lean_dec(x_124);
x_154 = lean_box(0);
x_155 = l_Lake_loadPackage___lambda__3(x_121, x_1, x_123, x_122, x_7, x_8, x_2, x_154, x_3, x_153);
lean_dec(x_123);
lean_dec(x_1);
lean_dec(x_121);
return x_155;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Lake_loadPackage___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_12, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_loadPackage___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadDepPackage(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_134; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_134 = lean_ctor_get(x_7, 0);
lean_inc(x_134);
x_15 = x_134;
goto block_133;
block_133:
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_132; 
x_16 = 0;
x_17 = l_Lean_Name_toString(x_15, x_16);
x_132 = lean_ctor_get(x_7, 1);
lean_inc(x_132);
lean_dec(x_7);
x_18 = x_132;
goto block_131;
block_131:
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
x_19 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set(x_19, 4, x_13);
lean_ctor_set(x_19, 5, x_2);
lean_ctor_set(x_19, 6, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*7, x_3);
x_20 = l_Lake_loadPackage(x_17, x_19, x_5, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_22, 1);
lean_dec(x_29);
lean_ctor_set(x_22, 1, x_4);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
lean_ctor_set(x_21, 0, x_31);
return x_20;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_34 = x_22;
} else {
 lean_dec_ref(x_22);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_20, 0, x_36);
return x_20;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_dec(x_20);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_39 = x_21;
} else {
 lean_dec_ref(x_21);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_22, 0);
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
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_4);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_39;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_dec(x_20);
x_46 = !lean_is_exclusive(x_21);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_21, 1);
x_48 = lean_ctor_get(x_21, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_22);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_22, 0);
x_51 = lean_ctor_get(x_22, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_23, 0);
lean_inc(x_52);
lean_dec(x_23);
x_53 = l_Lake_Workspace_addFacetsFromEnv(x_52, x_2, x_4);
lean_dec(x_2);
x_54 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_53, x_45);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_ctor_set(x_22, 1, x_56);
lean_ctor_set(x_54, 0, x_21);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_22, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_21);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_free_object(x_22);
lean_dec(x_50);
x_60 = !lean_is_exclusive(x_54);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_54, 0);
x_62 = lean_io_error_to_string(x_61);
x_63 = 3;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_array_get_size(x_47);
x_66 = lean_array_push(x_47, x_64);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_66);
lean_ctor_set(x_21, 0, x_65);
lean_ctor_set_tag(x_54, 0);
lean_ctor_set(x_54, 0, x_21);
return x_54;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_54, 0);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_54);
x_69 = lean_io_error_to_string(x_67);
x_70 = 3;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_get_size(x_47);
x_73 = lean_array_push(x_47, x_71);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_73);
lean_ctor_set(x_21, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_21);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_22, 0);
lean_inc(x_75);
lean_dec(x_22);
x_76 = lean_ctor_get(x_23, 0);
lean_inc(x_76);
lean_dec(x_23);
x_77 = l_Lake_Workspace_addFacetsFromEnv(x_76, x_2, x_4);
lean_dec(x_2);
x_78 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_77, x_45);
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
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
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_79);
lean_ctor_set(x_21, 0, x_82);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_21);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_75);
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_86 = x_78;
} else {
 lean_dec_ref(x_78);
 x_86 = lean_box(0);
}
x_87 = lean_io_error_to_string(x_84);
x_88 = 3;
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = lean_array_get_size(x_47);
x_91 = lean_array_push(x_47, x_89);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_91);
lean_ctor_set(x_21, 0, x_90);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_86;
 lean_ctor_set_tag(x_92, 0);
}
lean_ctor_set(x_92, 0, x_21);
lean_ctor_set(x_92, 1, x_85);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_21, 1);
lean_inc(x_93);
lean_dec(x_21);
x_94 = lean_ctor_get(x_22, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_95 = x_22;
} else {
 lean_dec_ref(x_22);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_23, 0);
lean_inc(x_96);
lean_dec(x_23);
x_97 = l_Lake_Workspace_addFacetsFromEnv(x_96, x_2, x_4);
lean_dec(x_2);
x_98 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_97, x_45);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_95;
}
lean_ctor_set(x_102, 0, x_94);
lean_ctor_set(x_102, 1, x_99);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_93);
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_101;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_100);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_95);
lean_dec(x_94);
x_105 = lean_ctor_get(x_98, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_98, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_107 = x_98;
} else {
 lean_dec_ref(x_98);
 x_107 = lean_box(0);
}
x_108 = lean_io_error_to_string(x_105);
x_109 = 3;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_array_get_size(x_93);
x_112 = lean_array_push(x_93, x_110);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
if (lean_is_scalar(x_107)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_107;
 lean_ctor_set_tag(x_114, 0);
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_106);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_4);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_20);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_20, 0);
lean_dec(x_116);
x_117 = !lean_is_exclusive(x_21);
if (x_117 == 0)
{
return x_20;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_21, 0);
x_119 = lean_ctor_get(x_21, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_21);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_20, 0, x_120);
return x_20;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_20, 1);
lean_inc(x_121);
lean_dec(x_20);
x_122 = lean_ctor_get(x_21, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_21, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_124 = x_21;
} else {
 lean_dec_ref(x_21);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_121);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_4);
lean_dec(x_2);
x_127 = !lean_is_exclusive(x_20);
if (x_127 == 0)
{
return x_20;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_20, 0);
x_129 = lean_ctor_get(x_20, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_20);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadDepPackage___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_loadDepPackage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_loadDepPackage(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_searchPathRef;
return x_1;
}
}
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[root]", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lake_Env_leanSearchPath(x_4);
x_6 = l_Lake_loadWorkspaceRoot___closed__1;
x_7 = lean_st_ref_set(x_6, x_5, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_loadWorkspaceRoot___closed__2;
lean_inc(x_1);
x_10 = l_Lake_loadPackage(x_9, x_1, x_2, x_8);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = l_Lake_loadLeanConfig___closed__1;
x_23 = l_Lake_initModuleFacetConfigs;
x_24 = l_Lake_initPackageFacetConfigs;
x_25 = l_Lake_initLibraryFacetConfigs;
x_26 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set(x_26, 5, x_24);
lean_ctor_set(x_26, 6, x_25);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_1);
lean_ctor_set(x_11, 0, x_26);
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_10);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_ctor_get(x_1, 5);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lake_Workspace_addFacetsFromEnv(x_27, x_28, x_26);
lean_dec(x_28);
x_30 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_29, x_14);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_11, 0, x_32);
lean_ctor_set(x_30, 0, x_11);
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
lean_ctor_set(x_11, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_io_error_to_string(x_37);
x_39 = 3;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_array_get_size(x_17);
x_42 = lean_array_push(x_17, x_40);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_42);
lean_ctor_set(x_11, 0, x_41);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_11);
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_io_error_to_string(x_43);
x_46 = 3;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_array_get_size(x_17);
x_49 = lean_array_push(x_17, x_47);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_49);
lean_ctor_set(x_11, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_11);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_dec(x_11);
x_52 = lean_ctor_get(x_12, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_box(0);
x_55 = l_Lake_loadLeanConfig___closed__1;
x_56 = l_Lake_initModuleFacetConfigs;
x_57 = l_Lake_initPackageFacetConfigs;
x_58 = l_Lake_initLibraryFacetConfigs;
x_59 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_54);
lean_ctor_set(x_59, 4, x_56);
lean_ctor_set(x_59, 5, x_57);
lean_ctor_set(x_59, 6, x_58);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_60; 
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_51);
lean_ctor_set(x_10, 0, x_60);
return x_10;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_10);
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
lean_dec(x_53);
x_62 = lean_ctor_get(x_1, 5);
lean_inc(x_62);
lean_dec(x_1);
x_63 = l_Lake_Workspace_addFacetsFromEnv(x_61, x_62, x_59);
lean_dec(x_62);
x_64 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_63, x_14);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
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
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_51);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
 x_72 = lean_box(0);
}
x_73 = lean_io_error_to_string(x_70);
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_array_get_size(x_51);
x_77 = lean_array_push(x_51, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_72;
 lean_ctor_set_tag(x_79, 0);
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_71);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_80 = lean_ctor_get(x_10, 1);
lean_inc(x_80);
lean_dec(x_10);
x_81 = lean_ctor_get(x_11, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_82 = x_11;
} else {
 lean_dec_ref(x_11);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_12, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_12, 1);
lean_inc(x_84);
lean_dec(x_12);
x_85 = lean_box(0);
x_86 = l_Lake_loadLeanConfig___closed__1;
x_87 = l_Lake_initModuleFacetConfigs;
x_88 = l_Lake_initPackageFacetConfigs;
x_89 = l_Lake_initLibraryFacetConfigs;
x_90 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_4);
lean_ctor_set(x_90, 2, x_86);
lean_ctor_set(x_90, 3, x_85);
lean_ctor_set(x_90, 4, x_87);
lean_ctor_set(x_90, 5, x_88);
lean_ctor_set(x_90, 6, x_89);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_1);
if (lean_is_scalar(x_82)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_82;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_81);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_80);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_84, 0);
lean_inc(x_93);
lean_dec(x_84);
x_94 = lean_ctor_get(x_1, 5);
lean_inc(x_94);
lean_dec(x_1);
x_95 = l_Lake_Workspace_addFacetsFromEnv(x_93, x_94, x_90);
lean_dec(x_94);
x_96 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_95, x_80);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_82;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_81);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_96, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_104 = x_96;
} else {
 lean_dec_ref(x_96);
 x_104 = lean_box(0);
}
x_105 = lean_io_error_to_string(x_102);
x_106 = 3;
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_106);
x_108 = lean_array_get_size(x_81);
x_109 = lean_array_push(x_81, x_107);
if (lean_is_scalar(x_82)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_82;
 lean_ctor_set_tag(x_110, 1);
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
if (lean_is_scalar(x_104)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_104;
 lean_ctor_set_tag(x_111, 0);
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_103);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_4);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_10);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_10, 0);
lean_dec(x_113);
x_114 = !lean_is_exclusive(x_11);
if (x_114 == 0)
{
return x_10;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_11, 0);
x_116 = lean_ctor_get(x_11, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_11);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_10, 0, x_117);
return x_10;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_10, 1);
lean_inc(x_118);
lean_dec(x_10);
x_119 = lean_ctor_get(x_11, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_11, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_121 = x_11;
} else {
 lean_dec_ref(x_11);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_118);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_4);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_10);
if (x_124 == 0)
{
return x_10;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_10, 0);
x_126 = lean_ctor_get(x_10, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_10);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__2___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_List_reverse___rarg(x_5);
x_8 = l_List_reverse___rarg(x_6);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = l_List_reverse___rarg(x_9);
x_12 = l_List_reverse___rarg(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_name_eq(x_16, x_1);
if (x_20 == 0)
{
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_3, 0, x_2);
x_2 = x_17;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_3, 1, x_2);
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_name_eq(x_23, x_1);
if (x_27 == 0)
{
lean_object* x_28; 
lean_ctor_set(x_2, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_26);
x_2 = x_24;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_30; 
lean_ctor_set(x_2, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_2);
x_2 = x_24;
x_3 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_36 = x_3;
} else {
 lean_dec_ref(x_3);
 x_36 = lean_box(0);
}
x_37 = lean_name_eq(x_32, x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_34);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
x_2 = x_33;
x_3 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_35);
if (lean_is_scalar(x_36)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_36;
}
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_41);
x_2 = x_33;
x_3 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__4___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg(x_1, x_2, x_4, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__1___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_apply_3(x_2, x_3, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_inc(x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__2), 5, 4);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_8);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__2___rarg), 5, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, lean_box(0));
lean_closure_set(x_13, 2, lean_box(0));
lean_closure_set(x_13, 3, x_11);
x_14 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3___closed__1;
x_17 = l_List_partition_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__3(x_1, x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_15);
x_21 = l_List_appendTR___rarg(x_19, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_apply_2(x_2, lean_box(0), x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
lean_inc(x_8);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3), 6, 5);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_3);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__4___rarg), 5, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, lean_box(0));
lean_closure_set(x_13, 2, lean_box(0));
lean_closure_set(x_13, 3, x_11);
x_14 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__1___rarg), 4, 0);
return x_3;
}
}
static lean_object* _init_l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  ", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = 1;
x_8 = l_Lean_Name_toString(x_5, x_7);
x_9 = l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lake_loadPackage___lambda__3___closed__1;
x_12 = lean_string_append(x_10, x_11);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_12);
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = 1;
x_17 = l_Lean_Name_toString(x_14, x_16);
x_18 = l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lake_loadPackage___lambda__3___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_1 = x_15;
x_2 = x_22;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dependency cycle detected:\n", 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6(x_5, x_1);
x_7 = l_Lake_loadPackage___closed__2;
x_8 = l_String_intercalate(x_7, x_6);
x_9 = l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lake_loadPackage___lambda__3___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_apply_2(x_2, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_box(0);
lean_inc(x_1);
x_7 = l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg(x_1, x_4, x_3, x_6);
x_8 = lean_alloc_closure((void*)(l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1), 4, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_1);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("the 'std' package has been renamed to '", 39);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' and moved to the\n'leanprover-community' organization; downstream packages which wish to\nupdate to the new std should replace\n\n  require std from\n    git \"https://github.com/leanprover/std4\"", 191);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n\nin their Lake configuration file with\n\n  require ", 51);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" from\n    git \"https://github.com/leanprover-community/", 55);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\"", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n\n", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdMismatchError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_3 = l_Lake_stdMismatchError___closed__1;
x_4 = lean_string_append(x_3, x_1);
x_5 = l_Lake_stdMismatchError___closed__2;
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_string_append(x_6, x_2);
x_8 = l_Lake_stdMismatchError___closed__3;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_1);
x_11 = l_Lake_stdMismatchError___closed__4;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_1);
x_14 = l_Lake_stdMismatchError___closed__5;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_2);
x_17 = l_Lake_stdMismatchError___closed__6;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_stdMismatchError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdMismatchError(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = lean_array_uget(x_3, x_4);
lean_inc(x_7);
lean_inc(x_1);
x_12 = lean_apply_4(x_11, x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_6 = x_15;
x_8 = x_16;
x_9 = x_14;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_29 = x_13;
} else {
 lean_dec_ref(x_13);
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
else
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_7);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_8);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
return x_37;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": running post-update hooks", 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
x_10 = lean_ctor_get(x_9, 15);
lean_inc(x_10);
x_11 = l_Array_isEmpty___rarg(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 1;
lean_inc(x_13);
x_15 = l_Lean_Name_toString(x_13, x_14);
x_16 = l_Lake_loadPackage___lambda__3___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = 1;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_array_push(x_6, x_21);
x_23 = lean_array_get_size(x_10);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
x_26 = 1;
x_27 = lean_usize_add(x_2, x_26);
x_28 = lean_box(0);
x_2 = x_27;
x_4 = x_28;
x_6 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_23, x_23);
if (x_30 == 0)
{
size_t x_31; size_t x_32; lean_object* x_33; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
x_31 = 1;
x_32 = lean_usize_add(x_2, x_31);
x_33 = lean_box(0);
x_2 = x_32;
x_4 = x_33;
x_6 = x_22;
goto _start;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_37 = lean_box(0);
lean_inc(x_5);
x_38 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2(x_9, x_13, x_10, x_35, x_36, x_37, x_5, x_22, x_7);
lean_dec(x_10);
lean_dec(x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = 1;
x_44 = lean_usize_add(x_2, x_43);
x_2 = x_44;
x_4 = x_41;
x_6 = x_42;
x_7 = x_40;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_38, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_38, 0, x_51);
return x_38;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_dec(x_38);
x_53 = lean_ctor_get(x_39, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_55 = x_39;
} else {
 lean_dec_ref(x_39);
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
x_58 = !lean_is_exclusive(x_38);
if (x_58 == 0)
{
return x_38;
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
return x_61;
}
}
}
}
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
lean_dec(x_10);
lean_dec(x_9);
x_62 = 1;
x_63 = lean_usize_add(x_2, x_62);
x_64 = lean_box(0);
x_2 = x_63;
x_4 = x_64;
goto _start;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_5);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_6);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_7);
return x_67;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__1(x_1, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_7);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_7, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 4);
lean_inc(x_17);
lean_dec(x_7);
lean_ctor_set(x_12, 0, x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lake_PackageEntry_setManifestFile(x_12, x_18);
x_20 = l_Lake_PackageEntry_setConfigFile(x_16, x_19);
x_21 = l_Lake_Manifest_addPackage(x_20, x_5);
x_3 = x_11;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_ctor_get(x_7, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 4);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lake_PackageEntry_setManifestFile(x_26, x_27);
x_29 = l_Lake_PackageEntry_setConfigFile(x_24, x_28);
x_30 = l_Lake_Manifest_addPackage(x_29, x_5);
x_3 = x_11;
x_5 = x_30;
goto _start;
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(x_9, x_2, x_3);
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
x_17 = l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(x_12, x_2, x_3);
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
x_24 = l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(x_19, x_2, x_3);
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
x_29 = l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(x_22, x_2, x_3);
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
x_38 = l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(x_33, x_2, x_3);
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
x_191 = l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(x_36, x_2, x_3);
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
x_347 = l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(x_342, x_2, x_3);
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
x_424 = l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(x_345, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_updateAndMaterialize___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lake_Workspace_updateAndMaterialize___spec__6(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_284; lean_object* x_285; lean_object* x_356; lean_object* x_357; lean_object* x_411; 
x_24 = lean_array_uget(x_8, x_7);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_uset(x_8, x_7, x_25);
x_126 = lean_ctor_get(x_24, 0);
lean_inc(x_126);
x_411 = l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__1(x_12, x_126);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; 
x_412 = l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__7(x_11, x_126);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_413 = lean_ctor_get(x_2, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_3, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_4, 1);
lean_inc(x_415);
x_416 = lean_ctor_get(x_1, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_416, 4);
lean_inc(x_417);
lean_dec(x_416);
x_418 = l_Lake_Dependency_materialize(x_24, x_5, x_413, x_414, x_415, x_417, x_14, x_15);
lean_dec(x_417);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; uint8_t x_421; 
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = !lean_is_exclusive(x_419);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_422 = lean_ctor_get(x_419, 0);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_11);
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_12);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_13);
lean_ctor_set(x_419, 0, x_425);
x_356 = x_419;
x_357 = x_420;
goto block_410;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_426 = lean_ctor_get(x_419, 0);
x_427 = lean_ctor_get(x_419, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_419);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_11);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_12);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_13);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_427);
x_356 = x_431;
x_357 = x_420;
goto block_410;
}
}
else
{
lean_object* x_432; uint8_t x_433; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_432 = lean_ctor_get(x_418, 1);
lean_inc(x_432);
lean_dec(x_418);
x_433 = !lean_is_exclusive(x_419);
if (x_433 == 0)
{
x_356 = x_419;
x_357 = x_432;
goto block_410;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_419, 0);
x_435 = lean_ctor_get(x_419, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_419);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
x_356 = x_436;
x_357 = x_432;
goto block_410;
}
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_437 = lean_ctor_get(x_412, 0);
lean_inc(x_437);
lean_dec(x_412);
x_438 = lean_ctor_get(x_2, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_3, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_1, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_440, 4);
lean_inc(x_441);
lean_dec(x_440);
x_442 = l_Lake_PackageEntry_materialize(x_437, x_24, x_438, x_439, x_441, x_14, x_15);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; uint8_t x_445; 
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = !lean_is_exclusive(x_443);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_446 = lean_ctor_get(x_443, 0);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_11);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_12);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_13);
lean_ctor_set(x_443, 0, x_449);
x_356 = x_443;
x_357 = x_444;
goto block_410;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_450 = lean_ctor_get(x_443, 0);
x_451 = lean_ctor_get(x_443, 1);
lean_inc(x_451);
lean_inc(x_450);
lean_dec(x_443);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_11);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_452);
lean_ctor_set(x_453, 1, x_12);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_13);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_451);
x_356 = x_455;
x_357 = x_444;
goto block_410;
}
}
else
{
lean_object* x_456; uint8_t x_457; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_456 = lean_ctor_get(x_442, 1);
lean_inc(x_456);
lean_dec(x_442);
x_457 = !lean_is_exclusive(x_443);
if (x_457 == 0)
{
x_356 = x_443;
x_357 = x_456;
goto block_410;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_443, 0);
x_459 = lean_ctor_get(x_443, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_443);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
x_356 = x_460;
x_357 = x_456;
goto block_410;
}
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_126);
lean_dec(x_24);
x_461 = lean_ctor_get(x_411, 0);
lean_inc(x_461);
lean_dec(x_411);
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_461);
x_463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_10);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_11);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_12);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_13);
x_467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_14);
x_27 = x_467;
x_28 = x_15;
goto block_125;
}
block_125:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_29, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_32, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_28);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_32, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_27);
lean_ctor_set(x_48, 1, x_28);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_dec(x_32);
x_50 = lean_ctor_get(x_33, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_51 = x_33;
} else {
 lean_dec_ref(x_33);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_31, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_27);
lean_ctor_set(x_54, 1, x_28);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_dec(x_31);
x_56 = lean_ctor_get(x_32, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_57 = x_32;
} else {
 lean_dec_ref(x_32);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_33, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_59 = x_33;
} else {
 lean_dec_ref(x_33);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
if (lean_is_scalar(x_57)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_57;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
lean_ctor_set(x_30, 0, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_27);
lean_ctor_set(x_63, 1, x_28);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_30, 1);
lean_inc(x_64);
lean_dec(x_30);
x_65 = lean_ctor_get(x_31, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_66 = x_31;
} else {
 lean_dec_ref(x_31);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_32, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_68 = x_32;
} else {
 lean_dec_ref(x_32);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_33, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_70 = x_33;
} else {
 lean_dec_ref(x_33);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_64);
lean_ctor_set(x_29, 0, x_74);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_27);
lean_ctor_set(x_75, 1, x_28);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_76 = lean_ctor_get(x_29, 1);
lean_inc(x_76);
lean_dec(x_29);
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
x_79 = lean_ctor_get(x_31, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_80 = x_31;
} else {
 lean_dec_ref(x_31);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_32, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_82 = x_32;
} else {
 lean_dec_ref(x_32);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_33, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_84 = x_33;
} else {
 lean_dec_ref(x_33);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_83);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
if (lean_is_scalar(x_80)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_80;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
if (lean_is_scalar(x_78)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_78;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_77);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_76);
lean_ctor_set(x_27, 0, x_89);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_27);
lean_ctor_set(x_90, 1, x_28);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_91 = lean_ctor_get(x_27, 1);
lean_inc(x_91);
lean_dec(x_27);
x_92 = lean_ctor_get(x_29, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_93 = x_29;
} else {
 lean_dec_ref(x_29);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_30, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_95 = x_30;
} else {
 lean_dec_ref(x_30);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_31, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_97 = x_31;
} else {
 lean_dec_ref(x_31);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_32, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_99 = x_32;
} else {
 lean_dec_ref(x_32);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_33, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_101 = x_33;
} else {
 lean_dec_ref(x_33);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
if (lean_is_scalar(x_99)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_99;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
if (lean_is_scalar(x_97)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_97;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_96);
if (lean_is_scalar(x_95)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_95;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_94);
if (lean_is_scalar(x_93)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_93;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_92);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_91);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_28);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; size_t x_115; size_t x_116; lean_object* x_117; 
x_109 = lean_ctor_get(x_27, 1);
lean_inc(x_109);
lean_dec(x_27);
x_110 = lean_ctor_get(x_29, 1);
lean_inc(x_110);
lean_dec(x_29);
x_111 = lean_ctor_get(x_30, 1);
lean_inc(x_111);
lean_dec(x_30);
x_112 = lean_ctor_get(x_31, 1);
lean_inc(x_112);
lean_dec(x_31);
x_113 = lean_ctor_get(x_32, 1);
lean_inc(x_113);
lean_dec(x_32);
x_114 = lean_ctor_get(x_33, 0);
lean_inc(x_114);
lean_dec(x_33);
x_115 = 1;
x_116 = lean_usize_add(x_7, x_115);
x_117 = lean_array_uset(x_26, x_7, x_114);
x_7 = x_116;
x_8 = x_117;
x_10 = x_113;
x_11 = x_112;
x_12 = x_111;
x_13 = x_110;
x_14 = x_109;
x_15 = x_28;
goto _start;
}
}
else
{
uint8_t x_119; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_27);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_27);
lean_ctor_set(x_120, 1, x_28);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_27, 0);
x_122 = lean_ctor_get(x_27, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_27);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_28);
return x_124;
}
}
}
block_283:
{
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
lean_dec(x_126);
x_134 = !lean_is_exclusive(x_127);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_127, 0);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_129);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_129, 0);
lean_dec(x_137);
x_138 = !lean_is_exclusive(x_130);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_130, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_131);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_131, 0);
lean_dec(x_141);
x_142 = !lean_is_exclusive(x_132);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_132, 0);
lean_dec(x_143);
x_144 = !lean_is_exclusive(x_133);
if (x_144 == 0)
{
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_133, 0);
lean_inc(x_145);
lean_dec(x_133);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_132, 0, x_146);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_132, 1);
lean_inc(x_147);
lean_dec(x_132);
x_148 = lean_ctor_get(x_133, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_149 = x_133;
} else {
 lean_dec_ref(x_133);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_147);
lean_ctor_set(x_131, 0, x_151);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_ctor_get(x_132, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_154 = x_132;
} else {
 lean_dec_ref(x_132);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_133, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_156 = x_133;
} else {
 lean_dec_ref(x_133);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 1, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
if (lean_is_scalar(x_154)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_154;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_153);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_152);
lean_ctor_set(x_130, 0, x_159);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_160 = lean_ctor_get(x_130, 1);
lean_inc(x_160);
lean_dec(x_130);
x_161 = lean_ctor_get(x_131, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_162 = x_131;
} else {
 lean_dec_ref(x_131);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_132, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_164 = x_132;
} else {
 lean_dec_ref(x_132);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_133, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_166 = x_133;
} else {
 lean_dec_ref(x_133);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 1, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_165);
if (lean_is_scalar(x_164)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_164;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_163);
if (lean_is_scalar(x_162)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_162;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_161);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_160);
lean_ctor_set(x_129, 0, x_170);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_171 = lean_ctor_get(x_129, 1);
lean_inc(x_171);
lean_dec(x_129);
x_172 = lean_ctor_get(x_130, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_173 = x_130;
} else {
 lean_dec_ref(x_130);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_131, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_175 = x_131;
} else {
 lean_dec_ref(x_131);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_132, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_177 = x_132;
} else {
 lean_dec_ref(x_132);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_133, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_179 = x_133;
} else {
 lean_dec_ref(x_133);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 1, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_178);
if (lean_is_scalar(x_177)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_177;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_176);
if (lean_is_scalar(x_175)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_175;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_174);
if (lean_is_scalar(x_173)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_173;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_172);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_171);
lean_ctor_set(x_127, 0, x_184);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_185 = lean_ctor_get(x_127, 1);
lean_inc(x_185);
lean_dec(x_127);
x_186 = lean_ctor_get(x_129, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_187 = x_129;
} else {
 lean_dec_ref(x_129);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_130, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_189 = x_130;
} else {
 lean_dec_ref(x_130);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_131, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_191 = x_131;
} else {
 lean_dec_ref(x_131);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_132, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_193 = x_132;
} else {
 lean_dec_ref(x_132);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_133, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_195 = x_133;
} else {
 lean_dec_ref(x_133);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 1, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_194);
if (lean_is_scalar(x_193)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_193;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_192);
if (lean_is_scalar(x_191)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_191;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_190);
if (lean_is_scalar(x_189)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_189;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_188);
if (lean_is_scalar(x_187)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_187;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_186);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_185);
x_27 = x_201;
x_28 = x_128;
goto block_125;
}
}
else
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_127);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_127, 0);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_129);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_129, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_130);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_207 = lean_ctor_get(x_130, 1);
x_208 = lean_ctor_get(x_130, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_131);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_131, 0);
lean_dec(x_210);
x_211 = !lean_is_exclusive(x_132);
if (x_211 == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_ctor_get(x_132, 0);
lean_dec(x_212);
x_213 = !lean_is_exclusive(x_133);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_133, 0);
lean_inc(x_214);
x_215 = l_Lean_RBNode_insert___at_Lake_Workspace_updateAndMaterialize___spec__5(x_207, x_126, x_214);
lean_ctor_set(x_130, 1, x_215);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_133, 0);
lean_inc(x_216);
lean_dec(x_133);
lean_inc(x_216);
x_217 = l_Lean_RBNode_insert___at_Lake_Workspace_updateAndMaterialize___spec__5(x_207, x_126, x_216);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_132, 0, x_218);
lean_ctor_set(x_130, 1, x_217);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_219 = lean_ctor_get(x_132, 1);
lean_inc(x_219);
lean_dec(x_132);
x_220 = lean_ctor_get(x_133, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_221 = x_133;
} else {
 lean_dec_ref(x_133);
 x_221 = lean_box(0);
}
lean_inc(x_220);
x_222 = l_Lean_RBNode_insert___at_Lake_Workspace_updateAndMaterialize___spec__5(x_207, x_126, x_220);
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_220);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_219);
lean_ctor_set(x_131, 0, x_224);
lean_ctor_set(x_130, 1, x_222);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_225 = lean_ctor_get(x_131, 1);
lean_inc(x_225);
lean_dec(x_131);
x_226 = lean_ctor_get(x_132, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_227 = x_132;
} else {
 lean_dec_ref(x_132);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_133, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_229 = x_133;
} else {
 lean_dec_ref(x_133);
 x_229 = lean_box(0);
}
lean_inc(x_228);
x_230 = l_Lean_RBNode_insert___at_Lake_Workspace_updateAndMaterialize___spec__5(x_207, x_126, x_228);
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_228);
if (lean_is_scalar(x_227)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_227;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_226);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_130, 1, x_230);
lean_ctor_set(x_130, 0, x_233);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_234 = lean_ctor_get(x_130, 1);
lean_inc(x_234);
lean_dec(x_130);
x_235 = lean_ctor_get(x_131, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_236 = x_131;
} else {
 lean_dec_ref(x_131);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_132, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_238 = x_132;
} else {
 lean_dec_ref(x_132);
 x_238 = lean_box(0);
}
x_239 = lean_ctor_get(x_133, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_240 = x_133;
} else {
 lean_dec_ref(x_133);
 x_240 = lean_box(0);
}
lean_inc(x_239);
x_241 = l_Lean_RBNode_insert___at_Lake_Workspace_updateAndMaterialize___spec__5(x_234, x_126, x_239);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_239);
if (lean_is_scalar(x_238)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_238;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_237);
if (lean_is_scalar(x_236)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_236;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_235);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_241);
lean_ctor_set(x_129, 0, x_245);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_246 = lean_ctor_get(x_129, 1);
lean_inc(x_246);
lean_dec(x_129);
x_247 = lean_ctor_get(x_130, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_248 = x_130;
} else {
 lean_dec_ref(x_130);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_131, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_250 = x_131;
} else {
 lean_dec_ref(x_131);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_132, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_252 = x_132;
} else {
 lean_dec_ref(x_132);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_133, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_254 = x_133;
} else {
 lean_dec_ref(x_133);
 x_254 = lean_box(0);
}
lean_inc(x_253);
x_255 = l_Lean_RBNode_insert___at_Lake_Workspace_updateAndMaterialize___spec__5(x_247, x_126, x_253);
if (lean_is_scalar(x_254)) {
 x_256 = lean_alloc_ctor(1, 1, 0);
} else {
 x_256 = x_254;
}
lean_ctor_set(x_256, 0, x_253);
if (lean_is_scalar(x_252)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_252;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_251);
if (lean_is_scalar(x_250)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_250;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_249);
if (lean_is_scalar(x_248)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_248;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_255);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_246);
lean_ctor_set(x_127, 0, x_260);
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_261 = lean_ctor_get(x_127, 1);
lean_inc(x_261);
lean_dec(x_127);
x_262 = lean_ctor_get(x_129, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_263 = x_129;
} else {
 lean_dec_ref(x_129);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_130, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_265 = x_130;
} else {
 lean_dec_ref(x_130);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_131, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_267 = x_131;
} else {
 lean_dec_ref(x_131);
 x_267 = lean_box(0);
}
x_268 = lean_ctor_get(x_132, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_269 = x_132;
} else {
 lean_dec_ref(x_132);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_133, 0);
lean_inc(x_270);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_271 = x_133;
} else {
 lean_dec_ref(x_133);
 x_271 = lean_box(0);
}
lean_inc(x_270);
x_272 = l_Lean_RBNode_insert___at_Lake_Workspace_updateAndMaterialize___spec__5(x_264, x_126, x_270);
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(1, 1, 0);
} else {
 x_273 = x_271;
}
lean_ctor_set(x_273, 0, x_270);
if (lean_is_scalar(x_269)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_269;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_268);
if (lean_is_scalar(x_267)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_267;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_266);
if (lean_is_scalar(x_265)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_265;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_272);
if (lean_is_scalar(x_263)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_263;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_262);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_261);
x_27 = x_278;
x_28 = x_128;
goto block_125;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_126);
x_279 = !lean_is_exclusive(x_127);
if (x_279 == 0)
{
x_27 = x_127;
x_28 = x_128;
goto block_125;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_127, 0);
x_281 = lean_ctor_get(x_127, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_127);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_27 = x_282;
x_28 = x_128;
goto block_125;
}
}
}
block_355:
{
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = !lean_is_exclusive(x_284);
if (x_290 == 0)
{
lean_object* x_291; uint8_t x_292; 
x_291 = lean_ctor_get(x_284, 0);
lean_dec(x_291);
x_292 = !lean_is_exclusive(x_286);
if (x_292 == 0)
{
lean_object* x_293; uint8_t x_294; 
x_293 = lean_ctor_get(x_286, 0);
lean_dec(x_293);
x_294 = !lean_is_exclusive(x_287);
if (x_294 == 0)
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_287, 0);
lean_dec(x_295);
x_296 = !lean_is_exclusive(x_288);
if (x_296 == 0)
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_ctor_get(x_288, 0);
lean_dec(x_297);
x_298 = !lean_is_exclusive(x_289);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_289, 0);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_289, 0, x_300);
x_127 = x_284;
x_128 = x_285;
goto block_283;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_289, 0);
x_302 = lean_ctor_get(x_289, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_289);
x_303 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_303, 0, x_301);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_302);
lean_ctor_set(x_288, 0, x_304);
x_127 = x_284;
x_128 = x_285;
goto block_283;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_305 = lean_ctor_get(x_288, 1);
lean_inc(x_305);
lean_dec(x_288);
x_306 = lean_ctor_get(x_289, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_289, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_308 = x_289;
} else {
 lean_dec_ref(x_289);
 x_308 = lean_box(0);
}
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_306);
if (lean_is_scalar(x_308)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_308;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_307);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_305);
lean_ctor_set(x_287, 0, x_311);
x_127 = x_284;
x_128 = x_285;
goto block_283;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_312 = lean_ctor_get(x_287, 1);
lean_inc(x_312);
lean_dec(x_287);
x_313 = lean_ctor_get(x_288, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_314 = x_288;
} else {
 lean_dec_ref(x_288);
 x_314 = lean_box(0);
}
x_315 = lean_ctor_get(x_289, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_289, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_317 = x_289;
} else {
 lean_dec_ref(x_289);
 x_317 = lean_box(0);
}
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_315);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_316);
if (lean_is_scalar(x_314)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_314;
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_313);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_312);
lean_ctor_set(x_286, 0, x_321);
x_127 = x_284;
x_128 = x_285;
goto block_283;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_322 = lean_ctor_get(x_286, 1);
lean_inc(x_322);
lean_dec(x_286);
x_323 = lean_ctor_get(x_287, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_324 = x_287;
} else {
 lean_dec_ref(x_287);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get(x_288, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_326 = x_288;
} else {
 lean_dec_ref(x_288);
 x_326 = lean_box(0);
}
x_327 = lean_ctor_get(x_289, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_289, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_329 = x_289;
} else {
 lean_dec_ref(x_289);
 x_329 = lean_box(0);
}
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_327);
if (lean_is_scalar(x_329)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_329;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_328);
if (lean_is_scalar(x_326)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_326;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_325);
if (lean_is_scalar(x_324)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_324;
}
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_323);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_322);
lean_ctor_set(x_284, 0, x_334);
x_127 = x_284;
x_128 = x_285;
goto block_283;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_335 = lean_ctor_get(x_284, 1);
lean_inc(x_335);
lean_dec(x_284);
x_336 = lean_ctor_get(x_286, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_337 = x_286;
} else {
 lean_dec_ref(x_286);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_287, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_339 = x_287;
} else {
 lean_dec_ref(x_287);
 x_339 = lean_box(0);
}
x_340 = lean_ctor_get(x_288, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_341 = x_288;
} else {
 lean_dec_ref(x_288);
 x_341 = lean_box(0);
}
x_342 = lean_ctor_get(x_289, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_289, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_344 = x_289;
} else {
 lean_dec_ref(x_289);
 x_344 = lean_box(0);
}
x_345 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_345, 0, x_342);
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_343);
if (lean_is_scalar(x_341)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_341;
}
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_340);
if (lean_is_scalar(x_339)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_339;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_338);
if (lean_is_scalar(x_337)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_337;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_336);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_335);
x_127 = x_350;
x_128 = x_285;
goto block_283;
}
}
else
{
uint8_t x_351; 
x_351 = !lean_is_exclusive(x_284);
if (x_351 == 0)
{
x_127 = x_284;
x_128 = x_285;
goto block_283;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_284, 0);
x_353 = lean_ctor_get(x_284, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_284);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
x_127 = x_354;
x_128 = x_285;
goto block_283;
}
}
}
block_410:
{
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; 
x_358 = lean_ctor_get(x_356, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = !lean_is_exclusive(x_356);
if (x_361 == 0)
{
lean_object* x_362; uint8_t x_363; 
x_362 = lean_ctor_get(x_356, 0);
lean_dec(x_362);
x_363 = !lean_is_exclusive(x_358);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_364 = lean_ctor_get(x_358, 1);
x_365 = lean_ctor_get(x_358, 0);
lean_dec(x_365);
x_366 = !lean_is_exclusive(x_359);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_367 = lean_ctor_get(x_359, 1);
x_368 = lean_ctor_get(x_359, 0);
lean_dec(x_368);
x_369 = !lean_is_exclusive(x_360);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_360, 1);
lean_ctor_set(x_360, 1, x_10);
lean_ctor_set(x_359, 1, x_370);
lean_ctor_set(x_358, 1, x_367);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_358);
lean_ctor_set(x_371, 1, x_364);
lean_ctor_set(x_356, 0, x_371);
x_284 = x_356;
x_285 = x_357;
goto block_355;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_372 = lean_ctor_get(x_360, 0);
x_373 = lean_ctor_get(x_360, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_360);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_10);
lean_ctor_set(x_359, 1, x_373);
lean_ctor_set(x_359, 0, x_374);
lean_ctor_set(x_358, 1, x_367);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_358);
lean_ctor_set(x_375, 1, x_364);
lean_ctor_set(x_356, 0, x_375);
x_284 = x_356;
x_285 = x_357;
goto block_355;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_376 = lean_ctor_get(x_359, 1);
lean_inc(x_376);
lean_dec(x_359);
x_377 = lean_ctor_get(x_360, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_360, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_379 = x_360;
} else {
 lean_dec_ref(x_360);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_10);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_378);
lean_ctor_set(x_358, 1, x_376);
lean_ctor_set(x_358, 0, x_381);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_358);
lean_ctor_set(x_382, 1, x_364);
lean_ctor_set(x_356, 0, x_382);
x_284 = x_356;
x_285 = x_357;
goto block_355;
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_383 = lean_ctor_get(x_358, 1);
lean_inc(x_383);
lean_dec(x_358);
x_384 = lean_ctor_get(x_359, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_385 = x_359;
} else {
 lean_dec_ref(x_359);
 x_385 = lean_box(0);
}
x_386 = lean_ctor_get(x_360, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_360, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_388 = x_360;
} else {
 lean_dec_ref(x_360);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_10);
if (lean_is_scalar(x_385)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_385;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_387);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_384);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_383);
lean_ctor_set(x_356, 0, x_392);
x_284 = x_356;
x_285 = x_357;
goto block_355;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_393 = lean_ctor_get(x_356, 1);
lean_inc(x_393);
lean_dec(x_356);
x_394 = lean_ctor_get(x_358, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_395 = x_358;
} else {
 lean_dec_ref(x_358);
 x_395 = lean_box(0);
}
x_396 = lean_ctor_get(x_359, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_397 = x_359;
} else {
 lean_dec_ref(x_359);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_360, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_360, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_400 = x_360;
} else {
 lean_dec_ref(x_360);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_10);
if (lean_is_scalar(x_397)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_397;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_399);
if (lean_is_scalar(x_395)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_395;
}
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_396);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_394);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_393);
x_284 = x_405;
x_285 = x_357;
goto block_355;
}
}
else
{
uint8_t x_406; 
lean_dec(x_10);
x_406 = !lean_is_exclusive(x_356);
if (x_406 == 0)
{
x_284 = x_356;
x_285 = x_357;
goto block_355;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_356, 0);
x_408 = lean_ctor_get(x_356, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_356);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
x_284 = x_409;
x_285 = x_357;
goto block_355;
}
}
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_30; 
x_30 = lean_usize_dec_eq(x_3, x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_52; 
lean_dec(x_5);
x_31 = lean_array_uget(x_2, x_3);
x_52 = lean_ctor_get(x_31, 0);
lean_inc(x_52);
x_32 = x_52;
goto block_51;
block_51:
{
uint8_t x_33; 
x_33 = l_Lean_NameMap_contains___rarg(x_8, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = l_Lake_PackageEntry_setInherited(x_31);
x_36 = l_Lake_PackageEntry_inDirectory(x_34, x_35);
x_37 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
x_40 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_39, x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_9);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_11);
x_13 = x_44;
x_14 = x_12;
goto block_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_31);
x_45 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_9);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_10);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_11);
x_13 = x_50;
x_14 = x_12;
goto block_29;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_5);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_7);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_8);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_9);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_10);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_11);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_12);
return x_59;
}
block_29:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
x_5 = x_25;
x_7 = x_24;
x_8 = x_23;
x_9 = x_22;
x_10 = x_21;
x_11 = x_20;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_2);
x_11 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_1, x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ignoring dependency manifest because it failed to load: ", 58);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ignoring missing dependency manifest '", 40);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_100; 
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
x_15 = l_System_FilePath_join(x_13, x_14);
x_100 = l_Lake_Manifest_load(x_15, x_12);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_101);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_7);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_8);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_9);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_10);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_11);
x_16 = x_109;
x_17 = x_102;
goto block_99;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_dec(x_100);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_110);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_7);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_8);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_9);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_10);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_11);
x_16 = x_118;
x_17 = x_111;
goto block_99;
}
block_99:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_3);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 11)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = 1;
x_33 = l_Lean_Name_toString(x_31, x_32);
x_34 = l_Lake_loadPackage___lambda__3___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_15);
lean_dec(x_15);
x_39 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
x_40 = lean_string_append(x_38, x_39);
x_41 = 2;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_push(x_25, x_42);
x_44 = lean_box(0);
x_45 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__1(x_2, x_1, x_44, x_6, x_29, x_28, x_27, x_26, x_43, x_17);
lean_dec(x_6);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_15);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_dec(x_16);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_dec(x_18);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_dec(x_19);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_dec(x_20);
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_dec(x_21);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
lean_dec(x_51);
x_53 = 1;
x_54 = l_Lean_Name_toString(x_52, x_53);
x_55 = l_Lake_loadPackage___lambda__3___closed__1;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_io_error_to_string(x_24);
x_60 = lean_string_append(x_58, x_59);
lean_dec(x_59);
x_61 = lean_string_append(x_60, x_55);
x_62 = 2;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_array_push(x_46, x_63);
x_65 = lean_box(0);
x_66 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__1(x_2, x_1, x_65, x_6, x_50, x_49, x_48, x_47, x_64, x_17);
lean_dec(x_6);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_15);
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
lean_dec(x_16);
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
lean_dec(x_18);
x_69 = lean_ctor_get(x_19, 1);
lean_inc(x_69);
lean_dec(x_19);
x_70 = lean_ctor_get(x_20, 1);
lean_inc(x_70);
lean_dec(x_20);
x_71 = lean_ctor_get(x_21, 1);
lean_inc(x_71);
lean_dec(x_21);
x_72 = lean_ctor_get(x_23, 0);
lean_inc(x_72);
lean_dec(x_23);
x_73 = lean_ctor_get(x_72, 3);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_array_get_size(x_73);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_lt(x_75, x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_3);
x_77 = lean_box(0);
x_78 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__1(x_2, x_1, x_77, x_6, x_71, x_70, x_69, x_68, x_67, x_17);
lean_dec(x_6);
return x_78;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_74, x_74);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_3);
x_80 = lean_box(0);
x_81 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__1(x_2, x_1, x_80, x_6, x_71, x_70, x_69, x_68, x_67, x_17);
lean_dec(x_6);
return x_81;
}
else
{
size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_82 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_83 = lean_box(0);
x_84 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9(x_3, x_73, x_4, x_82, x_83, x_6, x_71, x_70, x_69, x_68, x_67, x_17);
lean_dec(x_73);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_dec(x_85);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_dec(x_86);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
lean_dec(x_88);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_dec(x_89);
x_97 = lean_ctor_get(x_90, 0);
lean_inc(x_97);
lean_dec(x_90);
x_98 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__1(x_2, x_1, x_97, x_6, x_96, x_95, x_94, x_93, x_92, x_91);
lean_dec(x_6);
lean_dec(x_97);
return x_98;
}
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": package '", 11);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' was required as '", 19);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' was downloaded incorrectly; you will need to manually delete '", 64);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("': ", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_385; 
x_145 = lean_ctor_get(x_1, 0);
x_385 = l_IO_FS_removeDirAll(x_145, x_12);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_388, 0, x_386);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_7);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_8);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_9);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_10);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_11);
x_146 = x_393;
x_147 = x_387;
goto block_384;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_394 = lean_ctor_get(x_385, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_385, 1);
lean_inc(x_395);
lean_dec(x_385);
x_396 = lean_io_error_to_string(x_394);
x_397 = 3;
x_398 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set_uint8(x_398, sizeof(void*)*1, x_397);
x_399 = lean_array_get_size(x_11);
x_400 = lean_array_push(x_11, x_398);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
x_146 = x_401;
x_147 = x_395;
goto block_384;
}
block_144:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_16, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_18, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_14);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_18, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_14);
return x_34;
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
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_37 = x_19;
} else {
 lean_dec_ref(x_19);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_17, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_13);
lean_ctor_set(x_40, 1, x_14);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_43 = x_18;
} else {
 lean_dec_ref(x_18);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_45 = x_19;
} else {
 lean_dec_ref(x_19);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
lean_ctor_set(x_16, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_14);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
lean_dec(x_16);
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
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_54 = x_18;
} else {
 lean_dec_ref(x_18);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_19, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_56 = x_19;
} else {
 lean_dec_ref(x_19);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
lean_ctor_set(x_15, 0, x_60);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_13);
lean_ctor_set(x_61, 1, x_14);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_dec(x_15);
x_63 = lean_ctor_get(x_16, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_64 = x_16;
} else {
 lean_dec_ref(x_16);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_66 = x_17;
} else {
 lean_dec_ref(x_17);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_18, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_68 = x_18;
} else {
 lean_dec_ref(x_18);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_19, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_70 = x_19;
} else {
 lean_dec_ref(x_19);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
if (lean_is_scalar(x_64)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_64;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_63);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_62);
lean_ctor_set(x_13, 0, x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_13);
lean_ctor_set(x_76, 1, x_14);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_77 = lean_ctor_get(x_13, 1);
lean_inc(x_77);
lean_dec(x_13);
x_78 = lean_ctor_get(x_15, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_79 = x_15;
} else {
 lean_dec_ref(x_15);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_81 = x_16;
} else {
 lean_dec_ref(x_16);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_17, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_83 = x_17;
} else {
 lean_dec_ref(x_17);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_18, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_85 = x_18;
} else {
 lean_dec_ref(x_18);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_19, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_87 = x_19;
} else {
 lean_dec_ref(x_19);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 1, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
if (lean_is_scalar(x_83)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_83;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_82);
if (lean_is_scalar(x_81)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_81;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_79;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_78);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_77);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_14);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_95 = !lean_is_exclusive(x_13);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_96 = lean_ctor_get(x_13, 1);
x_97 = lean_ctor_get(x_13, 0);
lean_dec(x_97);
x_98 = 1;
x_99 = l_Lean_Name_toString(x_3, x_98);
x_100 = l_Lake_loadPackage___lambda__3___closed__1;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__1;
x_103 = lean_string_append(x_101, x_102);
x_104 = l_Lean_Name_toString(x_4, x_98);
x_105 = lean_string_append(x_103, x_104);
lean_dec(x_104);
x_106 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__2;
x_107 = lean_string_append(x_105, x_106);
x_108 = l_Lean_Name_toString(x_2, x_98);
x_109 = lean_string_append(x_107, x_108);
lean_dec(x_108);
x_110 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
x_111 = lean_string_append(x_109, x_110);
x_112 = 3;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
x_114 = lean_array_get_size(x_96);
x_115 = lean_array_push(x_96, x_113);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_115);
lean_ctor_set(x_13, 0, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_13);
lean_ctor_set(x_116, 1, x_14);
return x_116;
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_117 = lean_ctor_get(x_13, 1);
lean_inc(x_117);
lean_dec(x_13);
x_118 = 1;
x_119 = l_Lean_Name_toString(x_3, x_118);
x_120 = l_Lake_loadPackage___lambda__3___closed__1;
x_121 = lean_string_append(x_120, x_119);
lean_dec(x_119);
x_122 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__1;
x_123 = lean_string_append(x_121, x_122);
x_124 = l_Lean_Name_toString(x_4, x_118);
x_125 = lean_string_append(x_123, x_124);
lean_dec(x_124);
x_126 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__2;
x_127 = lean_string_append(x_125, x_126);
x_128 = l_Lean_Name_toString(x_2, x_118);
x_129 = lean_string_append(x_127, x_128);
lean_dec(x_128);
x_130 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
x_131 = lean_string_append(x_129, x_130);
x_132 = 3;
x_133 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_132);
x_134 = lean_array_get_size(x_117);
x_135 = lean_array_push(x_117, x_133);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_14);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_138 = !lean_is_exclusive(x_13);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_13);
lean_ctor_set(x_139, 1, x_14);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_13, 0);
x_141 = lean_ctor_get(x_13, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_13);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_14);
return x_143;
}
}
}
block_384:
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_146);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = lean_ctor_get(x_146, 1);
x_155 = lean_ctor_get(x_146, 0);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_148);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_148, 0);
lean_dec(x_157);
x_158 = !lean_is_exclusive(x_149);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_149, 0);
lean_dec(x_159);
x_160 = !lean_is_exclusive(x_150);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_150, 0);
lean_dec(x_161);
x_162 = !lean_is_exclusive(x_151);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_163 = lean_ctor_get(x_151, 0);
lean_dec(x_163);
x_164 = lean_ctor_get(x_152, 0);
lean_inc(x_164);
lean_dec(x_152);
x_165 = 1;
lean_inc(x_2);
x_166 = l_Lean_Name_toString(x_2, x_165);
x_167 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
x_168 = lean_string_append(x_167, x_166);
lean_dec(x_166);
x_169 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3;
x_170 = lean_string_append(x_168, x_169);
x_171 = lean_string_append(x_170, x_145);
x_172 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4;
x_173 = lean_string_append(x_171, x_172);
x_174 = l_List_toString___at_Lean_OpenDecl_instToString___spec__1(x_164);
x_175 = lean_string_append(x_173, x_174);
lean_dec(x_174);
x_176 = l_Lake_loadPackage___lambda__3___closed__1;
x_177 = lean_string_append(x_175, x_176);
x_178 = 3;
x_179 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set_uint8(x_179, sizeof(void*)*1, x_178);
x_180 = lean_array_push(x_154, x_179);
x_181 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1;
lean_ctor_set(x_151, 0, x_181);
lean_ctor_set(x_146, 1, x_180);
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_182 = lean_ctor_get(x_151, 1);
lean_inc(x_182);
lean_dec(x_151);
x_183 = lean_ctor_get(x_152, 0);
lean_inc(x_183);
lean_dec(x_152);
x_184 = 1;
lean_inc(x_2);
x_185 = l_Lean_Name_toString(x_2, x_184);
x_186 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
x_187 = lean_string_append(x_186, x_185);
lean_dec(x_185);
x_188 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3;
x_189 = lean_string_append(x_187, x_188);
x_190 = lean_string_append(x_189, x_145);
x_191 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4;
x_192 = lean_string_append(x_190, x_191);
x_193 = l_List_toString___at_Lean_OpenDecl_instToString___spec__1(x_183);
x_194 = lean_string_append(x_192, x_193);
lean_dec(x_193);
x_195 = l_Lake_loadPackage___lambda__3___closed__1;
x_196 = lean_string_append(x_194, x_195);
x_197 = 3;
x_198 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*1, x_197);
x_199 = lean_array_push(x_154, x_198);
x_200 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1;
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_182);
lean_ctor_set(x_150, 0, x_201);
lean_ctor_set(x_146, 1, x_199);
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_202 = lean_ctor_get(x_150, 1);
lean_inc(x_202);
lean_dec(x_150);
x_203 = lean_ctor_get(x_151, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_204 = x_151;
} else {
 lean_dec_ref(x_151);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_152, 0);
lean_inc(x_205);
lean_dec(x_152);
x_206 = 1;
lean_inc(x_2);
x_207 = l_Lean_Name_toString(x_2, x_206);
x_208 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
x_209 = lean_string_append(x_208, x_207);
lean_dec(x_207);
x_210 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3;
x_211 = lean_string_append(x_209, x_210);
x_212 = lean_string_append(x_211, x_145);
x_213 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4;
x_214 = lean_string_append(x_212, x_213);
x_215 = l_List_toString___at_Lean_OpenDecl_instToString___spec__1(x_205);
x_216 = lean_string_append(x_214, x_215);
lean_dec(x_215);
x_217 = l_Lake_loadPackage___lambda__3___closed__1;
x_218 = lean_string_append(x_216, x_217);
x_219 = 3;
x_220 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set_uint8(x_220, sizeof(void*)*1, x_219);
x_221 = lean_array_push(x_154, x_220);
x_222 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1;
if (lean_is_scalar(x_204)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_204;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_203);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_202);
lean_ctor_set(x_149, 0, x_224);
lean_ctor_set(x_146, 1, x_221);
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_225 = lean_ctor_get(x_149, 1);
lean_inc(x_225);
lean_dec(x_149);
x_226 = lean_ctor_get(x_150, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_227 = x_150;
} else {
 lean_dec_ref(x_150);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_151, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_229 = x_151;
} else {
 lean_dec_ref(x_151);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_152, 0);
lean_inc(x_230);
lean_dec(x_152);
x_231 = 1;
lean_inc(x_2);
x_232 = l_Lean_Name_toString(x_2, x_231);
x_233 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
x_234 = lean_string_append(x_233, x_232);
lean_dec(x_232);
x_235 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3;
x_236 = lean_string_append(x_234, x_235);
x_237 = lean_string_append(x_236, x_145);
x_238 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4;
x_239 = lean_string_append(x_237, x_238);
x_240 = l_List_toString___at_Lean_OpenDecl_instToString___spec__1(x_230);
x_241 = lean_string_append(x_239, x_240);
lean_dec(x_240);
x_242 = l_Lake_loadPackage___lambda__3___closed__1;
x_243 = lean_string_append(x_241, x_242);
x_244 = 3;
x_245 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set_uint8(x_245, sizeof(void*)*1, x_244);
x_246 = lean_array_push(x_154, x_245);
x_247 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1;
if (lean_is_scalar(x_229)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_229;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_228);
if (lean_is_scalar(x_227)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_227;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_226);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_225);
lean_ctor_set(x_148, 0, x_250);
lean_ctor_set(x_146, 1, x_246);
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_251 = lean_ctor_get(x_148, 1);
lean_inc(x_251);
lean_dec(x_148);
x_252 = lean_ctor_get(x_149, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_253 = x_149;
} else {
 lean_dec_ref(x_149);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_150, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_255 = x_150;
} else {
 lean_dec_ref(x_150);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_151, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_257 = x_151;
} else {
 lean_dec_ref(x_151);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_152, 0);
lean_inc(x_258);
lean_dec(x_152);
x_259 = 1;
lean_inc(x_2);
x_260 = l_Lean_Name_toString(x_2, x_259);
x_261 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
x_262 = lean_string_append(x_261, x_260);
lean_dec(x_260);
x_263 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3;
x_264 = lean_string_append(x_262, x_263);
x_265 = lean_string_append(x_264, x_145);
x_266 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4;
x_267 = lean_string_append(x_265, x_266);
x_268 = l_List_toString___at_Lean_OpenDecl_instToString___spec__1(x_258);
x_269 = lean_string_append(x_267, x_268);
lean_dec(x_268);
x_270 = l_Lake_loadPackage___lambda__3___closed__1;
x_271 = lean_string_append(x_269, x_270);
x_272 = 3;
x_273 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set_uint8(x_273, sizeof(void*)*1, x_272);
x_274 = lean_array_push(x_154, x_273);
x_275 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1;
if (lean_is_scalar(x_257)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_257;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_256);
if (lean_is_scalar(x_255)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_255;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_254);
if (lean_is_scalar(x_253)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_253;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_252);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_251);
lean_ctor_set(x_146, 1, x_274);
lean_ctor_set(x_146, 0, x_279);
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_280 = lean_ctor_get(x_146, 1);
lean_inc(x_280);
lean_dec(x_146);
x_281 = lean_ctor_get(x_148, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_282 = x_148;
} else {
 lean_dec_ref(x_148);
 x_282 = lean_box(0);
}
x_283 = lean_ctor_get(x_149, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_284 = x_149;
} else {
 lean_dec_ref(x_149);
 x_284 = lean_box(0);
}
x_285 = lean_ctor_get(x_150, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_286 = x_150;
} else {
 lean_dec_ref(x_150);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_151, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_288 = x_151;
} else {
 lean_dec_ref(x_151);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_152, 0);
lean_inc(x_289);
lean_dec(x_152);
x_290 = 1;
lean_inc(x_2);
x_291 = l_Lean_Name_toString(x_2, x_290);
x_292 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
x_293 = lean_string_append(x_292, x_291);
lean_dec(x_291);
x_294 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3;
x_295 = lean_string_append(x_293, x_294);
x_296 = lean_string_append(x_295, x_145);
x_297 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4;
x_298 = lean_string_append(x_296, x_297);
x_299 = l_List_toString___at_Lean_OpenDecl_instToString___spec__1(x_289);
x_300 = lean_string_append(x_298, x_299);
lean_dec(x_299);
x_301 = l_Lake_loadPackage___lambda__3___closed__1;
x_302 = lean_string_append(x_300, x_301);
x_303 = 3;
x_304 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set_uint8(x_304, sizeof(void*)*1, x_303);
x_305 = lean_array_push(x_280, x_304);
x_306 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1;
if (lean_is_scalar(x_288)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_288;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_287);
if (lean_is_scalar(x_286)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_286;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_285);
if (lean_is_scalar(x_284)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_284;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_283);
if (lean_is_scalar(x_282)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_282;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_281);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_305);
x_13 = x_311;
x_14 = x_147;
goto block_144;
}
}
else
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_146);
if (x_312 == 0)
{
lean_object* x_313; uint8_t x_314; 
x_313 = lean_ctor_get(x_146, 0);
lean_dec(x_313);
x_314 = !lean_is_exclusive(x_148);
if (x_314 == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_148, 0);
lean_dec(x_315);
x_316 = !lean_is_exclusive(x_149);
if (x_316 == 0)
{
lean_object* x_317; uint8_t x_318; 
x_317 = lean_ctor_get(x_149, 0);
lean_dec(x_317);
x_318 = !lean_is_exclusive(x_150);
if (x_318 == 0)
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_ctor_get(x_150, 0);
lean_dec(x_319);
x_320 = !lean_is_exclusive(x_151);
if (x_320 == 0)
{
lean_object* x_321; uint8_t x_322; 
x_321 = lean_ctor_get(x_151, 0);
lean_dec(x_321);
x_322 = !lean_is_exclusive(x_152);
if (x_322 == 0)
{
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
else
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_152, 0);
lean_inc(x_323);
lean_dec(x_152);
x_324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_151, 0, x_324);
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = lean_ctor_get(x_151, 1);
lean_inc(x_325);
lean_dec(x_151);
x_326 = lean_ctor_get(x_152, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_327 = x_152;
} else {
 lean_dec_ref(x_152);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 1, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_326);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_325);
lean_ctor_set(x_150, 0, x_329);
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_330 = lean_ctor_get(x_150, 1);
lean_inc(x_330);
lean_dec(x_150);
x_331 = lean_ctor_get(x_151, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_332 = x_151;
} else {
 lean_dec_ref(x_151);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_152, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_334 = x_152;
} else {
 lean_dec_ref(x_152);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 1, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_333);
if (lean_is_scalar(x_332)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_332;
}
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_331);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_330);
lean_ctor_set(x_149, 0, x_337);
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_338 = lean_ctor_get(x_149, 1);
lean_inc(x_338);
lean_dec(x_149);
x_339 = lean_ctor_get(x_150, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_340 = x_150;
} else {
 lean_dec_ref(x_150);
 x_340 = lean_box(0);
}
x_341 = lean_ctor_get(x_151, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_342 = x_151;
} else {
 lean_dec_ref(x_151);
 x_342 = lean_box(0);
}
x_343 = lean_ctor_get(x_152, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_344 = x_152;
} else {
 lean_dec_ref(x_152);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(1, 1, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_343);
if (lean_is_scalar(x_342)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_342;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_341);
if (lean_is_scalar(x_340)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_340;
}
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_339);
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_338);
lean_ctor_set(x_148, 0, x_348);
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_349 = lean_ctor_get(x_148, 1);
lean_inc(x_349);
lean_dec(x_148);
x_350 = lean_ctor_get(x_149, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_351 = x_149;
} else {
 lean_dec_ref(x_149);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_150, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_353 = x_150;
} else {
 lean_dec_ref(x_150);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_151, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_355 = x_151;
} else {
 lean_dec_ref(x_151);
 x_355 = lean_box(0);
}
x_356 = lean_ctor_get(x_152, 0);
lean_inc(x_356);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_357 = x_152;
} else {
 lean_dec_ref(x_152);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 1, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_356);
if (lean_is_scalar(x_355)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_355;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_354);
if (lean_is_scalar(x_353)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_353;
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_352);
if (lean_is_scalar(x_351)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_351;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_350);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_349);
lean_ctor_set(x_146, 0, x_362);
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_363 = lean_ctor_get(x_146, 1);
lean_inc(x_363);
lean_dec(x_146);
x_364 = lean_ctor_get(x_148, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_365 = x_148;
} else {
 lean_dec_ref(x_148);
 x_365 = lean_box(0);
}
x_366 = lean_ctor_get(x_149, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_367 = x_149;
} else {
 lean_dec_ref(x_149);
 x_367 = lean_box(0);
}
x_368 = lean_ctor_get(x_150, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_369 = x_150;
} else {
 lean_dec_ref(x_150);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_151, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_371 = x_151;
} else {
 lean_dec_ref(x_151);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_152, 0);
lean_inc(x_372);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_373 = x_152;
} else {
 lean_dec_ref(x_152);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 1, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_372);
if (lean_is_scalar(x_371)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_371;
}
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_370);
if (lean_is_scalar(x_369)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_369;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_368);
if (lean_is_scalar(x_367)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_367;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_366);
if (lean_is_scalar(x_365)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_365;
}
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_364);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_363);
x_13 = x_379;
x_14 = x_147;
goto block_144;
}
}
}
else
{
uint8_t x_380; 
x_380 = !lean_is_exclusive(x_146);
if (x_380 == 0)
{
x_13 = x_146;
x_14 = x_147;
goto block_144;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_146, 0);
x_382 = lean_ctor_get(x_146, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_146);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
x_13 = x_383;
x_14 = x_147;
goto block_144;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("std", 3);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" @ ", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_125; lean_object* x_570; lean_object* x_571; 
x_23 = lean_array_uget(x_7, x_6);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_uset(x_7, x_6, x_24);
x_570 = lean_ctor_get(x_23, 2);
lean_inc(x_570);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
lean_dec(x_570);
x_125 = x_571;
goto block_569;
block_124:
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_26, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_29, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_30, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_31, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_27);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_31, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_ctor_get(x_32, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_50 = x_32;
} else {
 lean_dec_ref(x_32);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_30, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_26);
lean_ctor_set(x_53, 1, x_27);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_dec(x_30);
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_56 = x_31;
} else {
 lean_dec_ref(x_31);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_32, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_58 = x_32;
} else {
 lean_dec_ref(x_32);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_54);
lean_ctor_set(x_29, 0, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_26);
lean_ctor_set(x_62, 1, x_27);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_29, 1);
lean_inc(x_63);
lean_dec(x_29);
x_64 = lean_ctor_get(x_30, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_65 = x_30;
} else {
 lean_dec_ref(x_30);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_31, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_67 = x_31;
} else {
 lean_dec_ref(x_31);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_32, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_69 = x_32;
} else {
 lean_dec_ref(x_32);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
if (lean_is_scalar(x_65)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_65;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_63);
lean_ctor_set(x_28, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_26);
lean_ctor_set(x_74, 1, x_27);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_75 = lean_ctor_get(x_28, 1);
lean_inc(x_75);
lean_dec(x_28);
x_76 = lean_ctor_get(x_29, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_77 = x_29;
} else {
 lean_dec_ref(x_29);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_30, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_79 = x_30;
} else {
 lean_dec_ref(x_30);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_31, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_81 = x_31;
} else {
 lean_dec_ref(x_31);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_32, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_83 = x_32;
} else {
 lean_dec_ref(x_32);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_79;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_77;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_75);
lean_ctor_set(x_26, 0, x_88);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_26);
lean_ctor_set(x_89, 1, x_27);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_90 = lean_ctor_get(x_26, 1);
lean_inc(x_90);
lean_dec(x_26);
x_91 = lean_ctor_get(x_28, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_92 = x_28;
} else {
 lean_dec_ref(x_28);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_29, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_94 = x_29;
} else {
 lean_dec_ref(x_29);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_30, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_96 = x_30;
} else {
 lean_dec_ref(x_30);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_31, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_98 = x_31;
} else {
 lean_dec_ref(x_31);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_32, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_100 = x_32;
} else {
 lean_dec_ref(x_32);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_99);
if (lean_is_scalar(x_98)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_98;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_97);
if (lean_is_scalar(x_96)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_96;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_95);
if (lean_is_scalar(x_94)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_94;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_93);
if (lean_is_scalar(x_92)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_92;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_91);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_90);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_27);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_26, 1);
lean_inc(x_108);
lean_dec(x_26);
x_109 = lean_ctor_get(x_28, 1);
lean_inc(x_109);
lean_dec(x_28);
x_110 = lean_ctor_get(x_29, 1);
lean_inc(x_110);
lean_dec(x_29);
x_111 = lean_ctor_get(x_30, 1);
lean_inc(x_111);
lean_dec(x_30);
x_112 = lean_ctor_get(x_31, 1);
lean_inc(x_112);
lean_dec(x_31);
x_113 = lean_ctor_get(x_32, 0);
lean_inc(x_113);
lean_dec(x_32);
x_114 = 1;
x_115 = lean_usize_add(x_6, x_114);
x_116 = lean_array_uset(x_25, x_6, x_113);
x_6 = x_115;
x_7 = x_116;
x_9 = x_112;
x_10 = x_111;
x_11 = x_110;
x_12 = x_109;
x_13 = x_108;
x_14 = x_27;
goto _start;
}
}
else
{
uint8_t x_118; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_26);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_26);
lean_ctor_set(x_119, 1, x_27);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_26, 0);
x_121 = lean_ctor_get(x_26, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_26);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_27);
return x_123;
}
}
}
block_569:
{
lean_object* x_126; lean_object* x_127; lean_object* x_251; lean_object* x_252; lean_object* x_411; lean_object* x_412; lean_object* x_483; lean_object* x_484; lean_object* x_538; 
x_538 = l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__10(x_9, x_125);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; 
lean_inc(x_12);
lean_inc(x_1);
lean_inc(x_23);
x_539 = l_Lake_loadDepPackage(x_23, x_1, x_2, x_12, x_13, x_14);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; uint8_t x_542; 
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_542 = !lean_is_exclusive(x_540);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_543 = lean_ctor_get(x_540, 0);
x_544 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_544, 0, x_543);
lean_ctor_set(x_544, 1, x_10);
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_11);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_12);
lean_ctor_set(x_540, 0, x_546);
x_483 = x_540;
x_484 = x_541;
goto block_537;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_547 = lean_ctor_get(x_540, 0);
x_548 = lean_ctor_get(x_540, 1);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_540);
x_549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_10);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_11);
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_12);
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_548);
x_483 = x_552;
x_484 = x_541;
goto block_537;
}
}
else
{
lean_object* x_553; uint8_t x_554; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_553 = lean_ctor_get(x_539, 1);
lean_inc(x_553);
lean_dec(x_539);
x_554 = !lean_is_exclusive(x_540);
if (x_554 == 0)
{
x_483 = x_540;
x_484 = x_553;
goto block_537;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_540, 0);
x_556 = lean_ctor_get(x_540, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_540);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
x_483 = x_557;
x_484 = x_553;
goto block_537;
}
}
}
else
{
uint8_t x_558; 
lean_dec(x_125);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_558 = !lean_is_exclusive(x_539);
if (x_558 == 0)
{
return x_539;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_539, 0);
x_560 = lean_ctor_get(x_539, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_539);
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_560);
return x_561;
}
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_125);
lean_dec(x_23);
x_562 = lean_ctor_get(x_538, 0);
lean_inc(x_562);
lean_dec(x_538);
x_563 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_563, 0, x_562);
x_564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_9);
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_10);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_11);
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_12);
x_568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_13);
x_26 = x_568;
x_27 = x_14;
goto block_124;
}
block_250:
{
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
lean_dec(x_125);
lean_dec(x_23);
x_133 = !lean_is_exclusive(x_126);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_126, 0);
lean_dec(x_134);
x_135 = !lean_is_exclusive(x_128);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_128, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_129);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_129, 0);
lean_dec(x_138);
x_139 = !lean_is_exclusive(x_130);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_130, 0);
lean_dec(x_140);
x_141 = !lean_is_exclusive(x_131);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_131, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_132);
if (x_143 == 0)
{
x_26 = x_126;
x_27 = x_127;
goto block_124;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_132, 0);
lean_inc(x_144);
lean_dec(x_132);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_131, 0, x_145);
x_26 = x_126;
x_27 = x_127;
goto block_124;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_131, 1);
lean_inc(x_146);
lean_dec(x_131);
x_147 = lean_ctor_get(x_132, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_148 = x_132;
} else {
 lean_dec_ref(x_132);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 1, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_147);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_146);
lean_ctor_set(x_130, 0, x_150);
x_26 = x_126;
x_27 = x_127;
goto block_124;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_151 = lean_ctor_get(x_130, 1);
lean_inc(x_151);
lean_dec(x_130);
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_153 = x_131;
} else {
 lean_dec_ref(x_131);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_132, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_155 = x_132;
} else {
 lean_dec_ref(x_132);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 1, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_151);
lean_ctor_set(x_129, 0, x_158);
x_26 = x_126;
x_27 = x_127;
goto block_124;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_159 = lean_ctor_get(x_129, 1);
lean_inc(x_159);
lean_dec(x_129);
x_160 = lean_ctor_get(x_130, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_161 = x_130;
} else {
 lean_dec_ref(x_130);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_131, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_163 = x_131;
} else {
 lean_dec_ref(x_131);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_132, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_165 = x_132;
} else {
 lean_dec_ref(x_132);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 1, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
if (lean_is_scalar(x_163)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_163;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_162);
if (lean_is_scalar(x_161)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_161;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_160);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_159);
lean_ctor_set(x_128, 0, x_169);
x_26 = x_126;
x_27 = x_127;
goto block_124;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_170 = lean_ctor_get(x_128, 1);
lean_inc(x_170);
lean_dec(x_128);
x_171 = lean_ctor_get(x_129, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_172 = x_129;
} else {
 lean_dec_ref(x_129);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_130, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_174 = x_130;
} else {
 lean_dec_ref(x_130);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_131, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_176 = x_131;
} else {
 lean_dec_ref(x_131);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_132, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_178 = x_132;
} else {
 lean_dec_ref(x_132);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 1, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_177);
if (lean_is_scalar(x_176)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_176;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_175);
if (lean_is_scalar(x_174)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_174;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_173);
if (lean_is_scalar(x_172)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_172;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_171);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_170);
lean_ctor_set(x_126, 0, x_183);
x_26 = x_126;
x_27 = x_127;
goto block_124;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_184 = lean_ctor_get(x_126, 1);
lean_inc(x_184);
lean_dec(x_126);
x_185 = lean_ctor_get(x_128, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_186 = x_128;
} else {
 lean_dec_ref(x_128);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_129, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_188 = x_129;
} else {
 lean_dec_ref(x_129);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_130, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_190 = x_130;
} else {
 lean_dec_ref(x_130);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_131, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_192 = x_131;
} else {
 lean_dec_ref(x_131);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_132, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_194 = x_132;
} else {
 lean_dec_ref(x_132);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 1, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
if (lean_is_scalar(x_192)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_192;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
if (lean_is_scalar(x_190)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_190;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_189);
if (lean_is_scalar(x_188)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_188;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_187);
if (lean_is_scalar(x_186)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_186;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_185);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_184);
x_26 = x_200;
x_27 = x_127;
goto block_124;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_210; 
x_201 = lean_ctor_get(x_126, 1);
lean_inc(x_201);
lean_dec(x_126);
x_202 = lean_ctor_get(x_128, 1);
lean_inc(x_202);
lean_dec(x_128);
x_203 = lean_ctor_get(x_129, 1);
lean_inc(x_203);
lean_dec(x_129);
x_204 = lean_ctor_get(x_130, 1);
lean_inc(x_204);
lean_dec(x_130);
x_205 = lean_ctor_get(x_131, 1);
lean_inc(x_205);
lean_dec(x_131);
x_206 = lean_ctor_get(x_132, 0);
lean_inc(x_206);
lean_dec(x_132);
x_207 = lean_ctor_get(x_206, 2);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 2);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_name_eq(x_208, x_125);
x_210 = l_instDecidableNot___rarg(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_208);
x_211 = lean_box(0);
lean_inc(x_8);
x_212 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2(x_206, x_125, x_23, x_4, x_211, x_8, x_205, x_204, x_203, x_202, x_201, x_127);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_26 = x_213;
x_27 = x_214;
goto block_124;
}
else
{
lean_object* x_215; uint8_t x_216; 
x_215 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__2;
x_216 = lean_name_eq(x_125, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_23);
x_217 = lean_box(0);
lean_inc(x_3);
x_218 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3(x_206, x_125, x_3, x_208, x_217, x_8, x_205, x_204, x_203, x_202, x_201, x_127);
lean_dec(x_206);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_26 = x_219;
x_27 = x_220;
goto block_124;
}
else
{
lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_23, 2);
lean_inc(x_221);
lean_dec(x_23);
x_222 = 1;
lean_inc(x_208);
x_223 = l_Lean_Name_toString(x_208, x_222);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_234; 
lean_dec(x_221);
x_234 = l_Lake_loadPackage___lambda__3___closed__1;
x_224 = x_234;
goto block_233;
}
else
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_221, 5);
lean_inc(x_235);
lean_dec(x_221);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = l_Lake_loadPackage___lambda__3___closed__1;
x_224 = x_236;
goto block_233;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
lean_dec(x_235);
x_238 = l_String_quote(x_237);
lean_dec(x_237);
x_239 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_240 = l_Std_Format_defWidth;
x_241 = lean_format_pretty(x_239, x_240, x_24, x_24);
x_242 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__3;
x_243 = lean_string_append(x_242, x_241);
lean_dec(x_241);
x_244 = l_Lake_loadPackage___lambda__3___closed__1;
x_245 = lean_string_append(x_243, x_244);
x_224 = x_245;
goto block_233;
}
}
block_233:
{
lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_225 = l_Lake_stdMismatchError(x_223, x_224);
lean_dec(x_224);
lean_dec(x_223);
x_226 = 3;
x_227 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set_uint8(x_227, sizeof(void*)*1, x_226);
x_228 = lean_array_push(x_201, x_227);
x_229 = lean_box(0);
lean_inc(x_3);
x_230 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3(x_206, x_125, x_3, x_208, x_229, x_8, x_205, x_204, x_203, x_202, x_228, x_127);
lean_dec(x_206);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_26 = x_231;
x_27 = x_232;
goto block_124;
}
}
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_125);
lean_dec(x_23);
x_246 = !lean_is_exclusive(x_126);
if (x_246 == 0)
{
x_26 = x_126;
x_27 = x_127;
goto block_124;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_126, 0);
x_248 = lean_ctor_get(x_126, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_126);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_26 = x_249;
x_27 = x_127;
goto block_124;
}
}
}
block_410:
{
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_251);
if (x_258 == 0)
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_ctor_get(x_251, 0);
lean_dec(x_259);
x_260 = !lean_is_exclusive(x_253);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_253, 0);
lean_dec(x_261);
x_262 = !lean_is_exclusive(x_254);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; 
x_263 = lean_ctor_get(x_254, 0);
lean_dec(x_263);
x_264 = !lean_is_exclusive(x_255);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_255, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_256);
if (x_266 == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_256, 0);
lean_dec(x_267);
x_268 = !lean_is_exclusive(x_257);
if (x_268 == 0)
{
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
else
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_257, 0);
lean_inc(x_269);
lean_dec(x_257);
x_270 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_256, 0, x_270);
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_271 = lean_ctor_get(x_256, 1);
lean_inc(x_271);
lean_dec(x_256);
x_272 = lean_ctor_get(x_257, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_273 = x_257;
} else {
 lean_dec_ref(x_257);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_271);
lean_ctor_set(x_255, 0, x_275);
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_276 = lean_ctor_get(x_255, 1);
lean_inc(x_276);
lean_dec(x_255);
x_277 = lean_ctor_get(x_256, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_278 = x_256;
} else {
 lean_dec_ref(x_256);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_257, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_280 = x_257;
} else {
 lean_dec_ref(x_257);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 1, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_279);
if (lean_is_scalar(x_278)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_278;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_277);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_276);
lean_ctor_set(x_254, 0, x_283);
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_284 = lean_ctor_get(x_254, 1);
lean_inc(x_284);
lean_dec(x_254);
x_285 = lean_ctor_get(x_255, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_286 = x_255;
} else {
 lean_dec_ref(x_255);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_256, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_288 = x_256;
} else {
 lean_dec_ref(x_256);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_257, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_290 = x_257;
} else {
 lean_dec_ref(x_257);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(0, 1, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_289);
if (lean_is_scalar(x_288)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_288;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_287);
if (lean_is_scalar(x_286)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_286;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_285);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_284);
lean_ctor_set(x_253, 0, x_294);
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_295 = lean_ctor_get(x_253, 1);
lean_inc(x_295);
lean_dec(x_253);
x_296 = lean_ctor_get(x_254, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_297 = x_254;
} else {
 lean_dec_ref(x_254);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_255, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_299 = x_255;
} else {
 lean_dec_ref(x_255);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_256, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_301 = x_256;
} else {
 lean_dec_ref(x_256);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_257, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_303 = x_257;
} else {
 lean_dec_ref(x_257);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(0, 1, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_302);
if (lean_is_scalar(x_301)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_301;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_300);
if (lean_is_scalar(x_299)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_299;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_298);
if (lean_is_scalar(x_297)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_297;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_296);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_295);
lean_ctor_set(x_251, 0, x_308);
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_309 = lean_ctor_get(x_251, 1);
lean_inc(x_309);
lean_dec(x_251);
x_310 = lean_ctor_get(x_253, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_311 = x_253;
} else {
 lean_dec_ref(x_253);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_254, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_313 = x_254;
} else {
 lean_dec_ref(x_254);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_255, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_315 = x_255;
} else {
 lean_dec_ref(x_255);
 x_315 = lean_box(0);
}
x_316 = lean_ctor_get(x_256, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_317 = x_256;
} else {
 lean_dec_ref(x_256);
 x_317 = lean_box(0);
}
x_318 = lean_ctor_get(x_257, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_319 = x_257;
} else {
 lean_dec_ref(x_257);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(0, 1, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_318);
if (lean_is_scalar(x_317)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_317;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_316);
if (lean_is_scalar(x_315)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_315;
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_314);
if (lean_is_scalar(x_313)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_313;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_312);
if (lean_is_scalar(x_311)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_311;
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_310);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_309);
x_126 = x_325;
x_127 = x_252;
goto block_250;
}
}
else
{
uint8_t x_326; 
lean_dec(x_253);
x_326 = !lean_is_exclusive(x_257);
if (x_326 == 0)
{
uint8_t x_327; 
x_327 = !lean_is_exclusive(x_251);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_328 = lean_ctor_get(x_257, 0);
x_329 = lean_ctor_get(x_251, 0);
lean_dec(x_329);
x_330 = !lean_is_exclusive(x_254);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_331 = lean_ctor_get(x_254, 1);
x_332 = lean_ctor_get(x_254, 0);
lean_dec(x_332);
x_333 = !lean_is_exclusive(x_255);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_334 = lean_ctor_get(x_255, 1);
x_335 = lean_ctor_get(x_255, 0);
lean_dec(x_335);
x_336 = !lean_is_exclusive(x_256);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_337 = lean_ctor_get(x_256, 1);
x_338 = lean_ctor_get(x_256, 0);
lean_dec(x_338);
x_339 = !lean_is_exclusive(x_328);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_328, 0);
x_341 = lean_ctor_get(x_328, 1);
lean_ctor_set(x_257, 0, x_340);
lean_ctor_set(x_328, 1, x_337);
lean_ctor_set(x_328, 0, x_257);
lean_ctor_set(x_256, 1, x_334);
lean_ctor_set(x_256, 0, x_328);
lean_ctor_set(x_255, 1, x_331);
lean_ctor_set(x_254, 1, x_341);
lean_ctor_set(x_251, 0, x_254);
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_328, 0);
x_343 = lean_ctor_get(x_328, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_328);
lean_ctor_set(x_257, 0, x_342);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_257);
lean_ctor_set(x_344, 1, x_337);
lean_ctor_set(x_256, 1, x_334);
lean_ctor_set(x_256, 0, x_344);
lean_ctor_set(x_255, 1, x_331);
lean_ctor_set(x_254, 1, x_343);
lean_ctor_set(x_251, 0, x_254);
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_345 = lean_ctor_get(x_256, 1);
lean_inc(x_345);
lean_dec(x_256);
x_346 = lean_ctor_get(x_328, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_328, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_348 = x_328;
} else {
 lean_dec_ref(x_328);
 x_348 = lean_box(0);
}
lean_ctor_set(x_257, 0, x_346);
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_257);
lean_ctor_set(x_349, 1, x_345);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_334);
lean_ctor_set(x_255, 1, x_331);
lean_ctor_set(x_255, 0, x_350);
lean_ctor_set(x_254, 1, x_347);
lean_ctor_set(x_251, 0, x_254);
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_351 = lean_ctor_get(x_255, 1);
lean_inc(x_351);
lean_dec(x_255);
x_352 = lean_ctor_get(x_256, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_353 = x_256;
} else {
 lean_dec_ref(x_256);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_328, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_328, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_356 = x_328;
} else {
 lean_dec_ref(x_328);
 x_356 = lean_box(0);
}
lean_ctor_set(x_257, 0, x_354);
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_257);
lean_ctor_set(x_357, 1, x_352);
if (lean_is_scalar(x_353)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_353;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_351);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_331);
lean_ctor_set(x_254, 1, x_355);
lean_ctor_set(x_254, 0, x_359);
lean_ctor_set(x_251, 0, x_254);
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_360 = lean_ctor_get(x_254, 1);
lean_inc(x_360);
lean_dec(x_254);
x_361 = lean_ctor_get(x_255, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_362 = x_255;
} else {
 lean_dec_ref(x_255);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_256, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_364 = x_256;
} else {
 lean_dec_ref(x_256);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_328, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_328, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_367 = x_328;
} else {
 lean_dec_ref(x_328);
 x_367 = lean_box(0);
}
lean_ctor_set(x_257, 0, x_365);
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_257);
lean_ctor_set(x_368, 1, x_363);
if (lean_is_scalar(x_364)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_364;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_361);
if (lean_is_scalar(x_362)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_362;
}
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_360);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_366);
lean_ctor_set(x_251, 0, x_371);
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_372 = lean_ctor_get(x_257, 0);
x_373 = lean_ctor_get(x_251, 1);
lean_inc(x_373);
lean_dec(x_251);
x_374 = lean_ctor_get(x_254, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_375 = x_254;
} else {
 lean_dec_ref(x_254);
 x_375 = lean_box(0);
}
x_376 = lean_ctor_get(x_255, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_377 = x_255;
} else {
 lean_dec_ref(x_255);
 x_377 = lean_box(0);
}
x_378 = lean_ctor_get(x_256, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_379 = x_256;
} else {
 lean_dec_ref(x_256);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_372, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_372, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_382 = x_372;
} else {
 lean_dec_ref(x_372);
 x_382 = lean_box(0);
}
lean_ctor_set(x_257, 0, x_380);
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_257);
lean_ctor_set(x_383, 1, x_378);
if (lean_is_scalar(x_379)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_379;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_376);
if (lean_is_scalar(x_377)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_377;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_374);
if (lean_is_scalar(x_375)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_375;
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_381);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_373);
x_126 = x_387;
x_127 = x_252;
goto block_250;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_388 = lean_ctor_get(x_257, 0);
lean_inc(x_388);
lean_dec(x_257);
x_389 = lean_ctor_get(x_251, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_390 = x_251;
} else {
 lean_dec_ref(x_251);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_254, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_392 = x_254;
} else {
 lean_dec_ref(x_254);
 x_392 = lean_box(0);
}
x_393 = lean_ctor_get(x_255, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_394 = x_255;
} else {
 lean_dec_ref(x_255);
 x_394 = lean_box(0);
}
x_395 = lean_ctor_get(x_256, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_396 = x_256;
} else {
 lean_dec_ref(x_256);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_388, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_388, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_399 = x_388;
} else {
 lean_dec_ref(x_388);
 x_399 = lean_box(0);
}
x_400 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_400, 0, x_397);
if (lean_is_scalar(x_399)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_399;
}
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_395);
if (lean_is_scalar(x_396)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_396;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_393);
if (lean_is_scalar(x_394)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_394;
}
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_391);
if (lean_is_scalar(x_392)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_392;
}
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_398);
if (lean_is_scalar(x_390)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_390;
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_389);
x_126 = x_405;
x_127 = x_252;
goto block_250;
}
}
}
else
{
uint8_t x_406; 
x_406 = !lean_is_exclusive(x_251);
if (x_406 == 0)
{
x_126 = x_251;
x_127 = x_252;
goto block_250;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_251, 0);
x_408 = lean_ctor_get(x_251, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_251);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
x_126 = x_409;
x_127 = x_252;
goto block_250;
}
}
}
block_482:
{
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_413 = lean_ctor_get(x_411, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = !lean_is_exclusive(x_411);
if (x_417 == 0)
{
lean_object* x_418; uint8_t x_419; 
x_418 = lean_ctor_get(x_411, 0);
lean_dec(x_418);
x_419 = !lean_is_exclusive(x_413);
if (x_419 == 0)
{
lean_object* x_420; uint8_t x_421; 
x_420 = lean_ctor_get(x_413, 0);
lean_dec(x_420);
x_421 = !lean_is_exclusive(x_414);
if (x_421 == 0)
{
lean_object* x_422; uint8_t x_423; 
x_422 = lean_ctor_get(x_414, 0);
lean_dec(x_422);
x_423 = !lean_is_exclusive(x_415);
if (x_423 == 0)
{
lean_object* x_424; uint8_t x_425; 
x_424 = lean_ctor_get(x_415, 0);
lean_dec(x_424);
x_425 = !lean_is_exclusive(x_416);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; 
x_426 = lean_ctor_get(x_416, 0);
x_427 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_416, 0, x_427);
x_251 = x_411;
x_252 = x_412;
goto block_410;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_428 = lean_ctor_get(x_416, 0);
x_429 = lean_ctor_get(x_416, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_416);
x_430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_430, 0, x_428);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_429);
lean_ctor_set(x_415, 0, x_431);
x_251 = x_411;
x_252 = x_412;
goto block_410;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_432 = lean_ctor_get(x_415, 1);
lean_inc(x_432);
lean_dec(x_415);
x_433 = lean_ctor_get(x_416, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_416, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_435 = x_416;
} else {
 lean_dec_ref(x_416);
 x_435 = lean_box(0);
}
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_433);
if (lean_is_scalar(x_435)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_435;
}
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_434);
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_432);
lean_ctor_set(x_414, 0, x_438);
x_251 = x_411;
x_252 = x_412;
goto block_410;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_439 = lean_ctor_get(x_414, 1);
lean_inc(x_439);
lean_dec(x_414);
x_440 = lean_ctor_get(x_415, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_441 = x_415;
} else {
 lean_dec_ref(x_415);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_416, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_416, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_444 = x_416;
} else {
 lean_dec_ref(x_416);
 x_444 = lean_box(0);
}
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_442);
if (lean_is_scalar(x_444)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_444;
}
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_443);
if (lean_is_scalar(x_441)) {
 x_447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_447 = x_441;
}
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_440);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_439);
lean_ctor_set(x_413, 0, x_448);
x_251 = x_411;
x_252 = x_412;
goto block_410;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_449 = lean_ctor_get(x_413, 1);
lean_inc(x_449);
lean_dec(x_413);
x_450 = lean_ctor_get(x_414, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_451 = x_414;
} else {
 lean_dec_ref(x_414);
 x_451 = lean_box(0);
}
x_452 = lean_ctor_get(x_415, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_453 = x_415;
} else {
 lean_dec_ref(x_415);
 x_453 = lean_box(0);
}
x_454 = lean_ctor_get(x_416, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_416, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_456 = x_416;
} else {
 lean_dec_ref(x_416);
 x_456 = lean_box(0);
}
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_454);
if (lean_is_scalar(x_456)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_456;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_455);
if (lean_is_scalar(x_453)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_453;
}
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_452);
if (lean_is_scalar(x_451)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_451;
}
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_450);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_449);
lean_ctor_set(x_411, 0, x_461);
x_251 = x_411;
x_252 = x_412;
goto block_410;
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_462 = lean_ctor_get(x_411, 1);
lean_inc(x_462);
lean_dec(x_411);
x_463 = lean_ctor_get(x_413, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_464 = x_413;
} else {
 lean_dec_ref(x_413);
 x_464 = lean_box(0);
}
x_465 = lean_ctor_get(x_414, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_466 = x_414;
} else {
 lean_dec_ref(x_414);
 x_466 = lean_box(0);
}
x_467 = lean_ctor_get(x_415, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_468 = x_415;
} else {
 lean_dec_ref(x_415);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_416, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_416, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_471 = x_416;
} else {
 lean_dec_ref(x_416);
 x_471 = lean_box(0);
}
x_472 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_472, 0, x_469);
if (lean_is_scalar(x_471)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_471;
}
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_470);
if (lean_is_scalar(x_468)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_468;
}
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_467);
if (lean_is_scalar(x_466)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_466;
}
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_465);
if (lean_is_scalar(x_464)) {
 x_476 = lean_alloc_ctor(0, 2, 0);
} else {
 x_476 = x_464;
}
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_463);
x_477 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_462);
x_251 = x_477;
x_252 = x_412;
goto block_410;
}
}
else
{
uint8_t x_478; 
x_478 = !lean_is_exclusive(x_411);
if (x_478 == 0)
{
x_251 = x_411;
x_252 = x_412;
goto block_410;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_411, 0);
x_480 = lean_ctor_get(x_411, 1);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_411);
x_481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
x_251 = x_481;
x_252 = x_412;
goto block_410;
}
}
}
block_537:
{
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; 
x_485 = lean_ctor_get(x_483, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = !lean_is_exclusive(x_483);
if (x_488 == 0)
{
lean_object* x_489; uint8_t x_490; 
x_489 = lean_ctor_get(x_483, 0);
lean_dec(x_489);
x_490 = !lean_is_exclusive(x_485);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_491 = lean_ctor_get(x_485, 1);
x_492 = lean_ctor_get(x_485, 0);
lean_dec(x_492);
x_493 = !lean_is_exclusive(x_486);
if (x_493 == 0)
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_494 = lean_ctor_get(x_486, 1);
x_495 = lean_ctor_get(x_486, 0);
lean_dec(x_495);
x_496 = !lean_is_exclusive(x_487);
if (x_496 == 0)
{
lean_object* x_497; lean_object* x_498; 
x_497 = lean_ctor_get(x_487, 1);
lean_ctor_set(x_487, 1, x_9);
lean_ctor_set(x_486, 1, x_497);
lean_ctor_set(x_485, 1, x_494);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_485);
lean_ctor_set(x_498, 1, x_491);
lean_ctor_set(x_483, 0, x_498);
x_411 = x_483;
x_412 = x_484;
goto block_482;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_499 = lean_ctor_get(x_487, 0);
x_500 = lean_ctor_get(x_487, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_487);
x_501 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_9);
lean_ctor_set(x_486, 1, x_500);
lean_ctor_set(x_486, 0, x_501);
lean_ctor_set(x_485, 1, x_494);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_485);
lean_ctor_set(x_502, 1, x_491);
lean_ctor_set(x_483, 0, x_502);
x_411 = x_483;
x_412 = x_484;
goto block_482;
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_503 = lean_ctor_get(x_486, 1);
lean_inc(x_503);
lean_dec(x_486);
x_504 = lean_ctor_get(x_487, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_487, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_506 = x_487;
} else {
 lean_dec_ref(x_487);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_9);
x_508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_505);
lean_ctor_set(x_485, 1, x_503);
lean_ctor_set(x_485, 0, x_508);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_485);
lean_ctor_set(x_509, 1, x_491);
lean_ctor_set(x_483, 0, x_509);
x_411 = x_483;
x_412 = x_484;
goto block_482;
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_510 = lean_ctor_get(x_485, 1);
lean_inc(x_510);
lean_dec(x_485);
x_511 = lean_ctor_get(x_486, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_512 = x_486;
} else {
 lean_dec_ref(x_486);
 x_512 = lean_box(0);
}
x_513 = lean_ctor_get(x_487, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_487, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_515 = x_487;
} else {
 lean_dec_ref(x_487);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(0, 2, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_9);
if (lean_is_scalar(x_512)) {
 x_517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_517 = x_512;
}
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_514);
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_511);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_510);
lean_ctor_set(x_483, 0, x_519);
x_411 = x_483;
x_412 = x_484;
goto block_482;
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_520 = lean_ctor_get(x_483, 1);
lean_inc(x_520);
lean_dec(x_483);
x_521 = lean_ctor_get(x_485, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_522 = x_485;
} else {
 lean_dec_ref(x_485);
 x_522 = lean_box(0);
}
x_523 = lean_ctor_get(x_486, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_524 = x_486;
} else {
 lean_dec_ref(x_486);
 x_524 = lean_box(0);
}
x_525 = lean_ctor_get(x_487, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_487, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_527 = x_487;
} else {
 lean_dec_ref(x_487);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_9);
if (lean_is_scalar(x_524)) {
 x_529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_529 = x_524;
}
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_526);
if (lean_is_scalar(x_522)) {
 x_530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_530 = x_522;
}
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_523);
x_531 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_521);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_520);
x_411 = x_532;
x_412 = x_484;
goto block_482;
}
}
else
{
uint8_t x_533; 
lean_dec(x_9);
x_533 = !lean_is_exclusive(x_483);
if (x_533 == 0)
{
x_411 = x_483;
x_412 = x_484;
goto block_482;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_483, 0);
x_535 = lean_ctor_get(x_483, 1);
lean_inc(x_535);
lean_inc(x_534);
lean_dec(x_483);
x_536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
x_411 = x_536;
x_412 = x_484;
goto block_482;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_122; 
x_20 = lean_array_uget(x_4, x_3);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_uset(x_4, x_3, x_21);
lean_inc(x_1);
lean_inc(x_5);
x_122 = lean_apply_8(x_1, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_122, 1);
lean_inc(x_129);
lean_dec(x_122);
x_130 = !lean_is_exclusive(x_123);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_123, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_124);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_124, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_125);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_125, 0);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_126);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_126, 0);
lean_dec(x_137);
x_138 = !lean_is_exclusive(x_127);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_127, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_128);
if (x_140 == 0)
{
x_23 = x_123;
x_24 = x_129;
goto block_121;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_128, 0);
lean_inc(x_141);
lean_dec(x_128);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_127, 0, x_142);
x_23 = x_123;
x_24 = x_129;
goto block_121;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_127, 1);
lean_inc(x_143);
lean_dec(x_127);
x_144 = lean_ctor_get(x_128, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_145 = x_128;
} else {
 lean_dec_ref(x_128);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 1, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_144);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_143);
lean_ctor_set(x_126, 0, x_147);
x_23 = x_123;
x_24 = x_129;
goto block_121;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_148 = lean_ctor_get(x_126, 1);
lean_inc(x_148);
lean_dec(x_126);
x_149 = lean_ctor_get(x_127, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_150 = x_127;
} else {
 lean_dec_ref(x_127);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_128, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_152 = x_128;
} else {
 lean_dec_ref(x_128);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_150;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_149);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_148);
lean_ctor_set(x_125, 0, x_155);
x_23 = x_123;
x_24 = x_129;
goto block_121;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_156 = lean_ctor_get(x_125, 1);
lean_inc(x_156);
lean_dec(x_125);
x_157 = lean_ctor_get(x_126, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_158 = x_126;
} else {
 lean_dec_ref(x_126);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_127, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_160 = x_127;
} else {
 lean_dec_ref(x_127);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_128, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_162 = x_128;
} else {
 lean_dec_ref(x_128);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 1, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_161);
if (lean_is_scalar(x_160)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_160;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_159);
if (lean_is_scalar(x_158)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_158;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_157);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_156);
lean_ctor_set(x_124, 0, x_166);
x_23 = x_123;
x_24 = x_129;
goto block_121;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_167 = lean_ctor_get(x_124, 1);
lean_inc(x_167);
lean_dec(x_124);
x_168 = lean_ctor_get(x_125, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_169 = x_125;
} else {
 lean_dec_ref(x_125);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_126, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_171 = x_126;
} else {
 lean_dec_ref(x_126);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_127, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_173 = x_127;
} else {
 lean_dec_ref(x_127);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_128, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_175 = x_128;
} else {
 lean_dec_ref(x_128);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 1, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
if (lean_is_scalar(x_173)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_173;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_172);
if (lean_is_scalar(x_171)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_171;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_170);
if (lean_is_scalar(x_169)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_169;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_168);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_167);
lean_ctor_set(x_123, 0, x_180);
x_23 = x_123;
x_24 = x_129;
goto block_121;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_181 = lean_ctor_get(x_123, 1);
lean_inc(x_181);
lean_dec(x_123);
x_182 = lean_ctor_get(x_124, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_183 = x_124;
} else {
 lean_dec_ref(x_124);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_125, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_185 = x_125;
} else {
 lean_dec_ref(x_125);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_126, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_187 = x_126;
} else {
 lean_dec_ref(x_126);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_127, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_189 = x_127;
} else {
 lean_dec_ref(x_127);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_128, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_191 = x_128;
} else {
 lean_dec_ref(x_128);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 1, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
if (lean_is_scalar(x_189)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_189;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_188);
if (lean_is_scalar(x_187)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_187;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_186);
if (lean_is_scalar(x_185)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_185;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_184);
if (lean_is_scalar(x_183)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_183;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_182);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_181);
x_23 = x_197;
x_24 = x_129;
goto block_121;
}
}
else
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_122, 1);
lean_inc(x_198);
lean_dec(x_122);
x_199 = !lean_is_exclusive(x_123);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_ctor_get(x_123, 0);
lean_dec(x_200);
x_201 = !lean_is_exclusive(x_124);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_124, 0);
lean_dec(x_202);
x_203 = !lean_is_exclusive(x_125);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_125, 0);
lean_dec(x_204);
x_205 = !lean_is_exclusive(x_126);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_ctor_get(x_126, 0);
lean_dec(x_206);
x_207 = !lean_is_exclusive(x_127);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_127, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_128);
if (x_209 == 0)
{
x_23 = x_123;
x_24 = x_198;
goto block_121;
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_128, 0);
lean_inc(x_210);
lean_dec(x_128);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_127, 0, x_211);
x_23 = x_123;
x_24 = x_198;
goto block_121;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_127, 1);
lean_inc(x_212);
lean_dec(x_127);
x_213 = lean_ctor_get(x_128, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_214 = x_128;
} else {
 lean_dec_ref(x_128);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_213);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_212);
lean_ctor_set(x_126, 0, x_216);
x_23 = x_123;
x_24 = x_198;
goto block_121;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_217 = lean_ctor_get(x_126, 1);
lean_inc(x_217);
lean_dec(x_126);
x_218 = lean_ctor_get(x_127, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_219 = x_127;
} else {
 lean_dec_ref(x_127);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_128, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_221 = x_128;
} else {
 lean_dec_ref(x_128);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 1, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_220);
if (lean_is_scalar(x_219)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_219;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_218);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_217);
lean_ctor_set(x_125, 0, x_224);
x_23 = x_123;
x_24 = x_198;
goto block_121;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_225 = lean_ctor_get(x_125, 1);
lean_inc(x_225);
lean_dec(x_125);
x_226 = lean_ctor_get(x_126, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_227 = x_126;
} else {
 lean_dec_ref(x_126);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_127, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_229 = x_127;
} else {
 lean_dec_ref(x_127);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_128, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_231 = x_128;
} else {
 lean_dec_ref(x_128);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_230);
if (lean_is_scalar(x_229)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_229;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_228);
if (lean_is_scalar(x_227)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_227;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_226);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_225);
lean_ctor_set(x_124, 0, x_235);
x_23 = x_123;
x_24 = x_198;
goto block_121;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_236 = lean_ctor_get(x_124, 1);
lean_inc(x_236);
lean_dec(x_124);
x_237 = lean_ctor_get(x_125, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_238 = x_125;
} else {
 lean_dec_ref(x_125);
 x_238 = lean_box(0);
}
x_239 = lean_ctor_get(x_126, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_240 = x_126;
} else {
 lean_dec_ref(x_126);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_127, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_242 = x_127;
} else {
 lean_dec_ref(x_127);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_128, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_244 = x_128;
} else {
 lean_dec_ref(x_128);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 1, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_243);
if (lean_is_scalar(x_242)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_242;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_241);
if (lean_is_scalar(x_240)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_240;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_239);
if (lean_is_scalar(x_238)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_238;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_237);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_236);
lean_ctor_set(x_123, 0, x_249);
x_23 = x_123;
x_24 = x_198;
goto block_121;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_250 = lean_ctor_get(x_123, 1);
lean_inc(x_250);
lean_dec(x_123);
x_251 = lean_ctor_get(x_124, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_252 = x_124;
} else {
 lean_dec_ref(x_124);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_125, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_254 = x_125;
} else {
 lean_dec_ref(x_125);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_126, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_256 = x_126;
} else {
 lean_dec_ref(x_126);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_127, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_258 = x_127;
} else {
 lean_dec_ref(x_127);
 x_258 = lean_box(0);
}
x_259 = lean_ctor_get(x_128, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_260 = x_128;
} else {
 lean_dec_ref(x_128);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 1, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_259);
if (lean_is_scalar(x_258)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_258;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_257);
if (lean_is_scalar(x_256)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_256;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_255);
if (lean_is_scalar(x_254)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_254;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_253);
if (lean_is_scalar(x_252)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_252;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_251);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_250);
x_23 = x_266;
x_24 = x_198;
goto block_121;
}
}
}
else
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_122, 1);
lean_inc(x_267);
lean_dec(x_122);
x_268 = !lean_is_exclusive(x_123);
if (x_268 == 0)
{
x_23 = x_123;
x_24 = x_267;
goto block_121;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_123, 0);
x_270 = lean_ctor_get(x_123, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_123);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_23 = x_271;
x_24 = x_267;
goto block_121;
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_1);
x_272 = !lean_is_exclusive(x_122);
if (x_272 == 0)
{
return x_122;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_122, 0);
x_274 = lean_ctor_get(x_122, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_122);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
block_121:
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_28, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_29);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_28, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_23);
lean_ctor_set(x_44, 1, x_24);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_dec(x_28);
x_46 = lean_ctor_get(x_29, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_47 = x_29;
} else {
 lean_dec_ref(x_29);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_27, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_23);
lean_ctor_set(x_50, 1, x_24);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_dec(x_27);
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_53 = x_28;
} else {
 lean_dec_ref(x_28);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_29, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_55 = x_29;
} else {
 lean_dec_ref(x_29);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_26, 0, x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_23);
lean_ctor_set(x_59, 1, x_24);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_60 = lean_ctor_get(x_26, 1);
lean_inc(x_60);
lean_dec(x_26);
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_62 = x_27;
} else {
 lean_dec_ref(x_27);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_28, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_64 = x_28;
} else {
 lean_dec_ref(x_28);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_29, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_66 = x_29;
} else {
 lean_dec_ref(x_29);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_62;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_61);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_60);
lean_ctor_set(x_25, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_23);
lean_ctor_set(x_71, 1, x_24);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_72 = lean_ctor_get(x_25, 1);
lean_inc(x_72);
lean_dec(x_25);
x_73 = lean_ctor_get(x_26, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_74 = x_26;
} else {
 lean_dec_ref(x_26);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_27, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_76 = x_27;
} else {
 lean_dec_ref(x_27);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_28, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_78 = x_28;
} else {
 lean_dec_ref(x_28);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_29, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_80 = x_29;
} else {
 lean_dec_ref(x_29);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_76;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
if (lean_is_scalar(x_74)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_74;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_73);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_72);
lean_ctor_set(x_23, 0, x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_23);
lean_ctor_set(x_86, 1, x_24);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_87 = lean_ctor_get(x_23, 1);
lean_inc(x_87);
lean_dec(x_23);
x_88 = lean_ctor_get(x_25, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_89 = x_25;
} else {
 lean_dec_ref(x_25);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_26, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_91 = x_26;
} else {
 lean_dec_ref(x_26);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_27, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_93 = x_27;
} else {
 lean_dec_ref(x_27);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_28, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_95 = x_28;
} else {
 lean_dec_ref(x_28);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_29, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_97 = x_29;
} else {
 lean_dec_ref(x_29);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 1, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_96);
if (lean_is_scalar(x_95)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_95;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
if (lean_is_scalar(x_93)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_93;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_90);
if (lean_is_scalar(x_89)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_89;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_88);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_87);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_24);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_23, 1);
lean_inc(x_105);
lean_dec(x_23);
x_106 = lean_ctor_get(x_25, 1);
lean_inc(x_106);
lean_dec(x_25);
x_107 = lean_ctor_get(x_26, 1);
lean_inc(x_107);
lean_dec(x_26);
x_108 = lean_ctor_get(x_27, 1);
lean_inc(x_108);
lean_dec(x_27);
x_109 = lean_ctor_get(x_28, 1);
lean_inc(x_109);
lean_dec(x_28);
x_110 = lean_ctor_get(x_29, 0);
lean_inc(x_110);
lean_dec(x_29);
x_111 = 1;
x_112 = lean_usize_add(x_3, x_111);
x_113 = lean_array_uset(x_22, x_3, x_110);
x_3 = x_112;
x_4 = x_113;
x_6 = x_109;
x_7 = x_108;
x_8 = x_107;
x_9 = x_106;
x_10 = x_105;
x_11 = x_24;
goto _start;
}
}
else
{
uint8_t x_115; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_23);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_23);
lean_ctor_set(x_116, 1, x_24);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_23, 0);
x_118 = lean_ctor_get(x_23, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_23);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_24);
return x_120;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_List_reverse___rarg(x_5);
x_8 = l_List_reverse___rarg(x_6);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = l_List_reverse___rarg(x_9);
x_12 = l_List_reverse___rarg(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_name_eq(x_16, x_1);
if (x_20 == 0)
{
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_3, 0, x_2);
x_2 = x_17;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_3, 1, x_2);
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_name_eq(x_23, x_1);
if (x_27 == 0)
{
lean_object* x_28; 
lean_ctor_set(x_2, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_26);
x_2 = x_24;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_30; 
lean_ctor_set(x_2, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_2);
x_2 = x_24;
x_3 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_36 = x_3;
} else {
 lean_dec_ref(x_3);
 x_36 = lean_box(0);
}
x_37 = lean_name_eq(x_32, x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_34);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
x_2 = x_33;
x_3 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_35);
if (lean_is_scalar(x_36)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_36;
}
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_41);
x_2 = x_33;
x_3 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__16___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__16(x_1, x_3, x_2, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_11, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
lean_inc(x_13);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__16___lambda__1), 10, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_apply_9(x_1, x_2, x_14, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3___closed__1;
x_18 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__15(x_11, x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_16);
x_22 = l_List_appendTR___rarg(x_20, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_updateAndMaterialize___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___at_Lake_Workspace_updateAndMaterialize___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__16(x_2, x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6(x_22, x_9);
x_24 = l_Lake_loadPackage___closed__2;
x_25 = l_String_intercalate(x_24, x_23);
x_26 = l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lake_loadPackage___lambda__3___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_get_size(x_20);
x_33 = lean_array_push(x_20, x_31);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_33);
lean_ctor_set(x_11, 0, x_32);
return x_10;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_dec(x_11);
x_35 = lean_ctor_get(x_16, 0);
lean_inc(x_35);
lean_dec(x_16);
x_36 = l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6(x_35, x_9);
x_37 = l_Lake_loadPackage___closed__2;
x_38 = l_String_intercalate(x_37, x_36);
x_39 = l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_Lake_loadPackage___lambda__3___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = 3;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_array_get_size(x_34);
x_46 = lean_array_push(x_34, x_44);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_10, 0, x_47);
return x_10;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_dec(x_10);
x_49 = lean_ctor_get(x_11, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_50 = x_11;
} else {
 lean_dec_ref(x_11);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_16, 0);
lean_inc(x_51);
lean_dec(x_16);
x_52 = l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6(x_51, x_9);
x_53 = l_Lake_loadPackage___closed__2;
x_54 = l_String_intercalate(x_53, x_52);
x_55 = l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Lake_loadPackage___lambda__3___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = 3;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_array_get_size(x_49);
x_62 = lean_array_push(x_49, x_60);
if (lean_is_scalar(x_50)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_50;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_48);
return x_64;
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_10);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_10, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_11);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_11, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_12);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_12, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_13);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_13, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_14);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_14, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_15);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_15, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_16, 0);
lean_inc(x_77);
lean_dec(x_16);
lean_ctor_set(x_15, 0, x_77);
return x_10;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_15, 1);
lean_inc(x_78);
lean_dec(x_15);
x_79 = lean_ctor_get(x_16, 0);
lean_inc(x_79);
lean_dec(x_16);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_14, 0, x_80);
return x_10;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_14, 1);
lean_inc(x_81);
lean_dec(x_14);
x_82 = lean_ctor_get(x_15, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_83 = x_15;
} else {
 lean_dec_ref(x_15);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_16, 0);
lean_inc(x_84);
lean_dec(x_16);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
lean_ctor_set(x_13, 0, x_86);
return x_10;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_13, 1);
lean_inc(x_87);
lean_dec(x_13);
x_88 = lean_ctor_get(x_14, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_89 = x_14;
} else {
 lean_dec_ref(x_14);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_15, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_91 = x_15;
} else {
 lean_dec_ref(x_15);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_16, 0);
lean_inc(x_92);
lean_dec(x_16);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
if (lean_is_scalar(x_89)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_89;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_88);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_87);
lean_ctor_set(x_12, 0, x_95);
return x_10;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_96 = lean_ctor_get(x_12, 1);
lean_inc(x_96);
lean_dec(x_12);
x_97 = lean_ctor_get(x_13, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_98 = x_13;
} else {
 lean_dec_ref(x_13);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_14, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_100 = x_14;
} else {
 lean_dec_ref(x_14);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_15, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_102 = x_15;
} else {
 lean_dec_ref(x_15);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_16, 0);
lean_inc(x_103);
lean_dec(x_16);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
if (lean_is_scalar(x_100)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_100;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_99);
if (lean_is_scalar(x_98)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_98;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_97);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_96);
lean_ctor_set(x_11, 0, x_107);
return x_10;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_108 = lean_ctor_get(x_11, 1);
lean_inc(x_108);
lean_dec(x_11);
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
x_111 = lean_ctor_get(x_13, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_112 = x_13;
} else {
 lean_dec_ref(x_13);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_14, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_114 = x_14;
} else {
 lean_dec_ref(x_14);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_15, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_116 = x_15;
} else {
 lean_dec_ref(x_15);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_16, 0);
lean_inc(x_117);
lean_dec(x_16);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
if (lean_is_scalar(x_114)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_114;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_113);
if (lean_is_scalar(x_112)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_112;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_111);
if (lean_is_scalar(x_110)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_110;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_109);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_108);
lean_ctor_set(x_10, 0, x_122);
return x_10;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_123 = lean_ctor_get(x_10, 1);
lean_inc(x_123);
lean_dec(x_10);
x_124 = lean_ctor_get(x_11, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_125 = x_11;
} else {
 lean_dec_ref(x_11);
 x_125 = lean_box(0);
}
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
x_128 = lean_ctor_get(x_13, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_129 = x_13;
} else {
 lean_dec_ref(x_13);
 x_129 = lean_box(0);
}
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
x_132 = lean_ctor_get(x_15, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_133 = x_15;
} else {
 lean_dec_ref(x_15);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_16, 0);
lean_inc(x_134);
lean_dec(x_16);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
if (lean_is_scalar(x_131)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_131;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_130);
if (lean_is_scalar(x_129)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_129;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_128);
if (lean_is_scalar(x_127)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_127;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_126);
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_124);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_123);
return x_140;
}
}
}
else
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_10);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_10, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_11);
if (x_143 == 0)
{
return x_10;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_11, 0);
x_145 = lean_ctor_get(x_11, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_11);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_10, 0, x_146);
return x_10;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_10, 1);
lean_inc(x_147);
lean_dec(x_10);
x_148 = lean_ctor_get(x_11, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_11, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_150 = x_11;
} else {
 lean_dec_ref(x_11);
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
x_153 = !lean_is_exclusive(x_10);
if (x_153 == 0)
{
return x_10;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_10, 0);
x_155 = lean_ctor_get(x_10, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_10);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__17(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_28; 
x_28 = lean_usize_dec_eq(x_3, x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
x_29 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_40; 
x_40 = lean_ctor_get_uint8(x_29, sizeof(void*)*4);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_29, 0);
lean_inc(x_41);
x_42 = l_Lean_NameSet_contains(x_1, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_30 = x_43;
goto block_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_29);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_6);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_9);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_10);
x_12 = x_49;
x_13 = x_11;
goto block_27;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_29);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_9);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_10);
x_12 = x_55;
x_13 = x_11;
goto block_27;
}
}
else
{
uint8_t x_56; 
x_56 = lean_ctor_get_uint8(x_29, sizeof(void*)*7);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_29, 0);
lean_inc(x_57);
x_58 = l_Lean_NameSet_contains(x_1, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_30 = x_59;
goto block_39;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_29);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_6);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_7);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_8);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_9);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_10);
x_12 = x_65;
x_13 = x_11;
goto block_27;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_29);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_6);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_7);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_8);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_9);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_10);
x_12 = x_71;
x_13 = x_11;
goto block_27;
}
}
block_39:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_30);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_31, x_29);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_8);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
x_12 = x_38;
x_13 = x_11;
goto block_27;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_5);
lean_ctor_set(x_72, 1, x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_7);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_8);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_10);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_11);
return x_77;
}
block_27:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_5 = x_22;
x_6 = x_23;
x_7 = x_21;
x_8 = x_20;
x_9 = x_19;
x_10 = x_18;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; size_t x_22; size_t x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
x_20 = lean_name_eq(x_19, x_2);
x_21 = lean_array_get_size(x_18);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
if (x_20 == 0)
{
uint8_t x_612; 
x_612 = 1;
x_24 = x_612;
goto block_611;
}
else
{
uint8_t x_613; 
x_613 = 0;
x_24 = x_613;
goto block_611;
}
block_611:
{
lean_object* x_25; lean_object* x_26; 
lean_inc(x_18);
lean_inc(x_1);
x_25 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8(x_3, x_4, x_5, x_1, x_24, x_22, x_23, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_28, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_29);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_29, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_30, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_31, 0);
lean_inc(x_45);
lean_dec(x_31);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_30, 0, x_46);
return x_25;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_dec(x_30);
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_49 = x_31;
} else {
 lean_dec_ref(x_31);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_29, 0, x_51);
return x_25;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_dec(x_29);
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
x_55 = lean_ctor_get(x_31, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_56 = x_31;
} else {
 lean_dec_ref(x_31);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
lean_ctor_set(x_28, 0, x_59);
return x_25;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_28, 1);
lean_inc(x_60);
lean_dec(x_28);
x_61 = lean_ctor_get(x_29, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_62 = x_29;
} else {
 lean_dec_ref(x_29);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_30, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_64 = x_30;
} else {
 lean_dec_ref(x_30);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_31, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_66 = x_31;
} else {
 lean_dec_ref(x_31);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_62;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_61);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_60);
lean_ctor_set(x_27, 0, x_70);
return x_25;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_71 = lean_ctor_get(x_27, 1);
lean_inc(x_71);
lean_dec(x_27);
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
x_76 = lean_ctor_get(x_30, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_77 = x_30;
} else {
 lean_dec_ref(x_30);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_31, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_79 = x_31;
} else {
 lean_dec_ref(x_31);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_77;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_75;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_74);
if (lean_is_scalar(x_73)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_73;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_72);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_71);
lean_ctor_set(x_26, 0, x_84);
return x_25;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_85 = lean_ctor_get(x_26, 1);
lean_inc(x_85);
lean_dec(x_26);
x_86 = lean_ctor_get(x_27, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_87 = x_27;
} else {
 lean_dec_ref(x_27);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_28, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_89 = x_28;
} else {
 lean_dec_ref(x_28);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_29, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_91 = x_29;
} else {
 lean_dec_ref(x_29);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_30, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_93 = x_30;
} else {
 lean_dec_ref(x_30);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_31, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_95 = x_31;
} else {
 lean_dec_ref(x_31);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 1, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
if (lean_is_scalar(x_93)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_93;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_92);
if (lean_is_scalar(x_91)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_91;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_90);
if (lean_is_scalar(x_89)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_89;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_88);
if (lean_is_scalar(x_87)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_87;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_86);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_85);
lean_ctor_set(x_25, 0, x_101);
return x_25;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_102 = lean_ctor_get(x_25, 1);
lean_inc(x_102);
lean_dec(x_25);
x_103 = lean_ctor_get(x_26, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_104 = x_26;
} else {
 lean_dec_ref(x_26);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_27, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_106 = x_27;
} else {
 lean_dec_ref(x_27);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_28, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_108 = x_28;
} else {
 lean_dec_ref(x_28);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_29, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_110 = x_29;
} else {
 lean_dec_ref(x_29);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_30, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_112 = x_30;
} else {
 lean_dec_ref(x_30);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_31, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_114 = x_31;
} else {
 lean_dec_ref(x_31);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 1, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
if (lean_is_scalar(x_110)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_110;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_109);
if (lean_is_scalar(x_108)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_108;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_107);
if (lean_is_scalar(x_106)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_106;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_105);
if (lean_is_scalar(x_104)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_104;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_103);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_102);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; size_t x_130; lean_object* x_131; 
x_122 = lean_ctor_get(x_25, 1);
lean_inc(x_122);
lean_dec(x_25);
x_123 = lean_ctor_get(x_26, 1);
lean_inc(x_123);
lean_dec(x_26);
x_124 = lean_ctor_get(x_27, 1);
lean_inc(x_124);
lean_dec(x_27);
x_125 = lean_ctor_get(x_28, 1);
lean_inc(x_125);
lean_dec(x_28);
x_126 = lean_ctor_get(x_29, 1);
lean_inc(x_126);
lean_dec(x_29);
x_127 = lean_ctor_get(x_30, 1);
lean_inc(x_127);
lean_dec(x_30);
x_128 = lean_ctor_get(x_31, 0);
lean_inc(x_128);
lean_dec(x_31);
x_129 = lean_array_get_size(x_128);
x_130 = lean_usize_of_nat(x_129);
lean_dec(x_129);
lean_inc(x_10);
x_131 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11(x_6, x_7, x_19, x_23, x_130, x_23, x_128, x_10, x_127, x_126, x_125, x_124, x_123, x_122);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_131);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_131, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_132);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_132, 0);
lean_dec(x_141);
x_142 = !lean_is_exclusive(x_133);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_133, 0);
lean_dec(x_143);
x_144 = !lean_is_exclusive(x_134);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_134, 0);
lean_dec(x_145);
x_146 = !lean_is_exclusive(x_135);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_135, 0);
lean_dec(x_147);
x_148 = !lean_is_exclusive(x_136);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_136, 0);
lean_dec(x_149);
x_150 = !lean_is_exclusive(x_137);
if (x_150 == 0)
{
return x_131;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_137, 0);
lean_inc(x_151);
lean_dec(x_137);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_136, 0, x_152);
return x_131;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_136, 1);
lean_inc(x_153);
lean_dec(x_136);
x_154 = lean_ctor_get(x_137, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_155 = x_137;
} else {
 lean_dec_ref(x_137);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 1, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_153);
lean_ctor_set(x_135, 0, x_157);
return x_131;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_158 = lean_ctor_get(x_135, 1);
lean_inc(x_158);
lean_dec(x_135);
x_159 = lean_ctor_get(x_136, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_160 = x_136;
} else {
 lean_dec_ref(x_136);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_137, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_162 = x_137;
} else {
 lean_dec_ref(x_137);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 1, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_161);
if (lean_is_scalar(x_160)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_160;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_159);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_158);
lean_ctor_set(x_134, 0, x_165);
return x_131;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_166 = lean_ctor_get(x_134, 1);
lean_inc(x_166);
lean_dec(x_134);
x_167 = lean_ctor_get(x_135, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_168 = x_135;
} else {
 lean_dec_ref(x_135);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_136, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_170 = x_136;
} else {
 lean_dec_ref(x_136);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_137, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_172 = x_137;
} else {
 lean_dec_ref(x_137);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 1, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_171);
if (lean_is_scalar(x_170)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_170;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_169);
if (lean_is_scalar(x_168)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_168;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_167);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_166);
lean_ctor_set(x_133, 0, x_176);
return x_131;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_177 = lean_ctor_get(x_133, 1);
lean_inc(x_177);
lean_dec(x_133);
x_178 = lean_ctor_get(x_134, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_179 = x_134;
} else {
 lean_dec_ref(x_134);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_135, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_181 = x_135;
} else {
 lean_dec_ref(x_135);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_136, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_183 = x_136;
} else {
 lean_dec_ref(x_136);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_137, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_185 = x_137;
} else {
 lean_dec_ref(x_137);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 1, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
if (lean_is_scalar(x_183)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_183;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_182);
if (lean_is_scalar(x_181)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_181;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_180);
if (lean_is_scalar(x_179)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_179;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_178);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_177);
lean_ctor_set(x_132, 0, x_190);
return x_131;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_191 = lean_ctor_get(x_132, 1);
lean_inc(x_191);
lean_dec(x_132);
x_192 = lean_ctor_get(x_133, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_193 = x_133;
} else {
 lean_dec_ref(x_133);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_134, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_195 = x_134;
} else {
 lean_dec_ref(x_134);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_135, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_197 = x_135;
} else {
 lean_dec_ref(x_135);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_136, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_199 = x_136;
} else {
 lean_dec_ref(x_136);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_137, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_201 = x_137;
} else {
 lean_dec_ref(x_137);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 1, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_200);
if (lean_is_scalar(x_199)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_199;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_198);
if (lean_is_scalar(x_197)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_197;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_196);
if (lean_is_scalar(x_195)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_195;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_194);
if (lean_is_scalar(x_193)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_193;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_192);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_191);
lean_ctor_set(x_131, 0, x_207);
return x_131;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_208 = lean_ctor_get(x_131, 1);
lean_inc(x_208);
lean_dec(x_131);
x_209 = lean_ctor_get(x_132, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_210 = x_132;
} else {
 lean_dec_ref(x_132);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_133, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_212 = x_133;
} else {
 lean_dec_ref(x_133);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_134, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_214 = x_134;
} else {
 lean_dec_ref(x_134);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_135, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_216 = x_135;
} else {
 lean_dec_ref(x_135);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_136, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_218 = x_136;
} else {
 lean_dec_ref(x_136);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_137, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_220 = x_137;
} else {
 lean_dec_ref(x_137);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 1, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_219);
if (lean_is_scalar(x_218)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_218;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_217);
if (lean_is_scalar(x_216)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_216;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_215);
if (lean_is_scalar(x_214)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_214;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_213);
if (lean_is_scalar(x_212)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_212;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_211);
if (lean_is_scalar(x_210)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_210;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_209);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_208);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; size_t x_236; lean_object* x_237; 
x_228 = lean_ctor_get(x_131, 1);
lean_inc(x_228);
lean_dec(x_131);
x_229 = lean_ctor_get(x_132, 1);
lean_inc(x_229);
lean_dec(x_132);
x_230 = lean_ctor_get(x_133, 1);
lean_inc(x_230);
lean_dec(x_133);
x_231 = lean_ctor_get(x_134, 1);
lean_inc(x_231);
lean_dec(x_134);
x_232 = lean_ctor_get(x_135, 1);
lean_inc(x_232);
lean_dec(x_135);
x_233 = lean_ctor_get(x_136, 1);
lean_inc(x_233);
lean_dec(x_136);
x_234 = lean_ctor_get(x_137, 0);
lean_inc(x_234);
lean_dec(x_137);
x_235 = lean_array_get_size(x_234);
x_236 = lean_usize_of_nat(x_235);
lean_dec(x_235);
x_237 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__12(x_8, x_236, x_23, x_234, x_10, x_233, x_232, x_231, x_230, x_229, x_228);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
if (lean_obj_tag(x_243) == 0)
{
uint8_t x_244; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_244 = !lean_is_exclusive(x_237);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_237, 0);
lean_dec(x_245);
x_246 = !lean_is_exclusive(x_238);
if (x_246 == 0)
{
lean_object* x_247; uint8_t x_248; 
x_247 = lean_ctor_get(x_238, 0);
lean_dec(x_247);
x_248 = !lean_is_exclusive(x_239);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; 
x_249 = lean_ctor_get(x_239, 0);
lean_dec(x_249);
x_250 = !lean_is_exclusive(x_240);
if (x_250 == 0)
{
lean_object* x_251; uint8_t x_252; 
x_251 = lean_ctor_get(x_240, 0);
lean_dec(x_251);
x_252 = !lean_is_exclusive(x_241);
if (x_252 == 0)
{
lean_object* x_253; uint8_t x_254; 
x_253 = lean_ctor_get(x_241, 0);
lean_dec(x_253);
x_254 = !lean_is_exclusive(x_242);
if (x_254 == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_242, 0);
lean_dec(x_255);
x_256 = !lean_is_exclusive(x_243);
if (x_256 == 0)
{
return x_237;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_243, 0);
lean_inc(x_257);
lean_dec(x_243);
x_258 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_242, 0, x_258);
return x_237;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_259 = lean_ctor_get(x_242, 1);
lean_inc(x_259);
lean_dec(x_242);
x_260 = lean_ctor_get(x_243, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_261 = x_243;
} else {
 lean_dec_ref(x_243);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(0, 1, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_260);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_259);
lean_ctor_set(x_241, 0, x_263);
return x_237;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_264 = lean_ctor_get(x_241, 1);
lean_inc(x_264);
lean_dec(x_241);
x_265 = lean_ctor_get(x_242, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_266 = x_242;
} else {
 lean_dec_ref(x_242);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_243, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_268 = x_243;
} else {
 lean_dec_ref(x_243);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 1, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_267);
if (lean_is_scalar(x_266)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_266;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_265);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_264);
lean_ctor_set(x_240, 0, x_271);
return x_237;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_272 = lean_ctor_get(x_240, 1);
lean_inc(x_272);
lean_dec(x_240);
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
x_275 = lean_ctor_get(x_242, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_276 = x_242;
} else {
 lean_dec_ref(x_242);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_243, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_278 = x_243;
} else {
 lean_dec_ref(x_243);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 1, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_277);
if (lean_is_scalar(x_276)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_276;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_275);
if (lean_is_scalar(x_274)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_274;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_273);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_272);
lean_ctor_set(x_239, 0, x_282);
return x_237;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_283 = lean_ctor_get(x_239, 1);
lean_inc(x_283);
lean_dec(x_239);
x_284 = lean_ctor_get(x_240, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_285 = x_240;
} else {
 lean_dec_ref(x_240);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_241, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_287 = x_241;
} else {
 lean_dec_ref(x_241);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get(x_242, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_289 = x_242;
} else {
 lean_dec_ref(x_242);
 x_289 = lean_box(0);
}
x_290 = lean_ctor_get(x_243, 0);
lean_inc(x_290);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_291 = x_243;
} else {
 lean_dec_ref(x_243);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 1, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_290);
if (lean_is_scalar(x_289)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_289;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_288);
if (lean_is_scalar(x_287)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_287;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_286);
if (lean_is_scalar(x_285)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_285;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_284);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_283);
lean_ctor_set(x_238, 0, x_296);
return x_237;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_297 = lean_ctor_get(x_238, 1);
lean_inc(x_297);
lean_dec(x_238);
x_298 = lean_ctor_get(x_239, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_299 = x_239;
} else {
 lean_dec_ref(x_239);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_240, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_301 = x_240;
} else {
 lean_dec_ref(x_240);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_241, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_303 = x_241;
} else {
 lean_dec_ref(x_241);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_242, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_305 = x_242;
} else {
 lean_dec_ref(x_242);
 x_305 = lean_box(0);
}
x_306 = lean_ctor_get(x_243, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_307 = x_243;
} else {
 lean_dec_ref(x_243);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(0, 1, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_306);
if (lean_is_scalar(x_305)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_305;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_304);
if (lean_is_scalar(x_303)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_303;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_302);
if (lean_is_scalar(x_301)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_301;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_300);
if (lean_is_scalar(x_299)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_299;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_298);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_297);
lean_ctor_set(x_237, 0, x_313);
return x_237;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_314 = lean_ctor_get(x_237, 1);
lean_inc(x_314);
lean_dec(x_237);
x_315 = lean_ctor_get(x_238, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_316 = x_238;
} else {
 lean_dec_ref(x_238);
 x_316 = lean_box(0);
}
x_317 = lean_ctor_get(x_239, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_318 = x_239;
} else {
 lean_dec_ref(x_239);
 x_318 = lean_box(0);
}
x_319 = lean_ctor_get(x_240, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_320 = x_240;
} else {
 lean_dec_ref(x_240);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_241, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_322 = x_241;
} else {
 lean_dec_ref(x_241);
 x_322 = lean_box(0);
}
x_323 = lean_ctor_get(x_242, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_324 = x_242;
} else {
 lean_dec_ref(x_242);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get(x_243, 0);
lean_inc(x_325);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_326 = x_243;
} else {
 lean_dec_ref(x_243);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(0, 1, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_325);
if (lean_is_scalar(x_324)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_324;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_323);
if (lean_is_scalar(x_322)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_322;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_321);
if (lean_is_scalar(x_320)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_320;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_319);
if (lean_is_scalar(x_318)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_318;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_317);
if (lean_is_scalar(x_316)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_316;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_315);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_314);
return x_333;
}
}
else
{
uint8_t x_334; 
x_334 = !lean_is_exclusive(x_237);
if (x_334 == 0)
{
lean_object* x_335; uint8_t x_336; 
x_335 = lean_ctor_get(x_237, 0);
lean_dec(x_335);
x_336 = !lean_is_exclusive(x_238);
if (x_336 == 0)
{
lean_object* x_337; uint8_t x_338; 
x_337 = lean_ctor_get(x_238, 0);
lean_dec(x_337);
x_338 = !lean_is_exclusive(x_239);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_239, 1);
x_340 = lean_ctor_get(x_239, 0);
lean_dec(x_340);
x_341 = !lean_is_exclusive(x_240);
if (x_341 == 0)
{
lean_object* x_342; uint8_t x_343; 
x_342 = lean_ctor_get(x_240, 0);
lean_dec(x_342);
x_343 = !lean_is_exclusive(x_241);
if (x_343 == 0)
{
lean_object* x_344; uint8_t x_345; 
x_344 = lean_ctor_get(x_241, 0);
lean_dec(x_344);
x_345 = !lean_is_exclusive(x_242);
if (x_345 == 0)
{
lean_object* x_346; uint8_t x_347; 
x_346 = lean_ctor_get(x_242, 0);
lean_dec(x_346);
x_347 = !lean_is_exclusive(x_243);
if (x_347 == 0)
{
uint8_t x_348; 
x_348 = !lean_is_exclusive(x_1);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_349 = lean_ctor_get(x_243, 0);
x_350 = lean_ctor_get(x_1, 7);
lean_dec(x_350);
x_351 = lean_ctor_get(x_1, 6);
lean_dec(x_351);
x_352 = lean_ctor_get(x_1, 2);
lean_dec(x_352);
lean_ctor_set(x_1, 6, x_349);
lean_inc(x_1);
x_353 = l_Lake_Workspace_addPackage(x_1, x_339);
lean_ctor_set(x_243, 0, x_1);
lean_ctor_set(x_239, 1, x_353);
return x_237;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_354 = lean_ctor_get(x_243, 0);
x_355 = lean_ctor_get(x_1, 0);
x_356 = lean_ctor_get(x_1, 1);
x_357 = lean_ctor_get(x_1, 3);
x_358 = lean_ctor_get(x_1, 4);
x_359 = lean_ctor_get(x_1, 5);
x_360 = lean_ctor_get(x_1, 8);
x_361 = lean_ctor_get(x_1, 9);
x_362 = lean_ctor_get(x_1, 10);
x_363 = lean_ctor_get(x_1, 11);
x_364 = lean_ctor_get(x_1, 12);
x_365 = lean_ctor_get(x_1, 13);
x_366 = lean_ctor_get(x_1, 14);
x_367 = lean_ctor_get(x_1, 15);
x_368 = lean_ctor_get(x_1, 16);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_1);
x_369 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_369, 0, x_355);
lean_ctor_set(x_369, 1, x_356);
lean_ctor_set(x_369, 2, x_17);
lean_ctor_set(x_369, 3, x_357);
lean_ctor_set(x_369, 4, x_358);
lean_ctor_set(x_369, 5, x_359);
lean_ctor_set(x_369, 6, x_354);
lean_ctor_set(x_369, 7, x_18);
lean_ctor_set(x_369, 8, x_360);
lean_ctor_set(x_369, 9, x_361);
lean_ctor_set(x_369, 10, x_362);
lean_ctor_set(x_369, 11, x_363);
lean_ctor_set(x_369, 12, x_364);
lean_ctor_set(x_369, 13, x_365);
lean_ctor_set(x_369, 14, x_366);
lean_ctor_set(x_369, 15, x_367);
lean_ctor_set(x_369, 16, x_368);
lean_inc(x_369);
x_370 = l_Lake_Workspace_addPackage(x_369, x_339);
lean_ctor_set(x_243, 0, x_369);
lean_ctor_set(x_239, 1, x_370);
return x_237;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_371 = lean_ctor_get(x_243, 0);
lean_inc(x_371);
lean_dec(x_243);
x_372 = lean_ctor_get(x_1, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_1, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_1, 3);
lean_inc(x_374);
x_375 = lean_ctor_get(x_1, 4);
lean_inc(x_375);
x_376 = lean_ctor_get(x_1, 5);
lean_inc(x_376);
x_377 = lean_ctor_get(x_1, 8);
lean_inc(x_377);
x_378 = lean_ctor_get(x_1, 9);
lean_inc(x_378);
x_379 = lean_ctor_get(x_1, 10);
lean_inc(x_379);
x_380 = lean_ctor_get(x_1, 11);
lean_inc(x_380);
x_381 = lean_ctor_get(x_1, 12);
lean_inc(x_381);
x_382 = lean_ctor_get(x_1, 13);
lean_inc(x_382);
x_383 = lean_ctor_get(x_1, 14);
lean_inc(x_383);
x_384 = lean_ctor_get(x_1, 15);
lean_inc(x_384);
x_385 = lean_ctor_get(x_1, 16);
lean_inc(x_385);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 lean_ctor_release(x_1, 11);
 lean_ctor_release(x_1, 12);
 lean_ctor_release(x_1, 13);
 lean_ctor_release(x_1, 14);
 lean_ctor_release(x_1, 15);
 lean_ctor_release(x_1, 16);
 x_386 = x_1;
} else {
 lean_dec_ref(x_1);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(0, 17, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_372);
lean_ctor_set(x_387, 1, x_373);
lean_ctor_set(x_387, 2, x_17);
lean_ctor_set(x_387, 3, x_374);
lean_ctor_set(x_387, 4, x_375);
lean_ctor_set(x_387, 5, x_376);
lean_ctor_set(x_387, 6, x_371);
lean_ctor_set(x_387, 7, x_18);
lean_ctor_set(x_387, 8, x_377);
lean_ctor_set(x_387, 9, x_378);
lean_ctor_set(x_387, 10, x_379);
lean_ctor_set(x_387, 11, x_380);
lean_ctor_set(x_387, 12, x_381);
lean_ctor_set(x_387, 13, x_382);
lean_ctor_set(x_387, 14, x_383);
lean_ctor_set(x_387, 15, x_384);
lean_ctor_set(x_387, 16, x_385);
lean_inc(x_387);
x_388 = l_Lake_Workspace_addPackage(x_387, x_339);
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_242, 0, x_389);
lean_ctor_set(x_239, 1, x_388);
return x_237;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_390 = lean_ctor_get(x_242, 1);
lean_inc(x_390);
lean_dec(x_242);
x_391 = lean_ctor_get(x_243, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_392 = x_243;
} else {
 lean_dec_ref(x_243);
 x_392 = lean_box(0);
}
x_393 = lean_ctor_get(x_1, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_1, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_1, 3);
lean_inc(x_395);
x_396 = lean_ctor_get(x_1, 4);
lean_inc(x_396);
x_397 = lean_ctor_get(x_1, 5);
lean_inc(x_397);
x_398 = lean_ctor_get(x_1, 8);
lean_inc(x_398);
x_399 = lean_ctor_get(x_1, 9);
lean_inc(x_399);
x_400 = lean_ctor_get(x_1, 10);
lean_inc(x_400);
x_401 = lean_ctor_get(x_1, 11);
lean_inc(x_401);
x_402 = lean_ctor_get(x_1, 12);
lean_inc(x_402);
x_403 = lean_ctor_get(x_1, 13);
lean_inc(x_403);
x_404 = lean_ctor_get(x_1, 14);
lean_inc(x_404);
x_405 = lean_ctor_get(x_1, 15);
lean_inc(x_405);
x_406 = lean_ctor_get(x_1, 16);
lean_inc(x_406);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 lean_ctor_release(x_1, 11);
 lean_ctor_release(x_1, 12);
 lean_ctor_release(x_1, 13);
 lean_ctor_release(x_1, 14);
 lean_ctor_release(x_1, 15);
 lean_ctor_release(x_1, 16);
 x_407 = x_1;
} else {
 lean_dec_ref(x_1);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(0, 17, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_393);
lean_ctor_set(x_408, 1, x_394);
lean_ctor_set(x_408, 2, x_17);
lean_ctor_set(x_408, 3, x_395);
lean_ctor_set(x_408, 4, x_396);
lean_ctor_set(x_408, 5, x_397);
lean_ctor_set(x_408, 6, x_391);
lean_ctor_set(x_408, 7, x_18);
lean_ctor_set(x_408, 8, x_398);
lean_ctor_set(x_408, 9, x_399);
lean_ctor_set(x_408, 10, x_400);
lean_ctor_set(x_408, 11, x_401);
lean_ctor_set(x_408, 12, x_402);
lean_ctor_set(x_408, 13, x_403);
lean_ctor_set(x_408, 14, x_404);
lean_ctor_set(x_408, 15, x_405);
lean_ctor_set(x_408, 16, x_406);
lean_inc(x_408);
x_409 = l_Lake_Workspace_addPackage(x_408, x_339);
if (lean_is_scalar(x_392)) {
 x_410 = lean_alloc_ctor(1, 1, 0);
} else {
 x_410 = x_392;
}
lean_ctor_set(x_410, 0, x_408);
x_411 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_390);
lean_ctor_set(x_241, 0, x_411);
lean_ctor_set(x_239, 1, x_409);
return x_237;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_412 = lean_ctor_get(x_241, 1);
lean_inc(x_412);
lean_dec(x_241);
x_413 = lean_ctor_get(x_242, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_414 = x_242;
} else {
 lean_dec_ref(x_242);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_243, 0);
lean_inc(x_415);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_416 = x_243;
} else {
 lean_dec_ref(x_243);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_1, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_1, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_1, 3);
lean_inc(x_419);
x_420 = lean_ctor_get(x_1, 4);
lean_inc(x_420);
x_421 = lean_ctor_get(x_1, 5);
lean_inc(x_421);
x_422 = lean_ctor_get(x_1, 8);
lean_inc(x_422);
x_423 = lean_ctor_get(x_1, 9);
lean_inc(x_423);
x_424 = lean_ctor_get(x_1, 10);
lean_inc(x_424);
x_425 = lean_ctor_get(x_1, 11);
lean_inc(x_425);
x_426 = lean_ctor_get(x_1, 12);
lean_inc(x_426);
x_427 = lean_ctor_get(x_1, 13);
lean_inc(x_427);
x_428 = lean_ctor_get(x_1, 14);
lean_inc(x_428);
x_429 = lean_ctor_get(x_1, 15);
lean_inc(x_429);
x_430 = lean_ctor_get(x_1, 16);
lean_inc(x_430);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 lean_ctor_release(x_1, 11);
 lean_ctor_release(x_1, 12);
 lean_ctor_release(x_1, 13);
 lean_ctor_release(x_1, 14);
 lean_ctor_release(x_1, 15);
 lean_ctor_release(x_1, 16);
 x_431 = x_1;
} else {
 lean_dec_ref(x_1);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(0, 17, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_417);
lean_ctor_set(x_432, 1, x_418);
lean_ctor_set(x_432, 2, x_17);
lean_ctor_set(x_432, 3, x_419);
lean_ctor_set(x_432, 4, x_420);
lean_ctor_set(x_432, 5, x_421);
lean_ctor_set(x_432, 6, x_415);
lean_ctor_set(x_432, 7, x_18);
lean_ctor_set(x_432, 8, x_422);
lean_ctor_set(x_432, 9, x_423);
lean_ctor_set(x_432, 10, x_424);
lean_ctor_set(x_432, 11, x_425);
lean_ctor_set(x_432, 12, x_426);
lean_ctor_set(x_432, 13, x_427);
lean_ctor_set(x_432, 14, x_428);
lean_ctor_set(x_432, 15, x_429);
lean_ctor_set(x_432, 16, x_430);
lean_inc(x_432);
x_433 = l_Lake_Workspace_addPackage(x_432, x_339);
if (lean_is_scalar(x_416)) {
 x_434 = lean_alloc_ctor(1, 1, 0);
} else {
 x_434 = x_416;
}
lean_ctor_set(x_434, 0, x_432);
if (lean_is_scalar(x_414)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_414;
}
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_413);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_412);
lean_ctor_set(x_240, 0, x_436);
lean_ctor_set(x_239, 1, x_433);
return x_237;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_437 = lean_ctor_get(x_240, 1);
lean_inc(x_437);
lean_dec(x_240);
x_438 = lean_ctor_get(x_241, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_439 = x_241;
} else {
 lean_dec_ref(x_241);
 x_439 = lean_box(0);
}
x_440 = lean_ctor_get(x_242, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_441 = x_242;
} else {
 lean_dec_ref(x_242);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_243, 0);
lean_inc(x_442);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_443 = x_243;
} else {
 lean_dec_ref(x_243);
 x_443 = lean_box(0);
}
x_444 = lean_ctor_get(x_1, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_1, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_1, 3);
lean_inc(x_446);
x_447 = lean_ctor_get(x_1, 4);
lean_inc(x_447);
x_448 = lean_ctor_get(x_1, 5);
lean_inc(x_448);
x_449 = lean_ctor_get(x_1, 8);
lean_inc(x_449);
x_450 = lean_ctor_get(x_1, 9);
lean_inc(x_450);
x_451 = lean_ctor_get(x_1, 10);
lean_inc(x_451);
x_452 = lean_ctor_get(x_1, 11);
lean_inc(x_452);
x_453 = lean_ctor_get(x_1, 12);
lean_inc(x_453);
x_454 = lean_ctor_get(x_1, 13);
lean_inc(x_454);
x_455 = lean_ctor_get(x_1, 14);
lean_inc(x_455);
x_456 = lean_ctor_get(x_1, 15);
lean_inc(x_456);
x_457 = lean_ctor_get(x_1, 16);
lean_inc(x_457);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 lean_ctor_release(x_1, 11);
 lean_ctor_release(x_1, 12);
 lean_ctor_release(x_1, 13);
 lean_ctor_release(x_1, 14);
 lean_ctor_release(x_1, 15);
 lean_ctor_release(x_1, 16);
 x_458 = x_1;
} else {
 lean_dec_ref(x_1);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(0, 17, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_444);
lean_ctor_set(x_459, 1, x_445);
lean_ctor_set(x_459, 2, x_17);
lean_ctor_set(x_459, 3, x_446);
lean_ctor_set(x_459, 4, x_447);
lean_ctor_set(x_459, 5, x_448);
lean_ctor_set(x_459, 6, x_442);
lean_ctor_set(x_459, 7, x_18);
lean_ctor_set(x_459, 8, x_449);
lean_ctor_set(x_459, 9, x_450);
lean_ctor_set(x_459, 10, x_451);
lean_ctor_set(x_459, 11, x_452);
lean_ctor_set(x_459, 12, x_453);
lean_ctor_set(x_459, 13, x_454);
lean_ctor_set(x_459, 14, x_455);
lean_ctor_set(x_459, 15, x_456);
lean_ctor_set(x_459, 16, x_457);
lean_inc(x_459);
x_460 = l_Lake_Workspace_addPackage(x_459, x_339);
if (lean_is_scalar(x_443)) {
 x_461 = lean_alloc_ctor(1, 1, 0);
} else {
 x_461 = x_443;
}
lean_ctor_set(x_461, 0, x_459);
if (lean_is_scalar(x_441)) {
 x_462 = lean_alloc_ctor(0, 2, 0);
} else {
 x_462 = x_441;
}
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_440);
if (lean_is_scalar(x_439)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_439;
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_438);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_437);
lean_ctor_set(x_239, 1, x_460);
lean_ctor_set(x_239, 0, x_464);
return x_237;
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_465 = lean_ctor_get(x_239, 1);
lean_inc(x_465);
lean_dec(x_239);
x_466 = lean_ctor_get(x_240, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_467 = x_240;
} else {
 lean_dec_ref(x_240);
 x_467 = lean_box(0);
}
x_468 = lean_ctor_get(x_241, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_469 = x_241;
} else {
 lean_dec_ref(x_241);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_242, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_471 = x_242;
} else {
 lean_dec_ref(x_242);
 x_471 = lean_box(0);
}
x_472 = lean_ctor_get(x_243, 0);
lean_inc(x_472);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_473 = x_243;
} else {
 lean_dec_ref(x_243);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_1, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_1, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_1, 3);
lean_inc(x_476);
x_477 = lean_ctor_get(x_1, 4);
lean_inc(x_477);
x_478 = lean_ctor_get(x_1, 5);
lean_inc(x_478);
x_479 = lean_ctor_get(x_1, 8);
lean_inc(x_479);
x_480 = lean_ctor_get(x_1, 9);
lean_inc(x_480);
x_481 = lean_ctor_get(x_1, 10);
lean_inc(x_481);
x_482 = lean_ctor_get(x_1, 11);
lean_inc(x_482);
x_483 = lean_ctor_get(x_1, 12);
lean_inc(x_483);
x_484 = lean_ctor_get(x_1, 13);
lean_inc(x_484);
x_485 = lean_ctor_get(x_1, 14);
lean_inc(x_485);
x_486 = lean_ctor_get(x_1, 15);
lean_inc(x_486);
x_487 = lean_ctor_get(x_1, 16);
lean_inc(x_487);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 lean_ctor_release(x_1, 11);
 lean_ctor_release(x_1, 12);
 lean_ctor_release(x_1, 13);
 lean_ctor_release(x_1, 14);
 lean_ctor_release(x_1, 15);
 lean_ctor_release(x_1, 16);
 x_488 = x_1;
} else {
 lean_dec_ref(x_1);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(0, 17, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_474);
lean_ctor_set(x_489, 1, x_475);
lean_ctor_set(x_489, 2, x_17);
lean_ctor_set(x_489, 3, x_476);
lean_ctor_set(x_489, 4, x_477);
lean_ctor_set(x_489, 5, x_478);
lean_ctor_set(x_489, 6, x_472);
lean_ctor_set(x_489, 7, x_18);
lean_ctor_set(x_489, 8, x_479);
lean_ctor_set(x_489, 9, x_480);
lean_ctor_set(x_489, 10, x_481);
lean_ctor_set(x_489, 11, x_482);
lean_ctor_set(x_489, 12, x_483);
lean_ctor_set(x_489, 13, x_484);
lean_ctor_set(x_489, 14, x_485);
lean_ctor_set(x_489, 15, x_486);
lean_ctor_set(x_489, 16, x_487);
lean_inc(x_489);
x_490 = l_Lake_Workspace_addPackage(x_489, x_465);
if (lean_is_scalar(x_473)) {
 x_491 = lean_alloc_ctor(1, 1, 0);
} else {
 x_491 = x_473;
}
lean_ctor_set(x_491, 0, x_489);
if (lean_is_scalar(x_471)) {
 x_492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_492 = x_471;
}
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_470);
if (lean_is_scalar(x_469)) {
 x_493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_493 = x_469;
}
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_468);
if (lean_is_scalar(x_467)) {
 x_494 = lean_alloc_ctor(0, 2, 0);
} else {
 x_494 = x_467;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_466);
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_490);
lean_ctor_set(x_238, 0, x_495);
return x_237;
}
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_496 = lean_ctor_get(x_238, 1);
lean_inc(x_496);
lean_dec(x_238);
x_497 = lean_ctor_get(x_239, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_498 = x_239;
} else {
 lean_dec_ref(x_239);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_240, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_500 = x_240;
} else {
 lean_dec_ref(x_240);
 x_500 = lean_box(0);
}
x_501 = lean_ctor_get(x_241, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_502 = x_241;
} else {
 lean_dec_ref(x_241);
 x_502 = lean_box(0);
}
x_503 = lean_ctor_get(x_242, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_504 = x_242;
} else {
 lean_dec_ref(x_242);
 x_504 = lean_box(0);
}
x_505 = lean_ctor_get(x_243, 0);
lean_inc(x_505);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_506 = x_243;
} else {
 lean_dec_ref(x_243);
 x_506 = lean_box(0);
}
x_507 = lean_ctor_get(x_1, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_1, 1);
lean_inc(x_508);
x_509 = lean_ctor_get(x_1, 3);
lean_inc(x_509);
x_510 = lean_ctor_get(x_1, 4);
lean_inc(x_510);
x_511 = lean_ctor_get(x_1, 5);
lean_inc(x_511);
x_512 = lean_ctor_get(x_1, 8);
lean_inc(x_512);
x_513 = lean_ctor_get(x_1, 9);
lean_inc(x_513);
x_514 = lean_ctor_get(x_1, 10);
lean_inc(x_514);
x_515 = lean_ctor_get(x_1, 11);
lean_inc(x_515);
x_516 = lean_ctor_get(x_1, 12);
lean_inc(x_516);
x_517 = lean_ctor_get(x_1, 13);
lean_inc(x_517);
x_518 = lean_ctor_get(x_1, 14);
lean_inc(x_518);
x_519 = lean_ctor_get(x_1, 15);
lean_inc(x_519);
x_520 = lean_ctor_get(x_1, 16);
lean_inc(x_520);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 lean_ctor_release(x_1, 11);
 lean_ctor_release(x_1, 12);
 lean_ctor_release(x_1, 13);
 lean_ctor_release(x_1, 14);
 lean_ctor_release(x_1, 15);
 lean_ctor_release(x_1, 16);
 x_521 = x_1;
} else {
 lean_dec_ref(x_1);
 x_521 = lean_box(0);
}
if (lean_is_scalar(x_521)) {
 x_522 = lean_alloc_ctor(0, 17, 0);
} else {
 x_522 = x_521;
}
lean_ctor_set(x_522, 0, x_507);
lean_ctor_set(x_522, 1, x_508);
lean_ctor_set(x_522, 2, x_17);
lean_ctor_set(x_522, 3, x_509);
lean_ctor_set(x_522, 4, x_510);
lean_ctor_set(x_522, 5, x_511);
lean_ctor_set(x_522, 6, x_505);
lean_ctor_set(x_522, 7, x_18);
lean_ctor_set(x_522, 8, x_512);
lean_ctor_set(x_522, 9, x_513);
lean_ctor_set(x_522, 10, x_514);
lean_ctor_set(x_522, 11, x_515);
lean_ctor_set(x_522, 12, x_516);
lean_ctor_set(x_522, 13, x_517);
lean_ctor_set(x_522, 14, x_518);
lean_ctor_set(x_522, 15, x_519);
lean_ctor_set(x_522, 16, x_520);
lean_inc(x_522);
x_523 = l_Lake_Workspace_addPackage(x_522, x_497);
if (lean_is_scalar(x_506)) {
 x_524 = lean_alloc_ctor(1, 1, 0);
} else {
 x_524 = x_506;
}
lean_ctor_set(x_524, 0, x_522);
if (lean_is_scalar(x_504)) {
 x_525 = lean_alloc_ctor(0, 2, 0);
} else {
 x_525 = x_504;
}
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_503);
if (lean_is_scalar(x_502)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_502;
}
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_501);
if (lean_is_scalar(x_500)) {
 x_527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_527 = x_500;
}
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_499);
if (lean_is_scalar(x_498)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_498;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_523);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_496);
lean_ctor_set(x_237, 0, x_529);
return x_237;
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_530 = lean_ctor_get(x_237, 1);
lean_inc(x_530);
lean_dec(x_237);
x_531 = lean_ctor_get(x_238, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_532 = x_238;
} else {
 lean_dec_ref(x_238);
 x_532 = lean_box(0);
}
x_533 = lean_ctor_get(x_239, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_534 = x_239;
} else {
 lean_dec_ref(x_239);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_240, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_536 = x_240;
} else {
 lean_dec_ref(x_240);
 x_536 = lean_box(0);
}
x_537 = lean_ctor_get(x_241, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_538 = x_241;
} else {
 lean_dec_ref(x_241);
 x_538 = lean_box(0);
}
x_539 = lean_ctor_get(x_242, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_540 = x_242;
} else {
 lean_dec_ref(x_242);
 x_540 = lean_box(0);
}
x_541 = lean_ctor_get(x_243, 0);
lean_inc(x_541);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_542 = x_243;
} else {
 lean_dec_ref(x_243);
 x_542 = lean_box(0);
}
x_543 = lean_ctor_get(x_1, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_1, 1);
lean_inc(x_544);
x_545 = lean_ctor_get(x_1, 3);
lean_inc(x_545);
x_546 = lean_ctor_get(x_1, 4);
lean_inc(x_546);
x_547 = lean_ctor_get(x_1, 5);
lean_inc(x_547);
x_548 = lean_ctor_get(x_1, 8);
lean_inc(x_548);
x_549 = lean_ctor_get(x_1, 9);
lean_inc(x_549);
x_550 = lean_ctor_get(x_1, 10);
lean_inc(x_550);
x_551 = lean_ctor_get(x_1, 11);
lean_inc(x_551);
x_552 = lean_ctor_get(x_1, 12);
lean_inc(x_552);
x_553 = lean_ctor_get(x_1, 13);
lean_inc(x_553);
x_554 = lean_ctor_get(x_1, 14);
lean_inc(x_554);
x_555 = lean_ctor_get(x_1, 15);
lean_inc(x_555);
x_556 = lean_ctor_get(x_1, 16);
lean_inc(x_556);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 lean_ctor_release(x_1, 8);
 lean_ctor_release(x_1, 9);
 lean_ctor_release(x_1, 10);
 lean_ctor_release(x_1, 11);
 lean_ctor_release(x_1, 12);
 lean_ctor_release(x_1, 13);
 lean_ctor_release(x_1, 14);
 lean_ctor_release(x_1, 15);
 lean_ctor_release(x_1, 16);
 x_557 = x_1;
} else {
 lean_dec_ref(x_1);
 x_557 = lean_box(0);
}
if (lean_is_scalar(x_557)) {
 x_558 = lean_alloc_ctor(0, 17, 0);
} else {
 x_558 = x_557;
}
lean_ctor_set(x_558, 0, x_543);
lean_ctor_set(x_558, 1, x_544);
lean_ctor_set(x_558, 2, x_17);
lean_ctor_set(x_558, 3, x_545);
lean_ctor_set(x_558, 4, x_546);
lean_ctor_set(x_558, 5, x_547);
lean_ctor_set(x_558, 6, x_541);
lean_ctor_set(x_558, 7, x_18);
lean_ctor_set(x_558, 8, x_548);
lean_ctor_set(x_558, 9, x_549);
lean_ctor_set(x_558, 10, x_550);
lean_ctor_set(x_558, 11, x_551);
lean_ctor_set(x_558, 12, x_552);
lean_ctor_set(x_558, 13, x_553);
lean_ctor_set(x_558, 14, x_554);
lean_ctor_set(x_558, 15, x_555);
lean_ctor_set(x_558, 16, x_556);
lean_inc(x_558);
x_559 = l_Lake_Workspace_addPackage(x_558, x_533);
if (lean_is_scalar(x_542)) {
 x_560 = lean_alloc_ctor(1, 1, 0);
} else {
 x_560 = x_542;
}
lean_ctor_set(x_560, 0, x_558);
if (lean_is_scalar(x_540)) {
 x_561 = lean_alloc_ctor(0, 2, 0);
} else {
 x_561 = x_540;
}
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_539);
if (lean_is_scalar(x_538)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_538;
}
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_537);
if (lean_is_scalar(x_536)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_536;
}
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_535);
if (lean_is_scalar(x_534)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_534;
}
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_559);
if (lean_is_scalar(x_532)) {
 x_565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_565 = x_532;
}
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_531);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_530);
return x_566;
}
}
}
else
{
uint8_t x_567; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_567 = !lean_is_exclusive(x_237);
if (x_567 == 0)
{
lean_object* x_568; uint8_t x_569; 
x_568 = lean_ctor_get(x_237, 0);
lean_dec(x_568);
x_569 = !lean_is_exclusive(x_238);
if (x_569 == 0)
{
return x_237;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_ctor_get(x_238, 0);
x_571 = lean_ctor_get(x_238, 1);
lean_inc(x_571);
lean_inc(x_570);
lean_dec(x_238);
x_572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_572, 0, x_570);
lean_ctor_set(x_572, 1, x_571);
lean_ctor_set(x_237, 0, x_572);
return x_237;
}
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_573 = lean_ctor_get(x_237, 1);
lean_inc(x_573);
lean_dec(x_237);
x_574 = lean_ctor_get(x_238, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_238, 1);
lean_inc(x_575);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_576 = x_238;
} else {
 lean_dec_ref(x_238);
 x_576 = lean_box(0);
}
if (lean_is_scalar(x_576)) {
 x_577 = lean_alloc_ctor(1, 2, 0);
} else {
 x_577 = x_576;
}
lean_ctor_set(x_577, 0, x_574);
lean_ctor_set(x_577, 1, x_575);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_573);
return x_578;
}
}
}
else
{
uint8_t x_579; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_579 = !lean_is_exclusive(x_237);
if (x_579 == 0)
{
return x_237;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_237, 0);
x_581 = lean_ctor_get(x_237, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_237);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
}
else
{
uint8_t x_583; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_131);
if (x_583 == 0)
{
lean_object* x_584; uint8_t x_585; 
x_584 = lean_ctor_get(x_131, 0);
lean_dec(x_584);
x_585 = !lean_is_exclusive(x_132);
if (x_585 == 0)
{
return x_131;
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_586 = lean_ctor_get(x_132, 0);
x_587 = lean_ctor_get(x_132, 1);
lean_inc(x_587);
lean_inc(x_586);
lean_dec(x_132);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_586);
lean_ctor_set(x_588, 1, x_587);
lean_ctor_set(x_131, 0, x_588);
return x_131;
}
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_589 = lean_ctor_get(x_131, 1);
lean_inc(x_589);
lean_dec(x_131);
x_590 = lean_ctor_get(x_132, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_132, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_592 = x_132;
} else {
 lean_dec_ref(x_132);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_590);
lean_ctor_set(x_593, 1, x_591);
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_589);
return x_594;
}
}
}
else
{
uint8_t x_595; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_595 = !lean_is_exclusive(x_131);
if (x_595 == 0)
{
return x_131;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_131, 0);
x_597 = lean_ctor_get(x_131, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_131);
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
return x_598;
}
}
}
}
else
{
uint8_t x_599; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_599 = !lean_is_exclusive(x_25);
if (x_599 == 0)
{
lean_object* x_600; uint8_t x_601; 
x_600 = lean_ctor_get(x_25, 0);
lean_dec(x_600);
x_601 = !lean_is_exclusive(x_26);
if (x_601 == 0)
{
return x_25;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_26, 0);
x_603 = lean_ctor_get(x_26, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_26);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
lean_ctor_set(x_25, 0, x_604);
return x_25;
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_605 = lean_ctor_get(x_25, 1);
lean_inc(x_605);
lean_dec(x_25);
x_606 = lean_ctor_get(x_26, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_26, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_608 = x_26;
} else {
 lean_dec_ref(x_26);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_609 = x_608;
}
lean_ctor_set(x_609, 0, x_606);
lean_ctor_set(x_609, 1, x_607);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_605);
return x_610;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_7, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_13, 3);
lean_inc(x_18);
x_19 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_18, x_17);
lean_dec(x_17);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lake_Workspace_updateAndMaterialize___lambda__1(x_7, x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_11);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_14);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_15);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_14 = lean_box(x_6);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterialize___lambda__2___boxed), 15, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_14);
x_16 = l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___at_Lake_Workspace_updateAndMaterialize___spec__13(x_3, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterialize___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ignoring previous manifest because it failed to load: ", 56);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = l_Lake_loadPackage___lambda__3___closed__1;
x_12 = lean_string_append(x_11, x_1);
x_13 = l_Lake_Workspace_updateAndMaterialize___lambda__4___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_io_error_to_string(x_2);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_11);
x_18 = 2;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_push(x_9, x_19);
x_21 = lean_box(0);
x_22 = lean_apply_7(x_3, x_21, x_5, x_6, x_7, x_8, x_20, x_10);
return x_22;
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("workspace packages directory changed; renaming '", 48);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' to '", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("could not rename workspace packages directory: ", 47);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_apply_7(x_2, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_15);
lean_inc(x_16);
x_17 = l_System_FilePath_join(x_16, x_15);
x_18 = l_System_FilePath_pathExists(x_17, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = l_System_FilePath_normalize(x_15);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
lean_inc(x_23);
x_24 = l_System_FilePath_normalize(x_23);
x_25 = lean_string_dec_eq(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_unbox(x_19);
lean_dec(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = lean_apply_7(x_2, x_27, x_6, x_7, x_8, x_9, x_10, x_20);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_74; 
x_29 = l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__1;
x_30 = lean_string_append(x_29, x_17);
x_31 = l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_System_FilePath_join(x_16, x_23);
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3;
x_36 = lean_string_append(x_34, x_35);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_push(x_10, x_38);
lean_inc(x_33);
x_74 = l_System_FilePath_parent(x_33);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_io_rename(x_17, x_33, x_20);
lean_dec(x_33);
lean_dec(x_17);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_39);
x_40 = x_79;
x_41 = x_77;
goto block_73;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_80);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_39);
x_40 = x_83;
x_41 = x_81;
goto block_73;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_74, 0);
lean_inc(x_84);
lean_dec(x_74);
x_85 = l_IO_FS_createDirAll(x_84, x_20);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_io_rename(x_17, x_33, x_86);
lean_dec(x_33);
lean_dec(x_17);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_39);
x_40 = x_91;
x_41 = x_89;
goto block_73;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_39);
x_40 = x_95;
x_41 = x_93;
goto block_73;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_33);
lean_dec(x_17);
x_96 = lean_ctor_get(x_85, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_85, 1);
lean_inc(x_97);
lean_dec(x_85);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_39);
x_40 = x_99;
x_41 = x_97;
goto block_73;
}
}
block_73:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_40, 1);
x_45 = lean_ctor_get(x_40, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_io_error_to_string(x_46);
x_48 = l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__3;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Lake_loadPackage___lambda__3___closed__1;
x_51 = lean_string_append(x_49, x_50);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_get_size(x_44);
x_55 = lean_array_push(x_44, x_53);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_55);
lean_ctor_set(x_40, 0, x_54);
if (lean_is_scalar(x_21)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_21;
}
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_41);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = lean_ctor_get(x_40, 1);
lean_inc(x_57);
lean_dec(x_40);
x_58 = lean_ctor_get(x_42, 0);
lean_inc(x_58);
lean_dec(x_42);
x_59 = lean_io_error_to_string(x_58);
x_60 = l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__3;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = l_Lake_loadPackage___lambda__3___closed__1;
x_63 = lean_string_append(x_61, x_62);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_57);
x_67 = lean_array_push(x_57, x_65);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_21)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_21;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_41);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_42);
lean_dec(x_21);
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_dec(x_40);
x_71 = lean_box(0);
x_72 = lean_apply_7(x_2, x_71, x_6, x_7, x_8, x_9, x_70, x_41);
return x_72;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
x_100 = lean_box(0);
x_101 = lean_apply_7(x_2, x_100, x_6, x_7, x_8, x_9, x_10, x_20);
return x_101;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterialize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": no previous manifest, creating one from scratch", 49);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_213; lean_object* x_214; lean_object* x_247; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_302 = lean_ctor_get(x_1, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_302, 2);
lean_inc(x_303);
x_304 = lean_ctor_get(x_303, 2);
lean_inc(x_304);
x_305 = 0;
lean_inc(x_304);
x_306 = l_Lean_Name_toString(x_304, x_305);
x_429 = lean_ctor_get(x_302, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_302, 4);
lean_inc(x_430);
x_431 = l_System_FilePath_join(x_429, x_430);
x_432 = lean_box(0);
x_433 = l_Lake_Manifest_load(x_431, x_6);
lean_dec(x_431);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_434);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_432);
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_432);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_432);
lean_inc(x_1);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_1);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_5);
x_307 = x_441;
x_308 = x_435;
goto block_428;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_442 = lean_ctor_get(x_433, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_433, 1);
lean_inc(x_443);
lean_dec(x_433);
x_444 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_444, 0, x_442);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_432);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_432);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_432);
lean_inc(x_1);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_1);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_5);
x_307 = x_449;
x_308 = x_443;
goto block_428;
}
block_212:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_13 = x_7;
} else {
 lean_dec_ref(x_7);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_ctor_set(x_11, 0, x_14);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = l_Lake_defaultLakeDir;
x_24 = l_Lake_loadLeanConfig___closed__1;
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_array_get_size(x_17);
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_dec_lt(x_106, x_26);
x_108 = lean_ctor_get(x_14, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_14, 4);
lean_inc(x_109);
lean_dec(x_14);
x_110 = l_System_FilePath_join(x_108, x_109);
if (x_107 == 0)
{
lean_dec(x_15);
x_111 = x_25;
goto block_124;
}
else
{
uint8_t x_125; 
x_125 = lean_nat_dec_le(x_26, x_26);
if (x_125 == 0)
{
lean_dec(x_15);
x_111 = x_25;
goto block_124;
}
else
{
size_t x_126; size_t x_127; lean_object* x_128; 
x_126 = 0;
x_127 = lean_usize_of_nat(x_26);
x_128 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__4(x_15, x_17, x_126, x_127, x_25);
lean_dec(x_15);
x_111 = x_128;
goto block_124;
}
}
block_105:
{
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_26);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_17);
lean_ctor_set(x_27, 0, x_11);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_26, x_26);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_26);
lean_dec(x_17);
lean_ctor_set(x_27, 0, x_11);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_27);
x_37 = 0;
x_38 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_39 = lean_box(0);
lean_inc(x_11);
x_40 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3(x_17, x_37, x_38, x_39, x_11, x_30, x_28);
lean_dec(x_17);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
lean_ctor_set(x_41, 0, x_11);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_40, 0, x_47);
return x_40;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_dec(x_40);
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
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_11);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_40, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
return x_40;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_41, 0);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_41);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_40, 0, x_58);
return x_40;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_40, 1);
lean_inc(x_59);
lean_dec(x_40);
x_60 = lean_ctor_get(x_41, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_41, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_62 = x_41;
} else {
 lean_dec_ref(x_41);
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
lean_dec(x_11);
x_65 = !lean_is_exclusive(x_40);
if (x_65 == 0)
{
return x_40;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_40, 0);
x_67 = lean_ctor_get(x_40, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_40);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_27, 1);
lean_inc(x_69);
lean_dec(x_27);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_lt(x_70, x_26);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_26);
lean_dec(x_17);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_11);
lean_ctor_set(x_72, 1, x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_28);
return x_73;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_le(x_26, x_26);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_26);
lean_dec(x_17);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_11);
lean_ctor_set(x_75, 1, x_69);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_28);
return x_76;
}
else
{
size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; 
x_77 = 0;
x_78 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_79 = lean_box(0);
lean_inc(x_11);
x_80 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3(x_17, x_77, x_78, x_79, x_11, x_69, x_28);
lean_dec(x_17);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
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
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_11);
lean_ctor_set(x_86, 1, x_84);
if (lean_is_scalar(x_83)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_83;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_82);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_11);
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_89 = x_80;
} else {
 lean_dec_ref(x_80);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_92 = x_81;
} else {
 lean_dec_ref(x_81);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
if (lean_is_scalar(x_89)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_89;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_88);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_11);
x_95 = lean_ctor_get(x_80, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_80, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_97 = x_80;
} else {
 lean_dec_ref(x_80);
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
}
else
{
uint8_t x_99; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_17);
x_99 = !lean_is_exclusive(x_27);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_27);
lean_ctor_set(x_100, 1, x_28);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_27, 0);
x_102 = lean_ctor_get(x_27, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_27);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_28);
return x_104;
}
}
}
block_124:
{
lean_object* x_112; 
x_112 = l_Lake_Manifest_saveToFile(x_111, x_110, x_8);
lean_dec(x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
if (lean_is_scalar(x_13)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_13;
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_12);
x_27 = x_115;
x_28 = x_114;
goto block_105;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_io_error_to_string(x_116);
x_119 = 3;
x_120 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
x_121 = lean_array_get_size(x_12);
x_122 = lean_array_push(x_12, x_120);
if (lean_is_scalar(x_13)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_13;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_27 = x_123;
x_28 = x_117;
goto block_105;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_129 = lean_ctor_get(x_11, 1);
x_130 = lean_ctor_get(x_11, 2);
x_131 = lean_ctor_get(x_11, 3);
x_132 = lean_ctor_get(x_11, 4);
x_133 = lean_ctor_get(x_11, 5);
x_134 = lean_ctor_get(x_11, 6);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_11);
lean_inc(x_130);
lean_inc(x_14);
x_135 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_135, 0, x_14);
lean_ctor_set(x_135, 1, x_129);
lean_ctor_set(x_135, 2, x_130);
lean_ctor_set(x_135, 3, x_131);
lean_ctor_set(x_135, 4, x_132);
lean_ctor_set(x_135, 5, x_133);
lean_ctor_set(x_135, 6, x_134);
x_136 = lean_ctor_get(x_14, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 2);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_137);
x_140 = l_Lake_defaultLakeDir;
x_141 = l_Lake_loadLeanConfig___closed__1;
x_142 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_141);
x_143 = lean_array_get_size(x_130);
x_183 = lean_unsigned_to_nat(0u);
x_184 = lean_nat_dec_lt(x_183, x_143);
x_185 = lean_ctor_get(x_14, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_14, 4);
lean_inc(x_186);
lean_dec(x_14);
x_187 = l_System_FilePath_join(x_185, x_186);
if (x_184 == 0)
{
lean_dec(x_15);
x_188 = x_142;
goto block_201;
}
else
{
uint8_t x_202; 
x_202 = lean_nat_dec_le(x_143, x_143);
if (x_202 == 0)
{
lean_dec(x_15);
x_188 = x_142;
goto block_201;
}
else
{
size_t x_203; size_t x_204; lean_object* x_205; 
x_203 = 0;
x_204 = lean_usize_of_nat(x_143);
x_205 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__4(x_15, x_130, x_203, x_204, x_142);
lean_dec(x_15);
x_188 = x_205;
goto block_201;
}
}
block_182:
{
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
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
x_148 = lean_unsigned_to_nat(0u);
x_149 = lean_nat_dec_lt(x_148, x_143);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_143);
lean_dec(x_130);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_135);
lean_ctor_set(x_150, 1, x_146);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_145);
return x_151;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_143, x_143);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_143);
lean_dec(x_130);
if (lean_is_scalar(x_147)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_147;
}
lean_ctor_set(x_153, 0, x_135);
lean_ctor_set(x_153, 1, x_146);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_145);
return x_154;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_147);
x_155 = 0;
x_156 = lean_usize_of_nat(x_143);
lean_dec(x_143);
x_157 = lean_box(0);
lean_inc(x_135);
x_158 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3(x_130, x_155, x_156, x_157, x_135, x_146, x_145);
lean_dec(x_130);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
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
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_135);
lean_ctor_set(x_164, 1, x_162);
if (lean_is_scalar(x_161)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_161;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_160);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_135);
x_166 = lean_ctor_get(x_158, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_167 = x_158;
} else {
 lean_dec_ref(x_158);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_159, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_159, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_170 = x_159;
} else {
 lean_dec_ref(x_159);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_135);
x_173 = lean_ctor_get(x_158, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_158, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_175 = x_158;
} else {
 lean_dec_ref(x_158);
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
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_143);
lean_dec(x_135);
lean_dec(x_130);
x_177 = lean_ctor_get(x_144, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_144, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_179 = x_144;
} else {
 lean_dec_ref(x_144);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_145);
return x_181;
}
}
block_201:
{
lean_object* x_189; 
x_189 = l_Lake_Manifest_saveToFile(x_188, x_187, x_8);
lean_dec(x_187);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
if (lean_is_scalar(x_13)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_13;
}
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_12);
x_144 = x_192;
x_145 = x_191;
goto block_182;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_193 = lean_ctor_get(x_189, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 1);
lean_inc(x_194);
lean_dec(x_189);
x_195 = lean_io_error_to_string(x_193);
x_196 = 3;
x_197 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_196);
x_198 = lean_array_get_size(x_12);
x_199 = lean_array_push(x_12, x_197);
if (lean_is_scalar(x_13)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_13;
 lean_ctor_set_tag(x_200, 1);
}
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_144 = x_200;
x_145 = x_194;
goto block_182;
}
}
}
}
else
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_7);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_7);
lean_ctor_set(x_207, 1, x_8);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_7, 0);
x_209 = lean_ctor_get(x_7, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_7);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_8);
return x_211;
}
}
}
block_246:
{
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = !lean_is_exclusive(x_213);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = lean_ctor_get(x_213, 0);
lean_dec(x_219);
x_220 = lean_ctor_get(x_215, 1);
lean_inc(x_220);
lean_dec(x_215);
x_221 = !lean_is_exclusive(x_216);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_ctor_get(x_216, 1);
x_223 = lean_ctor_get(x_216, 0);
lean_dec(x_223);
x_224 = !lean_is_exclusive(x_217);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_217, 1);
lean_dec(x_225);
lean_ctor_set(x_217, 1, x_222);
lean_ctor_set(x_216, 1, x_220);
lean_ctor_set(x_213, 0, x_216);
x_7 = x_213;
x_8 = x_214;
goto block_212;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_217, 0);
lean_inc(x_226);
lean_dec(x_217);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_222);
lean_ctor_set(x_216, 1, x_220);
lean_ctor_set(x_216, 0, x_227);
lean_ctor_set(x_213, 0, x_216);
x_7 = x_213;
x_8 = x_214;
goto block_212;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_216, 1);
lean_inc(x_228);
lean_dec(x_216);
x_229 = lean_ctor_get(x_217, 0);
lean_inc(x_229);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_230 = x_217;
} else {
 lean_dec_ref(x_217);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_228);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_220);
lean_ctor_set(x_213, 0, x_232);
x_7 = x_213;
x_8 = x_214;
goto block_212;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_233 = lean_ctor_get(x_213, 1);
lean_inc(x_233);
lean_dec(x_213);
x_234 = lean_ctor_get(x_215, 1);
lean_inc(x_234);
lean_dec(x_215);
x_235 = lean_ctor_get(x_216, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_236 = x_216;
} else {
 lean_dec_ref(x_216);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_217, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_238 = x_217;
} else {
 lean_dec_ref(x_217);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_235);
if (lean_is_scalar(x_236)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_236;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_234);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_233);
x_7 = x_241;
x_8 = x_214;
goto block_212;
}
}
else
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_213);
if (x_242 == 0)
{
x_7 = x_213;
x_8 = x_214;
goto block_212;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_213, 0);
x_244 = lean_ctor_get(x_213, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_213);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_7 = x_245;
x_8 = x_214;
goto block_212;
}
}
}
block_301:
{
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_247, 1);
lean_inc(x_253);
lean_dec(x_247);
x_254 = !lean_is_exclusive(x_248);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = lean_ctor_get(x_248, 0);
lean_dec(x_255);
x_256 = lean_ctor_get(x_249, 1);
lean_inc(x_256);
lean_dec(x_249);
x_257 = !lean_is_exclusive(x_250);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_258 = lean_ctor_get(x_250, 1);
x_259 = lean_ctor_get(x_250, 0);
lean_dec(x_259);
x_260 = !lean_is_exclusive(x_251);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_261 = lean_ctor_get(x_251, 1);
x_262 = lean_ctor_get(x_251, 0);
lean_dec(x_262);
x_263 = !lean_is_exclusive(x_252);
if (x_263 == 0)
{
lean_object* x_264; 
x_264 = lean_ctor_get(x_252, 1);
lean_dec(x_264);
lean_ctor_set(x_252, 1, x_261);
lean_ctor_set(x_251, 1, x_258);
lean_ctor_set(x_250, 1, x_256);
lean_ctor_set(x_248, 0, x_250);
x_213 = x_248;
x_214 = x_253;
goto block_246;
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_252, 0);
lean_inc(x_265);
lean_dec(x_252);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_261);
lean_ctor_set(x_251, 1, x_258);
lean_ctor_set(x_251, 0, x_266);
lean_ctor_set(x_250, 1, x_256);
lean_ctor_set(x_248, 0, x_250);
x_213 = x_248;
x_214 = x_253;
goto block_246;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_267 = lean_ctor_get(x_251, 1);
lean_inc(x_267);
lean_dec(x_251);
x_268 = lean_ctor_get(x_252, 0);
lean_inc(x_268);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_269 = x_252;
} else {
 lean_dec_ref(x_252);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_267);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_258);
lean_ctor_set(x_250, 1, x_256);
lean_ctor_set(x_250, 0, x_271);
lean_ctor_set(x_248, 0, x_250);
x_213 = x_248;
x_214 = x_253;
goto block_246;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_272 = lean_ctor_get(x_250, 1);
lean_inc(x_272);
lean_dec(x_250);
x_273 = lean_ctor_get(x_251, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_274 = x_251;
} else {
 lean_dec_ref(x_251);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_252, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_276 = x_252;
} else {
 lean_dec_ref(x_252);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_273);
if (lean_is_scalar(x_274)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_274;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_272);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_256);
lean_ctor_set(x_248, 0, x_279);
x_213 = x_248;
x_214 = x_253;
goto block_246;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_280 = lean_ctor_get(x_248, 1);
lean_inc(x_280);
lean_dec(x_248);
x_281 = lean_ctor_get(x_249, 1);
lean_inc(x_281);
lean_dec(x_249);
x_282 = lean_ctor_get(x_250, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_283 = x_250;
} else {
 lean_dec_ref(x_250);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_251, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_285 = x_251;
} else {
 lean_dec_ref(x_251);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_252, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_287 = x_252;
} else {
 lean_dec_ref(x_252);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_284);
if (lean_is_scalar(x_285)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_285;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_282);
if (lean_is_scalar(x_283)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_283;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_281);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_280);
x_213 = x_291;
x_214 = x_253;
goto block_246;
}
}
else
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_247, 1);
lean_inc(x_292);
lean_dec(x_247);
x_293 = !lean_is_exclusive(x_248);
if (x_293 == 0)
{
x_213 = x_248;
x_214 = x_292;
goto block_246;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_248, 0);
x_295 = lean_ctor_get(x_248, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_248);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_213 = x_296;
x_214 = x_292;
goto block_246;
}
}
}
else
{
uint8_t x_297; 
x_297 = !lean_is_exclusive(x_247);
if (x_297 == 0)
{
return x_247;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_247, 0);
x_299 = lean_ctor_get(x_247, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_247);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
block_428:
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_307, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = !lean_is_exclusive(x_307);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_314 = lean_ctor_get(x_307, 1);
x_315 = lean_ctor_get(x_307, 0);
lean_dec(x_315);
x_316 = lean_ctor_get(x_309, 1);
lean_inc(x_316);
lean_dec(x_309);
x_317 = lean_ctor_get(x_310, 1);
lean_inc(x_317);
lean_dec(x_310);
x_318 = lean_ctor_get(x_311, 1);
lean_inc(x_318);
lean_dec(x_311);
x_319 = lean_ctor_get(x_312, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_312, 1);
lean_inc(x_320);
lean_dec(x_312);
x_321 = lean_box(x_4);
lean_inc(x_2);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_1);
lean_inc(x_304);
x_322 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterialize___lambda__3___boxed), 13, 6);
lean_closure_set(x_322, 0, x_304);
lean_closure_set(x_322, 1, x_1);
lean_closure_set(x_322, 2, x_302);
lean_closure_set(x_322, 3, x_303);
lean_closure_set(x_322, 4, x_2);
lean_closure_set(x_322, 5, x_321);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_319, 0);
lean_inc(x_323);
lean_dec(x_319);
if (lean_obj_tag(x_323) == 11)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_323);
lean_dec(x_322);
lean_free_object(x_307);
x_324 = l_Lake_loadPackage___lambda__3___closed__1;
x_325 = lean_string_append(x_324, x_306);
lean_dec(x_306);
x_326 = l_Lake_Workspace_updateAndMaterialize___closed__1;
x_327 = lean_string_append(x_325, x_326);
x_328 = 1;
x_329 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set_uint8(x_329, sizeof(void*)*1, x_328);
x_330 = lean_array_push(x_314, x_329);
x_331 = lean_box(0);
x_332 = l_Lake_Workspace_updateAndMaterialize___lambda__3(x_304, x_1, x_302, x_303, x_2, x_4, x_331, x_320, x_318, x_317, x_316, x_330, x_308);
x_247 = x_332;
goto block_301;
}
else
{
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_free_object(x_307);
x_333 = lean_box(0);
x_334 = l_Lake_Workspace_updateAndMaterialize___lambda__4(x_306, x_323, x_322, x_333, x_320, x_318, x_317, x_316, x_314, x_308);
lean_dec(x_306);
x_247 = x_334;
goto block_301;
}
else
{
lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_322);
lean_dec(x_320);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_306);
x_335 = lean_io_error_to_string(x_323);
x_336 = 3;
x_337 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*1, x_336);
x_338 = lean_array_get_size(x_314);
x_339 = lean_array_push(x_314, x_337);
lean_ctor_set_tag(x_307, 1);
lean_ctor_set(x_307, 1, x_339);
lean_ctor_set(x_307, 0, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_307);
lean_ctor_set(x_340, 1, x_308);
x_247 = x_340;
goto block_301;
}
}
}
else
{
lean_free_object(x_307);
lean_dec(x_306);
lean_dec(x_304);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_319, 0);
lean_inc(x_341);
lean_dec(x_319);
x_342 = lean_box(0);
x_343 = l_Lake_Workspace_updateAndMaterialize___lambda__5(x_341, x_322, x_302, x_303, x_342, x_320, x_318, x_317, x_316, x_314, x_308);
x_247 = x_343;
goto block_301;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_344 = lean_ctor_get(x_319, 0);
lean_inc(x_344);
lean_dec(x_319);
x_345 = lean_ctor_get(x_344, 3);
lean_inc(x_345);
x_346 = lean_array_get_size(x_345);
x_347 = lean_unsigned_to_nat(0u);
x_348 = lean_nat_dec_lt(x_347, x_346);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_346);
lean_dec(x_345);
x_349 = lean_box(0);
x_350 = l_Lake_Workspace_updateAndMaterialize___lambda__5(x_344, x_322, x_302, x_303, x_349, x_320, x_318, x_317, x_316, x_314, x_308);
x_247 = x_350;
goto block_301;
}
else
{
uint8_t x_351; 
x_351 = lean_nat_dec_le(x_346, x_346);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_346);
lean_dec(x_345);
x_352 = lean_box(0);
x_353 = l_Lake_Workspace_updateAndMaterialize___lambda__5(x_344, x_322, x_302, x_303, x_352, x_320, x_318, x_317, x_316, x_314, x_308);
x_247 = x_353;
goto block_301;
}
else
{
size_t x_354; size_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_354 = 0;
x_355 = lean_usize_of_nat(x_346);
lean_dec(x_346);
x_356 = lean_box(0);
x_357 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__17(x_3, x_345, x_354, x_355, x_356, x_320, x_318, x_317, x_316, x_314, x_308);
lean_dec(x_345);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_357, 1);
lean_inc(x_363);
lean_dec(x_357);
x_364 = lean_ctor_get(x_358, 1);
lean_inc(x_364);
lean_dec(x_358);
x_365 = lean_ctor_get(x_359, 1);
lean_inc(x_365);
lean_dec(x_359);
x_366 = lean_ctor_get(x_360, 1);
lean_inc(x_366);
lean_dec(x_360);
x_367 = lean_ctor_get(x_361, 1);
lean_inc(x_367);
lean_dec(x_361);
x_368 = lean_ctor_get(x_362, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_362, 1);
lean_inc(x_369);
lean_dec(x_362);
x_370 = l_Lake_Workspace_updateAndMaterialize___lambda__5(x_344, x_322, x_302, x_303, x_368, x_369, x_367, x_366, x_365, x_364, x_363);
lean_dec(x_368);
x_247 = x_370;
goto block_301;
}
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_371 = lean_ctor_get(x_307, 1);
lean_inc(x_371);
lean_dec(x_307);
x_372 = lean_ctor_get(x_309, 1);
lean_inc(x_372);
lean_dec(x_309);
x_373 = lean_ctor_get(x_310, 1);
lean_inc(x_373);
lean_dec(x_310);
x_374 = lean_ctor_get(x_311, 1);
lean_inc(x_374);
lean_dec(x_311);
x_375 = lean_ctor_get(x_312, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_312, 1);
lean_inc(x_376);
lean_dec(x_312);
x_377 = lean_box(x_4);
lean_inc(x_2);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_1);
lean_inc(x_304);
x_378 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterialize___lambda__3___boxed), 13, 6);
lean_closure_set(x_378, 0, x_304);
lean_closure_set(x_378, 1, x_1);
lean_closure_set(x_378, 2, x_302);
lean_closure_set(x_378, 3, x_303);
lean_closure_set(x_378, 4, x_2);
lean_closure_set(x_378, 5, x_377);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_375, 0);
lean_inc(x_379);
lean_dec(x_375);
if (lean_obj_tag(x_379) == 11)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_379);
lean_dec(x_378);
x_380 = l_Lake_loadPackage___lambda__3___closed__1;
x_381 = lean_string_append(x_380, x_306);
lean_dec(x_306);
x_382 = l_Lake_Workspace_updateAndMaterialize___closed__1;
x_383 = lean_string_append(x_381, x_382);
x_384 = 1;
x_385 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set_uint8(x_385, sizeof(void*)*1, x_384);
x_386 = lean_array_push(x_371, x_385);
x_387 = lean_box(0);
x_388 = l_Lake_Workspace_updateAndMaterialize___lambda__3(x_304, x_1, x_302, x_303, x_2, x_4, x_387, x_376, x_374, x_373, x_372, x_386, x_308);
x_247 = x_388;
goto block_301;
}
else
{
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_box(0);
x_390 = l_Lake_Workspace_updateAndMaterialize___lambda__4(x_306, x_379, x_378, x_389, x_376, x_374, x_373, x_372, x_371, x_308);
lean_dec(x_306);
x_247 = x_390;
goto block_301;
}
else
{
lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_306);
x_391 = lean_io_error_to_string(x_379);
x_392 = 3;
x_393 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set_uint8(x_393, sizeof(void*)*1, x_392);
x_394 = lean_array_get_size(x_371);
x_395 = lean_array_push(x_371, x_393);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_308);
x_247 = x_397;
goto block_301;
}
}
}
else
{
lean_dec(x_306);
lean_dec(x_304);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_375, 0);
lean_inc(x_398);
lean_dec(x_375);
x_399 = lean_box(0);
x_400 = l_Lake_Workspace_updateAndMaterialize___lambda__5(x_398, x_378, x_302, x_303, x_399, x_376, x_374, x_373, x_372, x_371, x_308);
x_247 = x_400;
goto block_301;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_401 = lean_ctor_get(x_375, 0);
lean_inc(x_401);
lean_dec(x_375);
x_402 = lean_ctor_get(x_401, 3);
lean_inc(x_402);
x_403 = lean_array_get_size(x_402);
x_404 = lean_unsigned_to_nat(0u);
x_405 = lean_nat_dec_lt(x_404, x_403);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
lean_dec(x_403);
lean_dec(x_402);
x_406 = lean_box(0);
x_407 = l_Lake_Workspace_updateAndMaterialize___lambda__5(x_401, x_378, x_302, x_303, x_406, x_376, x_374, x_373, x_372, x_371, x_308);
x_247 = x_407;
goto block_301;
}
else
{
uint8_t x_408; 
x_408 = lean_nat_dec_le(x_403, x_403);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; 
lean_dec(x_403);
lean_dec(x_402);
x_409 = lean_box(0);
x_410 = l_Lake_Workspace_updateAndMaterialize___lambda__5(x_401, x_378, x_302, x_303, x_409, x_376, x_374, x_373, x_372, x_371, x_308);
x_247 = x_410;
goto block_301;
}
else
{
size_t x_411; size_t x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_411 = 0;
x_412 = lean_usize_of_nat(x_403);
lean_dec(x_403);
x_413 = lean_box(0);
x_414 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__17(x_3, x_402, x_411, x_412, x_413, x_376, x_374, x_373, x_372, x_371, x_308);
lean_dec(x_402);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_414, 1);
lean_inc(x_420);
lean_dec(x_414);
x_421 = lean_ctor_get(x_415, 1);
lean_inc(x_421);
lean_dec(x_415);
x_422 = lean_ctor_get(x_416, 1);
lean_inc(x_422);
lean_dec(x_416);
x_423 = lean_ctor_get(x_417, 1);
lean_inc(x_423);
lean_dec(x_417);
x_424 = lean_ctor_get(x_418, 1);
lean_inc(x_424);
lean_dec(x_418);
x_425 = lean_ctor_get(x_419, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_419, 1);
lean_inc(x_426);
lean_dec(x_419);
x_427 = l_Lake_Workspace_updateAndMaterialize___lambda__5(x_401, x_378, x_302, x_303, x_425, x_426, x_424, x_423, x_422, x_421, x_420);
lean_dec(x_425);
x_247 = x_427;
goto block_301;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8(x_1, x_2, x_3, x_4, x_16, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11(x_1, x_15, x_3, x_16, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__12(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__15(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__17(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l_Lake_Workspace_updateAndMaterialize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l_Lake_Workspace_updateAndMaterialize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lake_Workspace_updateAndMaterialize___lambda__3(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Workspace_updateAndMaterialize___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_Workspace_updateAndMaterialize___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lake_Workspace_updateAndMaterialize(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(x_9, x_2, x_3);
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
x_17 = l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(x_12, x_2, x_3);
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
x_24 = l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(x_19, x_2, x_3);
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
x_29 = l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(x_22, x_2, x_3);
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
x_38 = l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(x_33, x_2, x_3);
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
x_191 = l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(x_36, x_2, x_3);
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
x_347 = l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(x_342, x_2, x_3);
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
x_424 = l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(x_345, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_materializeDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lake_Workspace_materializeDeps___spec__2(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dependency '", 12);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' of '", 6);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' not in manifest; ", 19);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("this suggests that the manifest is corrupt;", 43);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("use `lake update` to generate a new, complete file (warning: this will update ALL workspace dependencies)", 105);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("use `lake update ", 17);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` to add it", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_166; lean_object* x_167; lean_object* x_250; lean_object* x_251; lean_object* x_382; lean_object* x_383; 
x_21 = lean_array_uget(x_9, x_8);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_uset(x_9, x_8, x_22);
x_82 = lean_ctor_get(x_21, 0);
lean_inc(x_82);
x_382 = l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__7(x_5, x_82);
x_383 = l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__10(x_11, x_82);
if (lean_obj_tag(x_383) == 0)
{
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
x_384 = lean_ctor_get(x_6, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_384, 2);
lean_inc(x_385);
lean_dec(x_384);
x_386 = lean_ctor_get(x_3, 2);
x_387 = lean_ctor_get(x_386, 2);
x_388 = lean_name_eq(x_385, x_387);
if (x_388 == 0)
{
uint8_t x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_389 = 1;
x_390 = l_Lean_Name_toString(x_82, x_389);
x_391 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__1;
x_392 = lean_string_append(x_391, x_390);
lean_dec(x_390);
x_393 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__2;
x_394 = lean_string_append(x_392, x_393);
x_395 = l_Lean_Name_toString(x_385, x_389);
x_396 = lean_string_append(x_394, x_395);
lean_dec(x_395);
x_397 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__3;
x_398 = lean_string_append(x_396, x_397);
x_399 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__4;
x_400 = lean_string_append(x_398, x_399);
x_401 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__5;
x_402 = lean_string_append(x_400, x_401);
x_403 = 3;
x_404 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set_uint8(x_404, sizeof(void*)*1, x_403);
x_405 = lean_array_get_size(x_13);
x_406 = lean_array_push(x_13, x_404);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
x_24 = x_407;
x_25 = x_14;
goto block_81;
}
else
{
uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_385);
x_408 = 1;
x_409 = l_Lean_Name_toString(x_82, x_408);
x_410 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__1;
x_411 = lean_string_append(x_410, x_409);
x_412 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__3;
x_413 = lean_string_append(x_411, x_412);
x_414 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__6;
x_415 = lean_string_append(x_414, x_409);
lean_dec(x_409);
x_416 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__7;
x_417 = lean_string_append(x_415, x_416);
x_418 = lean_string_append(x_413, x_417);
lean_dec(x_417);
x_419 = 3;
x_420 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*1, x_419);
x_421 = lean_array_get_size(x_13);
x_422 = lean_array_push(x_13, x_420);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
x_24 = x_423;
x_25 = x_14;
goto block_81;
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_424 = lean_ctor_get(x_382, 0);
lean_inc(x_424);
lean_dec(x_382);
x_425 = lean_ctor_get(x_12, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
lean_dec(x_425);
x_427 = lean_ctor_get(x_12, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_427, 4);
lean_inc(x_428);
lean_dec(x_427);
lean_inc(x_4);
x_429 = l_Lake_PackageEntry_materialize(x_424, x_21, x_426, x_4, x_428, x_13, x_14);
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; uint8_t x_432; 
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = !lean_is_exclusive(x_430);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_433 = lean_ctor_get(x_430, 0);
x_434 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_434, 0, x_433);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_11);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_12);
lean_ctor_set(x_430, 0, x_436);
x_250 = x_430;
x_251 = x_431;
goto block_381;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_437 = lean_ctor_get(x_430, 0);
x_438 = lean_ctor_get(x_430, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_430);
x_439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_439, 0, x_437);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_11);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_12);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_438);
x_250 = x_442;
x_251 = x_431;
goto block_381;
}
}
else
{
lean_object* x_443; uint8_t x_444; 
lean_dec(x_12);
lean_dec(x_11);
x_443 = lean_ctor_get(x_429, 1);
lean_inc(x_443);
lean_dec(x_429);
x_444 = !lean_is_exclusive(x_430);
if (x_444 == 0)
{
x_250 = x_430;
x_251 = x_443;
goto block_381;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_430, 0);
x_446 = lean_ctor_get(x_430, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_430);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
x_250 = x_447;
x_251 = x_443;
goto block_381;
}
}
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_382);
lean_dec(x_82);
lean_dec(x_21);
x_448 = lean_ctor_get(x_383, 0);
lean_inc(x_448);
lean_dec(x_383);
x_449 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_449, 0, x_448);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_11);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_12);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_13);
x_24 = x_452;
x_25 = x_14;
goto block_81;
}
block_81:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_24, 0);
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
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_27, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_25);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_27, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_25);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_26, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_24);
lean_ctor_set(x_45, 1, x_25);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_26, 1);
lean_inc(x_46);
lean_dec(x_26);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_48 = x_27;
} else {
 lean_dec_ref(x_27);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_28, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_50 = x_28;
} else {
 lean_dec_ref(x_28);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set(x_24, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_24);
lean_ctor_set(x_54, 1, x_25);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_dec(x_24);
x_56 = lean_ctor_get(x_26, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_57 = x_26;
} else {
 lean_dec_ref(x_26);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_27, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_59 = x_27;
} else {
 lean_dec_ref(x_27);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_28, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_61 = x_28;
} else {
 lean_dec_ref(x_28);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_57;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_56);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_55);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_25);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_24, 1);
lean_inc(x_67);
lean_dec(x_24);
x_68 = lean_ctor_get(x_26, 1);
lean_inc(x_68);
lean_dec(x_26);
x_69 = lean_ctor_get(x_27, 1);
lean_inc(x_69);
lean_dec(x_27);
x_70 = lean_ctor_get(x_28, 0);
lean_inc(x_70);
lean_dec(x_28);
x_71 = 1;
x_72 = lean_usize_add(x_8, x_71);
x_73 = lean_array_uset(x_23, x_8, x_70);
x_8 = x_72;
x_9 = x_73;
x_11 = x_69;
x_12 = x_68;
x_13 = x_67;
x_14 = x_25;
goto _start;
}
}
else
{
uint8_t x_75; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_24);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_24);
lean_ctor_set(x_76, 1, x_25);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_24, 0);
x_78 = lean_ctor_get(x_24, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_24);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_25);
return x_80;
}
}
}
block_165:
{
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_82);
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_83, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_85);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_85, 0);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_86);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_86, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_87);
if (x_94 == 0)
{
x_24 = x_83;
x_25 = x_84;
goto block_81;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_87, 0);
lean_inc(x_95);
lean_dec(x_87);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_86, 0, x_96);
x_24 = x_83;
x_25 = x_84;
goto block_81;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_86, 1);
lean_inc(x_97);
lean_dec(x_86);
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_99 = x_87;
} else {
 lean_dec_ref(x_87);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set(x_85, 0, x_101);
x_24 = x_83;
x_25 = x_84;
goto block_81;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_85, 1);
lean_inc(x_102);
lean_dec(x_85);
x_103 = lean_ctor_get(x_86, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_104 = x_86;
} else {
 lean_dec_ref(x_86);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_87, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_106 = x_87;
} else {
 lean_dec_ref(x_87);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 1, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_105);
if (lean_is_scalar(x_104)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_104;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_103);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_102);
lean_ctor_set(x_83, 0, x_109);
x_24 = x_83;
x_25 = x_84;
goto block_81;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_83, 1);
lean_inc(x_110);
lean_dec(x_83);
x_111 = lean_ctor_get(x_85, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_112 = x_85;
} else {
 lean_dec_ref(x_85);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_86, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_114 = x_86;
} else {
 lean_dec_ref(x_86);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_87, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_116 = x_87;
} else {
 lean_dec_ref(x_87);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 1, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_115);
if (lean_is_scalar(x_114)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_114;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_113);
if (lean_is_scalar(x_112)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_112;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_110);
x_24 = x_120;
x_25 = x_84;
goto block_81;
}
}
else
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_83);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_83, 0);
lean_dec(x_122);
x_123 = !lean_is_exclusive(x_85);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_85, 0);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_86);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_86, 1);
x_127 = lean_ctor_get(x_86, 0);
lean_dec(x_127);
x_128 = !lean_is_exclusive(x_87);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_87, 0);
lean_inc(x_129);
x_130 = l_Lean_RBNode_insert___at_Lake_Workspace_materializeDeps___spec__1(x_126, x_82, x_129);
lean_ctor_set(x_86, 1, x_130);
x_24 = x_83;
x_25 = x_84;
goto block_81;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_87, 0);
lean_inc(x_131);
lean_dec(x_87);
lean_inc(x_131);
x_132 = l_Lean_RBNode_insert___at_Lake_Workspace_materializeDeps___spec__1(x_126, x_82, x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_86, 1, x_132);
lean_ctor_set(x_86, 0, x_133);
x_24 = x_83;
x_25 = x_84;
goto block_81;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_86, 1);
lean_inc(x_134);
lean_dec(x_86);
x_135 = lean_ctor_get(x_87, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_136 = x_87;
} else {
 lean_dec_ref(x_87);
 x_136 = lean_box(0);
}
lean_inc(x_135);
x_137 = l_Lean_RBNode_insert___at_Lake_Workspace_materializeDeps___spec__1(x_134, x_82, x_135);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
lean_ctor_set(x_85, 0, x_139);
x_24 = x_83;
x_25 = x_84;
goto block_81;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_140 = lean_ctor_get(x_85, 1);
lean_inc(x_140);
lean_dec(x_85);
x_141 = lean_ctor_get(x_86, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_142 = x_86;
} else {
 lean_dec_ref(x_86);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_87, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_144 = x_87;
} else {
 lean_dec_ref(x_87);
 x_144 = lean_box(0);
}
lean_inc(x_143);
x_145 = l_Lean_RBNode_insert___at_Lake_Workspace_materializeDeps___spec__1(x_141, x_82, x_143);
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_143);
if (lean_is_scalar(x_142)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_142;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_140);
lean_ctor_set(x_83, 0, x_148);
x_24 = x_83;
x_25 = x_84;
goto block_81;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_149 = lean_ctor_get(x_83, 1);
lean_inc(x_149);
lean_dec(x_83);
x_150 = lean_ctor_get(x_85, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_151 = x_85;
} else {
 lean_dec_ref(x_85);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_86, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_153 = x_86;
} else {
 lean_dec_ref(x_86);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_87, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_155 = x_87;
} else {
 lean_dec_ref(x_87);
 x_155 = lean_box(0);
}
lean_inc(x_154);
x_156 = l_Lean_RBNode_insert___at_Lake_Workspace_materializeDeps___spec__1(x_152, x_82, x_154);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(1, 1, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_154);
if (lean_is_scalar(x_153)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_153;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
if (lean_is_scalar(x_151)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_151;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_150);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_149);
x_24 = x_160;
x_25 = x_84;
goto block_81;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_82);
x_161 = !lean_is_exclusive(x_83);
if (x_161 == 0)
{
x_24 = x_83;
x_25 = x_84;
goto block_81;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_83, 0);
x_163 = lean_ctor_get(x_83, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_83);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_24 = x_164;
x_25 = x_84;
goto block_81;
}
}
}
block_249:
{
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_166);
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_166, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_168);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_168, 0);
lean_dec(x_174);
x_175 = !lean_is_exclusive(x_169);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_169, 0);
lean_dec(x_176);
x_177 = !lean_is_exclusive(x_170);
if (x_177 == 0)
{
x_83 = x_166;
x_84 = x_167;
goto block_165;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_170, 0);
lean_inc(x_178);
lean_dec(x_170);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_169, 0, x_179);
x_83 = x_166;
x_84 = x_167;
goto block_165;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_169, 1);
lean_inc(x_180);
lean_dec(x_169);
x_181 = lean_ctor_get(x_170, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_182 = x_170;
} else {
 lean_dec_ref(x_170);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(0, 1, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_181);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_180);
lean_ctor_set(x_168, 0, x_184);
x_83 = x_166;
x_84 = x_167;
goto block_165;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_185 = lean_ctor_get(x_168, 1);
lean_inc(x_185);
lean_dec(x_168);
x_186 = lean_ctor_get(x_169, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_187 = x_169;
} else {
 lean_dec_ref(x_169);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_170, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_189 = x_170;
} else {
 lean_dec_ref(x_170);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 1, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_188);
if (lean_is_scalar(x_187)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_187;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_186);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_185);
lean_ctor_set(x_166, 0, x_192);
x_83 = x_166;
x_84 = x_167;
goto block_165;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_193 = lean_ctor_get(x_166, 1);
lean_inc(x_193);
lean_dec(x_166);
x_194 = lean_ctor_get(x_168, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_195 = x_168;
} else {
 lean_dec_ref(x_168);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_169, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_197 = x_169;
} else {
 lean_dec_ref(x_169);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_170, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_199 = x_170;
} else {
 lean_dec_ref(x_170);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
if (lean_is_scalar(x_197)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_197;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_196);
if (lean_is_scalar(x_195)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_195;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_194);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_193);
x_83 = x_203;
x_84 = x_167;
goto block_165;
}
}
else
{
uint8_t x_204; 
lean_dec(x_168);
x_204 = !lean_is_exclusive(x_170);
if (x_204 == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_166);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = lean_ctor_get(x_170, 0);
x_207 = lean_ctor_get(x_166, 0);
lean_dec(x_207);
x_208 = !lean_is_exclusive(x_169);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_209 = lean_ctor_get(x_169, 1);
x_210 = lean_ctor_get(x_169, 0);
lean_dec(x_210);
x_211 = !lean_is_exclusive(x_206);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_206, 0);
x_213 = lean_ctor_get(x_206, 1);
lean_ctor_set(x_170, 0, x_212);
lean_ctor_set(x_206, 1, x_209);
lean_ctor_set(x_206, 0, x_170);
lean_ctor_set(x_169, 1, x_213);
lean_ctor_set(x_169, 0, x_206);
lean_ctor_set(x_166, 0, x_169);
x_83 = x_166;
x_84 = x_167;
goto block_165;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_206, 0);
x_215 = lean_ctor_get(x_206, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
lean_ctor_set(x_170, 0, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_170);
lean_ctor_set(x_216, 1, x_209);
lean_ctor_set(x_169, 1, x_215);
lean_ctor_set(x_169, 0, x_216);
lean_ctor_set(x_166, 0, x_169);
x_83 = x_166;
x_84 = x_167;
goto block_165;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_217 = lean_ctor_get(x_169, 1);
lean_inc(x_217);
lean_dec(x_169);
x_218 = lean_ctor_get(x_206, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_206, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_220 = x_206;
} else {
 lean_dec_ref(x_206);
 x_220 = lean_box(0);
}
lean_ctor_set(x_170, 0, x_218);
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_170);
lean_ctor_set(x_221, 1, x_217);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_219);
lean_ctor_set(x_166, 0, x_222);
x_83 = x_166;
x_84 = x_167;
goto block_165;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_223 = lean_ctor_get(x_170, 0);
x_224 = lean_ctor_get(x_166, 1);
lean_inc(x_224);
lean_dec(x_166);
x_225 = lean_ctor_get(x_169, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_226 = x_169;
} else {
 lean_dec_ref(x_169);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_223, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_229 = x_223;
} else {
 lean_dec_ref(x_223);
 x_229 = lean_box(0);
}
lean_ctor_set(x_170, 0, x_227);
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_170);
lean_ctor_set(x_230, 1, x_225);
if (lean_is_scalar(x_226)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_226;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_228);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_224);
x_83 = x_232;
x_84 = x_167;
goto block_165;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_233 = lean_ctor_get(x_170, 0);
lean_inc(x_233);
lean_dec(x_170);
x_234 = lean_ctor_get(x_166, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_235 = x_166;
} else {
 lean_dec_ref(x_166);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_169, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_237 = x_169;
} else {
 lean_dec_ref(x_169);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_233, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_233, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_240 = x_233;
} else {
 lean_dec_ref(x_233);
 x_240 = lean_box(0);
}
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_238);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_236);
if (lean_is_scalar(x_237)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_237;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_239);
if (lean_is_scalar(x_235)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_235;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_234);
x_83 = x_244;
x_84 = x_167;
goto block_165;
}
}
}
else
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_166);
if (x_245 == 0)
{
x_83 = x_166;
x_84 = x_167;
goto block_165;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_166, 0);
x_247 = lean_ctor_get(x_166, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_166);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_83 = x_248;
x_84 = x_167;
goto block_165;
}
}
}
block_381:
{
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_250);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_250, 0);
lean_dec(x_256);
x_257 = !lean_is_exclusive(x_252);
if (x_257 == 0)
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_ctor_get(x_252, 0);
lean_dec(x_258);
x_259 = !lean_is_exclusive(x_253);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_253, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_254);
if (x_261 == 0)
{
x_83 = x_250;
x_84 = x_251;
goto block_165;
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_254, 0);
lean_inc(x_262);
lean_dec(x_254);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_253, 0, x_263);
x_83 = x_250;
x_84 = x_251;
goto block_165;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_264 = lean_ctor_get(x_253, 1);
lean_inc(x_264);
lean_dec(x_253);
x_265 = lean_ctor_get(x_254, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_266 = x_254;
} else {
 lean_dec_ref(x_254);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(0, 1, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_265);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_264);
lean_ctor_set(x_252, 0, x_268);
x_83 = x_250;
x_84 = x_251;
goto block_165;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_269 = lean_ctor_get(x_252, 1);
lean_inc(x_269);
lean_dec(x_252);
x_270 = lean_ctor_get(x_253, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_271 = x_253;
} else {
 lean_dec_ref(x_253);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_254, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_273 = x_254;
} else {
 lean_dec_ref(x_254);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
if (lean_is_scalar(x_271)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_271;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_270);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_269);
lean_ctor_set(x_250, 0, x_276);
x_83 = x_250;
x_84 = x_251;
goto block_165;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_277 = lean_ctor_get(x_250, 1);
lean_inc(x_277);
lean_dec(x_250);
x_278 = lean_ctor_get(x_252, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_279 = x_252;
} else {
 lean_dec_ref(x_252);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_253, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_281 = x_253;
} else {
 lean_dec_ref(x_253);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_254, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_283 = x_254;
} else {
 lean_dec_ref(x_254);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 1, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_282);
if (lean_is_scalar(x_281)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_281;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_280);
if (lean_is_scalar(x_279)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_279;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_278);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_277);
x_83 = x_287;
x_84 = x_251;
goto block_165;
}
}
else
{
lean_object* x_288; uint8_t x_289; 
x_288 = lean_ctor_get(x_250, 1);
lean_inc(x_288);
lean_dec(x_250);
x_289 = !lean_is_exclusive(x_252);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_290 = lean_ctor_get(x_252, 1);
x_291 = lean_ctor_get(x_252, 0);
lean_dec(x_291);
x_292 = !lean_is_exclusive(x_253);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_293 = lean_ctor_get(x_253, 1);
x_294 = lean_ctor_get(x_253, 0);
lean_dec(x_294);
x_295 = !lean_is_exclusive(x_254);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_254, 0);
lean_inc(x_290);
lean_inc(x_1);
x_297 = l_Lake_loadDepPackage(x_296, x_1, x_2, x_290, x_288, x_251);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = !lean_is_exclusive(x_298);
if (x_300 == 0)
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_298, 0);
lean_ctor_set(x_254, 0, x_301);
lean_ctor_set(x_298, 0, x_252);
x_166 = x_298;
x_167 = x_299;
goto block_249;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_298, 0);
x_303 = lean_ctor_get(x_298, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_298);
lean_ctor_set(x_254, 0, x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_252);
lean_ctor_set(x_304, 1, x_303);
x_166 = x_304;
x_167 = x_299;
goto block_249;
}
}
else
{
lean_object* x_305; uint8_t x_306; 
lean_free_object(x_254);
lean_free_object(x_253);
lean_dec(x_293);
lean_free_object(x_252);
lean_dec(x_290);
x_305 = lean_ctor_get(x_297, 1);
lean_inc(x_305);
lean_dec(x_297);
x_306 = !lean_is_exclusive(x_298);
if (x_306 == 0)
{
x_166 = x_298;
x_167 = x_305;
goto block_249;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_298, 0);
x_308 = lean_ctor_get(x_298, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_298);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
x_166 = x_309;
x_167 = x_305;
goto block_249;
}
}
}
else
{
uint8_t x_310; 
lean_free_object(x_254);
lean_free_object(x_253);
lean_dec(x_293);
lean_free_object(x_252);
lean_dec(x_290);
lean_dec(x_82);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_297);
if (x_310 == 0)
{
return x_297;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_297, 0);
x_312 = lean_ctor_get(x_297, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_297);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_254, 0);
lean_inc(x_314);
lean_dec(x_254);
lean_inc(x_290);
lean_inc(x_1);
x_315 = l_Lake_loadDepPackage(x_314, x_1, x_2, x_290, x_288, x_251);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_320 = x_316;
} else {
 lean_dec_ref(x_316);
 x_320 = lean_box(0);
}
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_253, 0, x_321);
if (lean_is_scalar(x_320)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_320;
}
lean_ctor_set(x_322, 0, x_252);
lean_ctor_set(x_322, 1, x_319);
x_166 = x_322;
x_167 = x_317;
goto block_249;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_free_object(x_253);
lean_dec(x_293);
lean_free_object(x_252);
lean_dec(x_290);
x_323 = lean_ctor_get(x_315, 1);
lean_inc(x_323);
lean_dec(x_315);
x_324 = lean_ctor_get(x_316, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_316, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_326 = x_316;
} else {
 lean_dec_ref(x_316);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
x_166 = x_327;
x_167 = x_323;
goto block_249;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_free_object(x_253);
lean_dec(x_293);
lean_free_object(x_252);
lean_dec(x_290);
lean_dec(x_82);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_328 = lean_ctor_get(x_315, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_315, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_330 = x_315;
} else {
 lean_dec_ref(x_315);
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
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_253, 1);
lean_inc(x_332);
lean_dec(x_253);
x_333 = lean_ctor_get(x_254, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_334 = x_254;
} else {
 lean_dec_ref(x_254);
 x_334 = lean_box(0);
}
lean_inc(x_290);
lean_inc(x_1);
x_335 = l_Lake_loadDepPackage(x_333, x_1, x_2, x_290, x_288, x_251);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = lean_ctor_get(x_336, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_336, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_340 = x_336;
} else {
 lean_dec_ref(x_336);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_341 = lean_alloc_ctor(1, 1, 0);
} else {
 x_341 = x_334;
}
lean_ctor_set(x_341, 0, x_338);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_332);
lean_ctor_set(x_252, 0, x_342);
if (lean_is_scalar(x_340)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_340;
}
lean_ctor_set(x_343, 0, x_252);
lean_ctor_set(x_343, 1, x_339);
x_166 = x_343;
x_167 = x_337;
goto block_249;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_334);
lean_dec(x_332);
lean_free_object(x_252);
lean_dec(x_290);
x_344 = lean_ctor_get(x_335, 1);
lean_inc(x_344);
lean_dec(x_335);
x_345 = lean_ctor_get(x_336, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_336, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_347 = x_336;
} else {
 lean_dec_ref(x_336);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_346);
x_166 = x_348;
x_167 = x_344;
goto block_249;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_334);
lean_dec(x_332);
lean_free_object(x_252);
lean_dec(x_290);
lean_dec(x_82);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_349 = lean_ctor_get(x_335, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_335, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_351 = x_335;
} else {
 lean_dec_ref(x_335);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_350);
return x_352;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_353 = lean_ctor_get(x_252, 1);
lean_inc(x_353);
lean_dec(x_252);
x_354 = lean_ctor_get(x_253, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_355 = x_253;
} else {
 lean_dec_ref(x_253);
 x_355 = lean_box(0);
}
x_356 = lean_ctor_get(x_254, 0);
lean_inc(x_356);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_357 = x_254;
} else {
 lean_dec_ref(x_254);
 x_357 = lean_box(0);
}
lean_inc(x_353);
lean_inc(x_1);
x_358 = l_Lake_loadDepPackage(x_356, x_1, x_2, x_353, x_288, x_251);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = lean_ctor_get(x_359, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_363 = x_359;
} else {
 lean_dec_ref(x_359);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_364 = lean_alloc_ctor(1, 1, 0);
} else {
 x_364 = x_357;
}
lean_ctor_set(x_364, 0, x_361);
if (lean_is_scalar(x_355)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_355;
}
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_354);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_353);
if (lean_is_scalar(x_363)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_363;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_362);
x_166 = x_367;
x_167 = x_360;
goto block_249;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_357);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
x_368 = lean_ctor_get(x_358, 1);
lean_inc(x_368);
lean_dec(x_358);
x_369 = lean_ctor_get(x_359, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_359, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_371 = x_359;
} else {
 lean_dec_ref(x_359);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
x_166 = x_372;
x_167 = x_368;
goto block_249;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_357);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_82);
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_373 = lean_ctor_get(x_358, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_358, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_375 = x_358;
} else {
 lean_dec_ref(x_358);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
}
}
}
else
{
uint8_t x_377; 
x_377 = !lean_is_exclusive(x_250);
if (x_377 == 0)
{
x_83 = x_250;
x_84 = x_251;
goto block_165;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_250, 0);
x_379 = lean_ctor_get(x_250, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_250);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_83 = x_380;
x_84 = x_251;
goto block_165;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_77; 
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
lean_inc(x_1);
lean_inc(x_5);
x_77 = lean_apply_6(x_1, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_78, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_79);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_79, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_80);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_80, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_19 = x_78;
x_20 = x_82;
goto block_76;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
lean_dec(x_81);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_80, 0, x_91);
x_19 = x_78;
x_20 = x_82;
goto block_76;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_dec(x_80);
x_93 = lean_ctor_get(x_81, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_94 = x_81;
} else {
 lean_dec_ref(x_81);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set(x_79, 0, x_96);
x_19 = x_78;
x_20 = x_82;
goto block_76;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_79, 1);
lean_inc(x_97);
lean_dec(x_79);
x_98 = lean_ctor_get(x_80, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_99 = x_80;
} else {
 lean_dec_ref(x_80);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_81, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_101 = x_81;
} else {
 lean_dec_ref(x_81);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
if (lean_is_scalar(x_99)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_99;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_97);
lean_ctor_set(x_78, 0, x_104);
x_19 = x_78;
x_20 = x_82;
goto block_76;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_ctor_get(x_78, 1);
lean_inc(x_105);
lean_dec(x_78);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_107 = x_79;
} else {
 lean_dec_ref(x_79);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_80, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_109 = x_80;
} else {
 lean_dec_ref(x_80);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_81, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_111 = x_81;
} else {
 lean_dec_ref(x_81);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_110);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_108);
if (lean_is_scalar(x_107)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_107;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_106);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_105);
x_19 = x_115;
x_20 = x_82;
goto block_76;
}
}
else
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_77, 1);
lean_inc(x_116);
lean_dec(x_77);
x_117 = !lean_is_exclusive(x_78);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_78, 0);
lean_dec(x_118);
x_119 = !lean_is_exclusive(x_79);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_79, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_80);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_80, 0);
lean_dec(x_122);
x_123 = !lean_is_exclusive(x_81);
if (x_123 == 0)
{
x_19 = x_78;
x_20 = x_116;
goto block_76;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_81, 0);
lean_inc(x_124);
lean_dec(x_81);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_80, 0, x_125);
x_19 = x_78;
x_20 = x_116;
goto block_76;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_80, 1);
lean_inc(x_126);
lean_dec(x_80);
x_127 = lean_ctor_get(x_81, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_128 = x_81;
} else {
 lean_dec_ref(x_81);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set(x_79, 0, x_130);
x_19 = x_78;
x_20 = x_116;
goto block_76;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = lean_ctor_get(x_79, 1);
lean_inc(x_131);
lean_dec(x_79);
x_132 = lean_ctor_get(x_80, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_133 = x_80;
} else {
 lean_dec_ref(x_80);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_81, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_135 = x_81;
} else {
 lean_dec_ref(x_81);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_134);
if (lean_is_scalar(x_133)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_133;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_132);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_131);
lean_ctor_set(x_78, 0, x_138);
x_19 = x_78;
x_20 = x_116;
goto block_76;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_139 = lean_ctor_get(x_78, 1);
lean_inc(x_139);
lean_dec(x_78);
x_140 = lean_ctor_get(x_79, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_141 = x_79;
} else {
 lean_dec_ref(x_79);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_80, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_143 = x_80;
} else {
 lean_dec_ref(x_80);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_81, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_145 = x_81;
} else {
 lean_dec_ref(x_81);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_144);
if (lean_is_scalar(x_143)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_143;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_142);
if (lean_is_scalar(x_141)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_141;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_140);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_139);
x_19 = x_149;
x_20 = x_116;
goto block_76;
}
}
}
else
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_77, 1);
lean_inc(x_150);
lean_dec(x_77);
x_151 = !lean_is_exclusive(x_78);
if (x_151 == 0)
{
x_19 = x_78;
x_20 = x_150;
goto block_76;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_78, 0);
x_153 = lean_ctor_get(x_78, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_78);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_19 = x_154;
x_20 = x_150;
goto block_76;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_1);
x_155 = !lean_is_exclusive(x_77);
if (x_155 == 0)
{
return x_77;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_77, 0);
x_157 = lean_ctor_get(x_77, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_77);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
block_76:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_22, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_20);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_37 = x_23;
} else {
 lean_dec_ref(x_23);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_21, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_20);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_43 = x_22;
} else {
 lean_dec_ref(x_22);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_23, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_45 = x_23;
} else {
 lean_dec_ref(x_23);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
lean_ctor_set(x_19, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_20);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_dec(x_19);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_52 = x_21;
} else {
 lean_dec_ref(x_21);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_54 = x_22;
} else {
 lean_dec_ref(x_22);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_23, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_56 = x_23;
} else {
 lean_dec_ref(x_23);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_20);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
lean_dec(x_19);
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
lean_dec(x_21);
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
lean_dec(x_22);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
lean_dec(x_23);
x_66 = 1;
x_67 = lean_usize_add(x_3, x_66);
x_68 = lean_array_uset(x_18, x_3, x_65);
x_3 = x_67;
x_4 = x_68;
x_6 = x_64;
x_7 = x_63;
x_8 = x_62;
x_9 = x_20;
goto _start;
}
}
else
{
uint8_t x_70; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_19);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_19);
lean_ctor_set(x_71, 1, x_20);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_19);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_20);
return x_75;
}
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("manifest out of date: ", 22);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("git revision", 12);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__3;
x_2 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" of dependency '", 16);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__5;
x_2 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' changed; ", 11);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` to update it", 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; 
x_10 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(x_1, x_2);
x_11 = l_instDecidableNot___rarg(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_17 = 1;
x_18 = l_Lean_Name_toString(x_3, x_17);
x_19 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__7;
x_20 = lean_string_append(x_19, x_18);
x_21 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__8;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__6;
x_24 = lean_string_append(x_23, x_18);
lean_dec(x_18);
x_25 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__9;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_22, x_26);
lean_dec(x_26);
x_28 = 2;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_push(x_8, x_29);
x_31 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("source kind (git/path)", 22);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__3;
x_2 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("git url", 7);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__3;
x_2 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__5;
x_2 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_25; 
x_25 = lean_usize_dec_lt(x_4, x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_10);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
x_31 = lean_array_uget(x_2, x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = l_Lean_RBNode_find___at_Lake_Workspace_updateAndMaterialize___spec__7(x_1, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_31);
x_34 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_8);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
x_11 = x_37;
x_12 = x_10;
goto block_24;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_dec(x_31);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec(x_38);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_32);
x_40 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_7);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_9);
x_11 = x_43;
x_12 = x_10;
goto block_24;
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_39);
x_44 = 1;
x_45 = l_Lean_Name_toString(x_32, x_44);
x_46 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__3;
x_47 = lean_string_append(x_46, x_45);
x_48 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__8;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__6;
x_51 = lean_string_append(x_50, x_45);
lean_dec(x_45);
x_52 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__9;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_49, x_53);
lean_dec(x_53);
x_55 = 2;
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = lean_array_push(x_9, x_56);
x_58 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_8);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
x_11 = x_61;
x_12 = x_10;
goto block_24;
}
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_33, 0);
lean_inc(x_62);
lean_dec(x_33);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_38);
x_63 = 1;
x_64 = l_Lean_Name_toString(x_32, x_63);
x_65 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__3;
x_66 = lean_string_append(x_65, x_64);
x_67 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__8;
x_68 = lean_string_append(x_66, x_67);
x_69 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__6;
x_70 = lean_string_append(x_69, x_64);
lean_dec(x_64);
x_71 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__9;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_string_append(x_68, x_72);
lean_dec(x_72);
x_74 = 2;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_array_push(x_9, x_75);
x_77 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2;
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_7);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_8);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
x_11 = x_80;
x_12 = x_10;
goto block_24;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; 
x_81 = lean_ctor_get(x_38, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
lean_dec(x_38);
x_83 = lean_ctor_get(x_62, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_62, 5);
lean_inc(x_84);
lean_dec(x_62);
x_85 = lean_string_dec_eq(x_81, x_83);
lean_dec(x_83);
lean_dec(x_81);
x_86 = l_instDecidableNot___rarg(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_box(0);
x_88 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1(x_82, x_84, x_32, x_87, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_84);
lean_dec(x_82);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_11 = x_89;
x_12 = x_90;
goto block_24;
}
else
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_91 = 1;
lean_inc(x_32);
x_92 = l_Lean_Name_toString(x_32, x_91);
x_93 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__6;
x_94 = lean_string_append(x_93, x_92);
x_95 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__8;
x_96 = lean_string_append(x_94, x_95);
x_97 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__6;
x_98 = lean_string_append(x_97, x_92);
lean_dec(x_92);
x_99 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__9;
x_100 = lean_string_append(x_98, x_99);
x_101 = lean_string_append(x_96, x_100);
lean_dec(x_100);
x_102 = 2;
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_102);
x_104 = lean_array_push(x_9, x_103);
x_105 = lean_box(0);
x_106 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1(x_82, x_84, x_32, x_105, x_6, x_7, x_8, x_104, x_10);
lean_dec(x_84);
lean_dec(x_82);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_11 = x_107;
x_12 = x_108;
goto block_24;
}
}
}
}
}
block_24:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_4 = x_22;
x_5 = x_20;
x_7 = x_19;
x_8 = x_18;
x_9 = x_17;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_List_reverse___rarg(x_5);
x_8 = l_List_reverse___rarg(x_6);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = l_List_reverse___rarg(x_9);
x_12 = l_List_reverse___rarg(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_name_eq(x_16, x_1);
if (x_20 == 0)
{
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_3, 0, x_2);
x_2 = x_17;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_3, 1, x_2);
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_name_eq(x_23, x_1);
if (x_27 == 0)
{
lean_object* x_28; 
lean_ctor_set(x_2, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_26);
x_2 = x_24;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_30; 
lean_ctor_set(x_2, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_2);
x_2 = x_24;
x_3 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_36 = x_3;
} else {
 lean_dec_ref(x_3);
 x_36 = lean_box(0);
}
x_37 = lean_name_eq(x_32, x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_34);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
x_2 = x_33;
x_3 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_35);
if (lean_is_scalar(x_36)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_36;
}
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_41);
x_2 = x_33;
x_3 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(x_1, x_3, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_9, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___lambda__1), 8, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_apply_7(x_1, x_2, x_12, x_11, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3___closed__1;
x_16 = l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__8(x_9, x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_14);
x_20 = l_List_appendTR___rarg(x_18, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_materializeDeps___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___at_Lake_Workspace_materializeDeps___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(x_2, x_1, x_7, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_11);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6(x_18, x_7);
x_20 = l_Lake_loadPackage___closed__2;
x_21 = l_String_intercalate(x_20, x_19);
x_22 = l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lake_loadPackage___lambda__3___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_get_size(x_16);
x_29 = lean_array_push(x_16, x_27);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_29);
lean_ctor_set(x_9, 0, x_28);
return x_8;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6(x_31, x_7);
x_33 = l_Lake_loadPackage___closed__2;
x_34 = l_String_intercalate(x_33, x_32);
x_35 = l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lake_loadPackage___lambda__3___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = 3;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_array_get_size(x_30);
x_42 = lean_array_push(x_30, x_40);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_8, 0, x_43);
return x_8;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_dec(x_8);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_46 = x_9;
} else {
 lean_dec_ref(x_9);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_12, 0);
lean_inc(x_47);
lean_dec(x_12);
x_48 = l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6(x_47, x_7);
x_49 = l_Lake_loadPackage___closed__2;
x_50 = l_String_intercalate(x_49, x_48);
x_51 = l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Lake_loadPackage___lambda__3___closed__1;
x_54 = lean_string_append(x_52, x_53);
x_55 = 3;
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = lean_array_get_size(x_45);
x_58 = lean_array_push(x_45, x_56);
if (lean_is_scalar(x_46)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_46;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_44);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_8);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_8, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_9);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_9, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_10);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_10, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_11);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_11, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_12, 0);
lean_inc(x_69);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_69);
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
lean_dec(x_11);
x_71 = lean_ctor_get(x_12, 0);
lean_inc(x_71);
lean_dec(x_12);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_10, 0, x_72);
return x_8;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_10, 1);
lean_inc(x_73);
lean_dec(x_10);
x_74 = lean_ctor_get(x_11, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_75 = x_11;
} else {
 lean_dec_ref(x_11);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_12, 0);
lean_inc(x_76);
lean_dec(x_12);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_9, 0, x_78);
return x_8;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_9, 1);
lean_inc(x_79);
lean_dec(x_9);
x_80 = lean_ctor_get(x_10, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_81 = x_10;
} else {
 lean_dec_ref(x_10);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_11, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_83 = x_11;
} else {
 lean_dec_ref(x_11);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_12, 0);
lean_inc(x_84);
lean_dec(x_12);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
if (lean_is_scalar(x_81)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_81;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_8, 0, x_87);
return x_8;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_88 = lean_ctor_get(x_8, 1);
lean_inc(x_88);
lean_dec(x_8);
x_89 = lean_ctor_get(x_9, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_90 = x_9;
} else {
 lean_dec_ref(x_9);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_10, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_92 = x_10;
} else {
 lean_dec_ref(x_10);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_11, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_94 = x_11;
} else {
 lean_dec_ref(x_11);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_12, 0);
lean_inc(x_95);
lean_dec(x_12);
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
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_88);
return x_99;
}
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_8);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_8, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_9);
if (x_102 == 0)
{
return x_8;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_9, 0);
x_104 = lean_ctor_get(x_9, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_9);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_8, 0, x_105);
return x_8;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_8, 1);
lean_inc(x_106);
lean_dec(x_8);
x_107 = lean_ctor_get(x_9, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_9, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_109 = x_9;
} else {
 lean_dec_ref(x_9);
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
x_112 = !lean_is_exclusive(x_8);
if (x_112 == 0)
{
return x_8;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_8, 0);
x_114 = lean_ctor_get(x_8, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_8);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_4, x_9, x_6);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at_Lake_Workspace_materializeDeps___spec__11(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_array_get_size(x_1);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_1);
lean_inc(x_7);
x_18 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_19, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_21, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_21, 0, x_33);
return x_18;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_36 = x_22;
} else {
 lean_dec_ref(x_22);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 1, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_20, 0, x_38);
return x_18;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
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
x_42 = lean_ctor_get(x_22, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_43 = x_22;
} else {
 lean_dec_ref(x_22);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_19, 0, x_46);
return x_18;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_dec(x_19);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_49 = x_20;
} else {
 lean_dec_ref(x_20);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_51 = x_21;
} else {
 lean_dec_ref(x_21);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_22, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_53 = x_22;
} else {
 lean_dec_ref(x_22);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
if (lean_is_scalar(x_49)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_49;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_48);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_47);
lean_ctor_set(x_18, 0, x_57);
return x_18;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_18, 1);
lean_inc(x_58);
lean_dec(x_18);
x_59 = lean_ctor_get(x_19, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_60 = x_19;
} else {
 lean_dec_ref(x_19);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_20, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_62 = x_20;
} else {
 lean_dec_ref(x_20);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_64 = x_21;
} else {
 lean_dec_ref(x_21);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_22, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_66 = x_22;
} else {
 lean_dec_ref(x_22);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_62;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_61);
if (lean_is_scalar(x_60)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_60;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_59);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_58);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_18, 1);
lean_inc(x_72);
lean_dec(x_18);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_dec(x_19);
x_74 = lean_ctor_get(x_20, 1);
lean_inc(x_74);
lean_dec(x_20);
x_75 = lean_ctor_get(x_21, 1);
lean_inc(x_75);
lean_dec(x_21);
x_76 = lean_ctor_get(x_22, 0);
lean_inc(x_76);
lean_dec(x_22);
x_77 = lean_array_get_size(x_76);
x_78 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_79 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__4(x_8, x_78, x_17, x_76, x_10, x_75, x_74, x_73, x_72);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec(x_7);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_79, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_80);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_80, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_81, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_82);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_82, 0);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_83);
if (x_92 == 0)
{
return x_79;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_83, 0);
lean_inc(x_93);
lean_dec(x_83);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_82, 0, x_94);
return x_79;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_82, 1);
lean_inc(x_95);
lean_dec(x_82);
x_96 = lean_ctor_get(x_83, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_97 = x_83;
} else {
 lean_dec_ref(x_83);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 1, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_81, 0, x_99);
return x_79;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get(x_81, 1);
lean_inc(x_100);
lean_dec(x_81);
x_101 = lean_ctor_get(x_82, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_102 = x_82;
} else {
 lean_dec_ref(x_82);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_83, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_104 = x_83;
} else {
 lean_dec_ref(x_83);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
if (lean_is_scalar(x_102)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_102;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_100);
lean_ctor_set(x_80, 0, x_107);
return x_79;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_108 = lean_ctor_get(x_80, 1);
lean_inc(x_108);
lean_dec(x_80);
x_109 = lean_ctor_get(x_81, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_110 = x_81;
} else {
 lean_dec_ref(x_81);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_82, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_112 = x_82;
} else {
 lean_dec_ref(x_82);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_83, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_114 = x_83;
} else {
 lean_dec_ref(x_83);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 1, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
if (lean_is_scalar(x_110)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_110;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_109);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_108);
lean_ctor_set(x_79, 0, x_118);
return x_79;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_119 = lean_ctor_get(x_79, 1);
lean_inc(x_119);
lean_dec(x_79);
x_120 = lean_ctor_get(x_80, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_121 = x_80;
} else {
 lean_dec_ref(x_80);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_81, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_123 = x_81;
} else {
 lean_dec_ref(x_81);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_82, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_125 = x_82;
} else {
 lean_dec_ref(x_82);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_83, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_127 = x_83;
} else {
 lean_dec_ref(x_83);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 1, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_126);
if (lean_is_scalar(x_125)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_125;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
if (lean_is_scalar(x_123)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_123;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_122);
if (lean_is_scalar(x_121)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_121;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_120);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_119);
return x_132;
}
}
else
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_79);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_79, 0);
lean_dec(x_134);
x_135 = !lean_is_exclusive(x_80);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_80, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_81);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_81, 1);
x_139 = lean_ctor_get(x_81, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_82);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_82, 0);
lean_dec(x_141);
x_142 = !lean_is_exclusive(x_83);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_143 = lean_ctor_get(x_83, 0);
x_144 = lean_ctor_get(x_7, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_7, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_7, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_7, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_7, 4);
lean_inc(x_148);
x_149 = lean_ctor_get(x_7, 5);
lean_inc(x_149);
x_150 = lean_ctor_get(x_7, 8);
lean_inc(x_150);
x_151 = lean_ctor_get(x_7, 9);
lean_inc(x_151);
x_152 = lean_ctor_get(x_7, 10);
lean_inc(x_152);
x_153 = lean_ctor_get(x_7, 11);
lean_inc(x_153);
x_154 = lean_ctor_get(x_7, 12);
lean_inc(x_154);
x_155 = lean_ctor_get(x_7, 13);
lean_inc(x_155);
x_156 = lean_ctor_get(x_7, 14);
lean_inc(x_156);
x_157 = lean_ctor_get(x_7, 15);
lean_inc(x_157);
x_158 = lean_ctor_get(x_7, 16);
lean_inc(x_158);
lean_dec(x_7);
x_159 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_159, 0, x_144);
lean_ctor_set(x_159, 1, x_145);
lean_ctor_set(x_159, 2, x_146);
lean_ctor_set(x_159, 3, x_147);
lean_ctor_set(x_159, 4, x_148);
lean_ctor_set(x_159, 5, x_149);
lean_ctor_set(x_159, 6, x_143);
lean_ctor_set(x_159, 7, x_1);
lean_ctor_set(x_159, 8, x_150);
lean_ctor_set(x_159, 9, x_151);
lean_ctor_set(x_159, 10, x_152);
lean_ctor_set(x_159, 11, x_153);
lean_ctor_set(x_159, 12, x_154);
lean_ctor_set(x_159, 13, x_155);
lean_ctor_set(x_159, 14, x_156);
lean_ctor_set(x_159, 15, x_157);
lean_ctor_set(x_159, 16, x_158);
lean_inc(x_159);
x_160 = l_Lake_Workspace_addPackage(x_159, x_138);
lean_ctor_set(x_83, 0, x_159);
lean_ctor_set(x_81, 1, x_160);
return x_79;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_161 = lean_ctor_get(x_83, 0);
lean_inc(x_161);
lean_dec(x_83);
x_162 = lean_ctor_get(x_7, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_7, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_7, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_7, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_7, 4);
lean_inc(x_166);
x_167 = lean_ctor_get(x_7, 5);
lean_inc(x_167);
x_168 = lean_ctor_get(x_7, 8);
lean_inc(x_168);
x_169 = lean_ctor_get(x_7, 9);
lean_inc(x_169);
x_170 = lean_ctor_get(x_7, 10);
lean_inc(x_170);
x_171 = lean_ctor_get(x_7, 11);
lean_inc(x_171);
x_172 = lean_ctor_get(x_7, 12);
lean_inc(x_172);
x_173 = lean_ctor_get(x_7, 13);
lean_inc(x_173);
x_174 = lean_ctor_get(x_7, 14);
lean_inc(x_174);
x_175 = lean_ctor_get(x_7, 15);
lean_inc(x_175);
x_176 = lean_ctor_get(x_7, 16);
lean_inc(x_176);
lean_dec(x_7);
x_177 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_177, 0, x_162);
lean_ctor_set(x_177, 1, x_163);
lean_ctor_set(x_177, 2, x_164);
lean_ctor_set(x_177, 3, x_165);
lean_ctor_set(x_177, 4, x_166);
lean_ctor_set(x_177, 5, x_167);
lean_ctor_set(x_177, 6, x_161);
lean_ctor_set(x_177, 7, x_1);
lean_ctor_set(x_177, 8, x_168);
lean_ctor_set(x_177, 9, x_169);
lean_ctor_set(x_177, 10, x_170);
lean_ctor_set(x_177, 11, x_171);
lean_ctor_set(x_177, 12, x_172);
lean_ctor_set(x_177, 13, x_173);
lean_ctor_set(x_177, 14, x_174);
lean_ctor_set(x_177, 15, x_175);
lean_ctor_set(x_177, 16, x_176);
lean_inc(x_177);
x_178 = l_Lake_Workspace_addPackage(x_177, x_138);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_82, 0, x_179);
lean_ctor_set(x_81, 1, x_178);
return x_79;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_180 = lean_ctor_get(x_82, 1);
lean_inc(x_180);
lean_dec(x_82);
x_181 = lean_ctor_get(x_83, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_182 = x_83;
} else {
 lean_dec_ref(x_83);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_7, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_7, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_7, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_7, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_7, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_7, 5);
lean_inc(x_188);
x_189 = lean_ctor_get(x_7, 8);
lean_inc(x_189);
x_190 = lean_ctor_get(x_7, 9);
lean_inc(x_190);
x_191 = lean_ctor_get(x_7, 10);
lean_inc(x_191);
x_192 = lean_ctor_get(x_7, 11);
lean_inc(x_192);
x_193 = lean_ctor_get(x_7, 12);
lean_inc(x_193);
x_194 = lean_ctor_get(x_7, 13);
lean_inc(x_194);
x_195 = lean_ctor_get(x_7, 14);
lean_inc(x_195);
x_196 = lean_ctor_get(x_7, 15);
lean_inc(x_196);
x_197 = lean_ctor_get(x_7, 16);
lean_inc(x_197);
lean_dec(x_7);
x_198 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_198, 0, x_183);
lean_ctor_set(x_198, 1, x_184);
lean_ctor_set(x_198, 2, x_185);
lean_ctor_set(x_198, 3, x_186);
lean_ctor_set(x_198, 4, x_187);
lean_ctor_set(x_198, 5, x_188);
lean_ctor_set(x_198, 6, x_181);
lean_ctor_set(x_198, 7, x_1);
lean_ctor_set(x_198, 8, x_189);
lean_ctor_set(x_198, 9, x_190);
lean_ctor_set(x_198, 10, x_191);
lean_ctor_set(x_198, 11, x_192);
lean_ctor_set(x_198, 12, x_193);
lean_ctor_set(x_198, 13, x_194);
lean_ctor_set(x_198, 14, x_195);
lean_ctor_set(x_198, 15, x_196);
lean_ctor_set(x_198, 16, x_197);
lean_inc(x_198);
x_199 = l_Lake_Workspace_addPackage(x_198, x_138);
if (lean_is_scalar(x_182)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_182;
}
lean_ctor_set(x_200, 0, x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_180);
lean_ctor_set(x_81, 1, x_199);
lean_ctor_set(x_81, 0, x_201);
return x_79;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_202 = lean_ctor_get(x_81, 1);
lean_inc(x_202);
lean_dec(x_81);
x_203 = lean_ctor_get(x_82, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_204 = x_82;
} else {
 lean_dec_ref(x_82);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_83, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_206 = x_83;
} else {
 lean_dec_ref(x_83);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_7, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_7, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_7, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_7, 3);
lean_inc(x_210);
x_211 = lean_ctor_get(x_7, 4);
lean_inc(x_211);
x_212 = lean_ctor_get(x_7, 5);
lean_inc(x_212);
x_213 = lean_ctor_get(x_7, 8);
lean_inc(x_213);
x_214 = lean_ctor_get(x_7, 9);
lean_inc(x_214);
x_215 = lean_ctor_get(x_7, 10);
lean_inc(x_215);
x_216 = lean_ctor_get(x_7, 11);
lean_inc(x_216);
x_217 = lean_ctor_get(x_7, 12);
lean_inc(x_217);
x_218 = lean_ctor_get(x_7, 13);
lean_inc(x_218);
x_219 = lean_ctor_get(x_7, 14);
lean_inc(x_219);
x_220 = lean_ctor_get(x_7, 15);
lean_inc(x_220);
x_221 = lean_ctor_get(x_7, 16);
lean_inc(x_221);
lean_dec(x_7);
x_222 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_222, 0, x_207);
lean_ctor_set(x_222, 1, x_208);
lean_ctor_set(x_222, 2, x_209);
lean_ctor_set(x_222, 3, x_210);
lean_ctor_set(x_222, 4, x_211);
lean_ctor_set(x_222, 5, x_212);
lean_ctor_set(x_222, 6, x_205);
lean_ctor_set(x_222, 7, x_1);
lean_ctor_set(x_222, 8, x_213);
lean_ctor_set(x_222, 9, x_214);
lean_ctor_set(x_222, 10, x_215);
lean_ctor_set(x_222, 11, x_216);
lean_ctor_set(x_222, 12, x_217);
lean_ctor_set(x_222, 13, x_218);
lean_ctor_set(x_222, 14, x_219);
lean_ctor_set(x_222, 15, x_220);
lean_ctor_set(x_222, 16, x_221);
lean_inc(x_222);
x_223 = l_Lake_Workspace_addPackage(x_222, x_202);
if (lean_is_scalar(x_206)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_206;
}
lean_ctor_set(x_224, 0, x_222);
if (lean_is_scalar(x_204)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_204;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_203);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_223);
lean_ctor_set(x_80, 0, x_226);
return x_79;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_227 = lean_ctor_get(x_80, 1);
lean_inc(x_227);
lean_dec(x_80);
x_228 = lean_ctor_get(x_81, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_229 = x_81;
} else {
 lean_dec_ref(x_81);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_82, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_231 = x_82;
} else {
 lean_dec_ref(x_82);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_83, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_233 = x_83;
} else {
 lean_dec_ref(x_83);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_7, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_7, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_7, 2);
lean_inc(x_236);
x_237 = lean_ctor_get(x_7, 3);
lean_inc(x_237);
x_238 = lean_ctor_get(x_7, 4);
lean_inc(x_238);
x_239 = lean_ctor_get(x_7, 5);
lean_inc(x_239);
x_240 = lean_ctor_get(x_7, 8);
lean_inc(x_240);
x_241 = lean_ctor_get(x_7, 9);
lean_inc(x_241);
x_242 = lean_ctor_get(x_7, 10);
lean_inc(x_242);
x_243 = lean_ctor_get(x_7, 11);
lean_inc(x_243);
x_244 = lean_ctor_get(x_7, 12);
lean_inc(x_244);
x_245 = lean_ctor_get(x_7, 13);
lean_inc(x_245);
x_246 = lean_ctor_get(x_7, 14);
lean_inc(x_246);
x_247 = lean_ctor_get(x_7, 15);
lean_inc(x_247);
x_248 = lean_ctor_get(x_7, 16);
lean_inc(x_248);
lean_dec(x_7);
x_249 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_249, 0, x_234);
lean_ctor_set(x_249, 1, x_235);
lean_ctor_set(x_249, 2, x_236);
lean_ctor_set(x_249, 3, x_237);
lean_ctor_set(x_249, 4, x_238);
lean_ctor_set(x_249, 5, x_239);
lean_ctor_set(x_249, 6, x_232);
lean_ctor_set(x_249, 7, x_1);
lean_ctor_set(x_249, 8, x_240);
lean_ctor_set(x_249, 9, x_241);
lean_ctor_set(x_249, 10, x_242);
lean_ctor_set(x_249, 11, x_243);
lean_ctor_set(x_249, 12, x_244);
lean_ctor_set(x_249, 13, x_245);
lean_ctor_set(x_249, 14, x_246);
lean_ctor_set(x_249, 15, x_247);
lean_ctor_set(x_249, 16, x_248);
lean_inc(x_249);
x_250 = l_Lake_Workspace_addPackage(x_249, x_228);
if (lean_is_scalar(x_233)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_233;
}
lean_ctor_set(x_251, 0, x_249);
if (lean_is_scalar(x_231)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_231;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_230);
if (lean_is_scalar(x_229)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_229;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_250);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_227);
lean_ctor_set(x_79, 0, x_254);
return x_79;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_255 = lean_ctor_get(x_79, 1);
lean_inc(x_255);
lean_dec(x_79);
x_256 = lean_ctor_get(x_80, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_257 = x_80;
} else {
 lean_dec_ref(x_80);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_81, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_259 = x_81;
} else {
 lean_dec_ref(x_81);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_82, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_261 = x_82;
} else {
 lean_dec_ref(x_82);
 x_261 = lean_box(0);
}
x_262 = lean_ctor_get(x_83, 0);
lean_inc(x_262);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_263 = x_83;
} else {
 lean_dec_ref(x_83);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_7, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_7, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_7, 2);
lean_inc(x_266);
x_267 = lean_ctor_get(x_7, 3);
lean_inc(x_267);
x_268 = lean_ctor_get(x_7, 4);
lean_inc(x_268);
x_269 = lean_ctor_get(x_7, 5);
lean_inc(x_269);
x_270 = lean_ctor_get(x_7, 8);
lean_inc(x_270);
x_271 = lean_ctor_get(x_7, 9);
lean_inc(x_271);
x_272 = lean_ctor_get(x_7, 10);
lean_inc(x_272);
x_273 = lean_ctor_get(x_7, 11);
lean_inc(x_273);
x_274 = lean_ctor_get(x_7, 12);
lean_inc(x_274);
x_275 = lean_ctor_get(x_7, 13);
lean_inc(x_275);
x_276 = lean_ctor_get(x_7, 14);
lean_inc(x_276);
x_277 = lean_ctor_get(x_7, 15);
lean_inc(x_277);
x_278 = lean_ctor_get(x_7, 16);
lean_inc(x_278);
lean_dec(x_7);
x_279 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_279, 0, x_264);
lean_ctor_set(x_279, 1, x_265);
lean_ctor_set(x_279, 2, x_266);
lean_ctor_set(x_279, 3, x_267);
lean_ctor_set(x_279, 4, x_268);
lean_ctor_set(x_279, 5, x_269);
lean_ctor_set(x_279, 6, x_262);
lean_ctor_set(x_279, 7, x_1);
lean_ctor_set(x_279, 8, x_270);
lean_ctor_set(x_279, 9, x_271);
lean_ctor_set(x_279, 10, x_272);
lean_ctor_set(x_279, 11, x_273);
lean_ctor_set(x_279, 12, x_274);
lean_ctor_set(x_279, 13, x_275);
lean_ctor_set(x_279, 14, x_276);
lean_ctor_set(x_279, 15, x_277);
lean_ctor_set(x_279, 16, x_278);
lean_inc(x_279);
x_280 = l_Lake_Workspace_addPackage(x_279, x_258);
if (lean_is_scalar(x_263)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_263;
}
lean_ctor_set(x_281, 0, x_279);
if (lean_is_scalar(x_261)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_261;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_260);
if (lean_is_scalar(x_259)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_259;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_280);
if (lean_is_scalar(x_257)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_257;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_256);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_255);
return x_285;
}
}
}
else
{
uint8_t x_286; 
lean_dec(x_7);
lean_dec(x_1);
x_286 = !lean_is_exclusive(x_79);
if (x_286 == 0)
{
lean_object* x_287; uint8_t x_288; 
x_287 = lean_ctor_get(x_79, 0);
lean_dec(x_287);
x_288 = !lean_is_exclusive(x_80);
if (x_288 == 0)
{
return x_79;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_80, 0);
x_290 = lean_ctor_get(x_80, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_80);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
lean_ctor_set(x_79, 0, x_291);
return x_79;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_292 = lean_ctor_get(x_79, 1);
lean_inc(x_292);
lean_dec(x_79);
x_293 = lean_ctor_get(x_80, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_80, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_295 = x_80;
} else {
 lean_dec_ref(x_80);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_292);
return x_297;
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_7);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_79);
if (x_298 == 0)
{
return x_79;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_79, 0);
x_300 = lean_ctor_get(x_79, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_79);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_18);
if (x_302 == 0)
{
lean_object* x_303; uint8_t x_304; 
x_303 = lean_ctor_get(x_18, 0);
lean_dec(x_303);
x_304 = !lean_is_exclusive(x_19);
if (x_304 == 0)
{
return x_18;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_19, 0);
x_306 = lean_ctor_get(x_19, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_19);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
lean_ctor_set(x_18, 0, x_307);
return x_18;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_308 = lean_ctor_get(x_18, 1);
lean_inc(x_308);
lean_dec(x_18);
x_309 = lean_ctor_get(x_19, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_19, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_311 = x_19;
} else {
 lean_dec_ref(x_19);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_308);
return x_313;
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_18);
if (x_314 == 0)
{
return x_18;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_18, 0);
x_316 = lean_ctor_get(x_18, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_18);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_box(0);
x_14 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5(x_2, x_1, x_11, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_apply_6(x_3, x_13, x_5, x_21, x_20, x_19, x_18);
return x_22;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("missing manifest; use `lake update` to generate one", 51);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___lambda__3___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_Workspace_materializeDeps___lambda__3___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_9);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 7);
lean_inc(x_16);
x_17 = lean_box(x_3);
lean_inc(x_7);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___lambda__1___boxed), 14, 8);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_6);
lean_closure_set(x_18, 6, x_1);
lean_closure_set(x_18, 7, x_7);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_name_eq(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_8);
x_23 = lean_box(0);
x_24 = l_Lake_Workspace_materializeDeps___lambda__1(x_16, x_2, x_3, x_4, x_5, x_6, x_1, x_7, x_23, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_4);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Array_isEmpty___rarg(x_8);
lean_dec(x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lake_Workspace_materializeDeps___lambda__2(x_16, x_6, x_18, x_26, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_16);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = l_Array_isEmpty___rarg(x_16);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_29 = lean_array_get_size(x_13);
x_30 = l_Lake_Workspace_materializeDeps___lambda__3___closed__2;
x_31 = lean_array_push(x_13, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_14);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Lake_Workspace_materializeDeps___lambda__2(x_16, x_6, x_18, x_34, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_16);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_11, 3);
lean_inc(x_16);
x_17 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_16, x_15);
lean_dec(x_15);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lake_Workspace_materializeDeps___lambda__3(x_7, x_1, x_2, x_3, x_4, x_5, x_8, x_6, x_18, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_11);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_12);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = lean_box(0);
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_array_get_size(x_47);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_lt(x_49, x_48);
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_51, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec(x_89);
x_52 = x_90;
goto block_88;
}
else
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_45, 0);
lean_inc(x_91);
lean_dec(x_45);
x_52 = x_91;
goto block_88;
}
block_44:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_14);
lean_ctor_set(x_8, 0, x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_11, 1);
x_19 = lean_ctor_get(x_11, 2);
x_20 = lean_ctor_get(x_11, 3);
x_21 = lean_ctor_get(x_11, 4);
x_22 = lean_ctor_get(x_11, 5);
x_23 = lean_ctor_get(x_11, 6);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_24 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_22);
lean_ctor_set(x_24, 6, x_23);
lean_ctor_set(x_8, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_11, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_11, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_11, 6);
lean_inc(x_33);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 lean_ctor_release(x_11, 6);
 x_34 = x_11;
} else {
 lean_dec_ref(x_11);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 7, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_31);
lean_ctor_set(x_35, 5, x_32);
lean_ctor_set(x_35, 6, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_9);
return x_43;
}
}
}
block_88:
{
lean_object* x_53; 
if (x_50 == 0)
{
lean_dec(x_48);
x_53 = x_46;
goto block_83;
}
else
{
uint8_t x_84; 
x_84 = lean_nat_dec_le(x_48, x_48);
if (x_84 == 0)
{
lean_dec(x_48);
x_53 = x_46;
goto block_83;
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; 
x_85 = 0;
x_86 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_87 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__10(x_47, x_85, x_86, x_46);
x_53 = x_87;
goto block_83;
}
}
block_83:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_box(x_4);
lean_inc(x_51);
x_55 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___lambda__4___boxed), 13, 6);
lean_closure_set(x_55, 0, x_3);
lean_closure_set(x_55, 1, x_54);
lean_closure_set(x_55, 2, x_51);
lean_closure_set(x_55, 3, x_52);
lean_closure_set(x_55, 4, x_53);
lean_closure_set(x_55, 5, x_47);
x_56 = l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___at_Lake_Workspace_materializeDeps___spec__6(x_51, x_55, x_46, x_2, x_6, x_7);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_57, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_dec(x_58);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 1);
lean_dec(x_65);
lean_ctor_set(x_59, 1, x_63);
lean_ctor_set(x_57, 0, x_59);
x_8 = x_57;
x_9 = x_60;
goto block_44;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set(x_57, 0, x_67);
x_8 = x_57;
x_9 = x_60;
goto block_44;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_57, 1);
lean_inc(x_68);
lean_dec(x_57);
x_69 = lean_ctor_get(x_58, 1);
lean_inc(x_69);
lean_dec(x_58);
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_71 = x_59;
} else {
 lean_dec_ref(x_59);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
x_8 = x_73;
x_9 = x_60;
goto block_44;
}
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
lean_dec(x_56);
x_75 = !lean_is_exclusive(x_57);
if (x_75 == 0)
{
x_8 = x_57;
x_9 = x_74;
goto block_44;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_57, 0);
x_77 = lean_ctor_get(x_57, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_57);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_8 = x_78;
x_9 = x_74;
goto block_44;
}
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_56);
if (x_79 == 0)
{
return x_56;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_56, 0);
x_81 = lean_ctor_get(x_56, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_56);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("manifest out of date: packages directory changed; ", 50);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("use `lake update` to rebuild the manifest (warning: this will update ALL workspace dependencies)", 96);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_materializeDeps___closed__1;
x_2 = l_Lake_Workspace_materializeDeps___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = l_Lake_Workspace_materializeDeps___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lake_mkRelPathString(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at_Lake_Workspace_materializeDeps___spec__11(x_9, x_14);
lean_dec(x_14);
lean_dec(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lake_Workspace_materializeDeps___closed__4;
x_17 = lean_array_push(x_5, x_16);
x_18 = lean_box(0);
x_19 = l_Lake_Workspace_materializeDeps___lambda__5(x_2, x_1, x_3, x_4, x_18, x_17, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lake_Workspace_materializeDeps___lambda__5(x_2, x_1, x_3, x_4, x_20, x_5, x_6);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lake_Workspace_materializeDeps___lambda__5(x_2, x_1, x_3, x_4, x_22, x_5, x_6);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_18 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3(x_1, x_15, x_3, x_4, x_5, x_6, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__8(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at_Lake_Workspace_materializeDeps___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_158____at_Lake_Workspace_materializeDeps___spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lake_Workspace_materializeDeps___lambda__1(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Workspace_materializeDeps___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lake_Workspace_materializeDeps___lambda__3(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lake_Workspace_materializeDeps___lambda__4(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lake_Workspace_materializeDeps___lambda__5(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lake_Workspace_materializeDeps(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_6 = lean_ctor_get(x_1, 5);
lean_inc(x_6);
x_7 = l_Lake_loadWorkspaceRoot(x_1, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
if (x_2 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_System_FilePath_join(x_14, x_15);
x_17 = l_Lake_Manifest_load_x3f(x_16, x_9);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_free_object(x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_NameSet_empty;
x_21 = l_Lake_Workspace_updateAndMaterialize(x_11, x_6, x_20, x_5, x_12, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Lake_Workspace_materializeDeps(x_11, x_23, x_6, x_5, x_12, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_12);
x_31 = lean_array_push(x_12, x_29);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_31);
lean_ctor_set(x_8, 0, x_30);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_8);
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_io_error_to_string(x_32);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_get_size(x_12);
x_38 = lean_array_push(x_12, x_36);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_38);
lean_ctor_set(x_8, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 4);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_System_FilePath_join(x_43, x_44);
x_46 = l_Lake_Manifest_load_x3f(x_45, x_9);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_NameSet_empty;
x_50 = l_Lake_Workspace_updateAndMaterialize(x_40, x_6, x_49, x_5, x_41, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = l_Lake_Workspace_materializeDeps(x_40, x_52, x_6, x_5, x_41, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_40);
lean_dec(x_6);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_56 = x_46;
} else {
 lean_dec_ref(x_46);
 x_56 = lean_box(0);
}
x_57 = lean_io_error_to_string(x_54);
x_58 = 3;
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_array_get_size(x_41);
x_61 = lean_array_push(x_41, x_59);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_56)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_56;
 lean_ctor_set_tag(x_63, 0);
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_7, 1);
lean_inc(x_64);
lean_dec(x_7);
x_65 = lean_ctor_get(x_8, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_8, 1);
lean_inc(x_66);
lean_dec(x_8);
x_67 = l_Lean_NameSet_empty;
x_68 = l_Lake_Workspace_updateAndMaterialize(x_65, x_6, x_67, x_5, x_66, x_64);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_6);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_7, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_8);
if (x_71 == 0)
{
return x_7;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_8, 0);
x_73 = lean_ctor_get(x_8, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_8);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_7, 0, x_74);
return x_7;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_7, 1);
lean_inc(x_75);
lean_dec(x_7);
x_76 = lean_ctor_get(x_8, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_8, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_78 = x_8;
} else {
 lean_dec_ref(x_8);
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
lean_dec(x_6);
x_81 = !lean_is_exclusive(x_7);
if (x_81 == 0)
{
return x_7;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_7, 0);
x_83 = lean_ctor_get(x_7, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_7);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_loadWorkspace(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_6 = lean_ctor_get(x_1, 5);
lean_inc(x_6);
x_7 = l_Lake_loadWorkspaceRoot(x_1, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lake_Workspace_updateAndMaterialize(x_10, x_6, x_2, x_5, x_11, x_9);
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
else
{
uint8_t x_44; 
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_7, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
return x_7;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_8, 0);
x_48 = lean_ctor_get(x_8, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_8);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_7, 0, x_49);
return x_7;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_dec(x_7);
x_51 = lean_ctor_get(x_8, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_53 = x_8;
} else {
 lean_dec_ref(x_8);
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
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_7);
if (x_56 == 0)
{
return x_7;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_7, 0);
x_58 = lean_ctor_get(x_7, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_7);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateManifest(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_EStateT(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_StoreInsts(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Topological(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Library(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Materialize(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Toml(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EStateT(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_StoreInsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Topological(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Library(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Materialize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Toml(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_loadLeanConfig___closed__1 = _init_l_Lake_loadLeanConfig___closed__1();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__1);
l_Lake_loadLeanConfig___closed__2 = _init_l_Lake_loadLeanConfig___closed__2();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__2);
l_Lake_loadLeanConfig___closed__3 = _init_l_Lake_loadLeanConfig___closed__3();
lean_mark_persistent(l_Lake_loadLeanConfig___closed__3);
l_Lake_configFileExists___closed__1 = _init_l_Lake_configFileExists___closed__1();
lean_mark_persistent(l_Lake_configFileExists___closed__1);
l_Lake_configFileExists___closed__2 = _init_l_Lake_configFileExists___closed__2();
lean_mark_persistent(l_Lake_configFileExists___closed__2);
l_Lake_loadPackage___lambda__2___closed__1 = _init_l_Lake_loadPackage___lambda__2___closed__1();
lean_mark_persistent(l_Lake_loadPackage___lambda__2___closed__1);
l_Lake_loadPackage___lambda__2___closed__2 = _init_l_Lake_loadPackage___lambda__2___closed__2();
lean_mark_persistent(l_Lake_loadPackage___lambda__2___closed__2);
l_Lake_loadPackage___lambda__3___closed__1 = _init_l_Lake_loadPackage___lambda__3___closed__1();
lean_mark_persistent(l_Lake_loadPackage___lambda__3___closed__1);
l_Lake_loadPackage___lambda__3___closed__2 = _init_l_Lake_loadPackage___lambda__3___closed__2();
lean_mark_persistent(l_Lake_loadPackage___lambda__3___closed__2);
l_Lake_loadPackage___closed__1 = _init_l_Lake_loadPackage___closed__1();
lean_mark_persistent(l_Lake_loadPackage___closed__1);
l_Lake_loadPackage___closed__2 = _init_l_Lake_loadPackage___closed__2();
lean_mark_persistent(l_Lake_loadPackage___closed__2);
l_Lake_loadPackage___closed__3 = _init_l_Lake_loadPackage___closed__3();
lean_mark_persistent(l_Lake_loadPackage___closed__3);
l_Lake_loadPackage___closed__4 = _init_l_Lake_loadPackage___closed__4();
lean_mark_persistent(l_Lake_loadPackage___closed__4);
l_Lake_loadPackage___closed__5 = _init_l_Lake_loadPackage___closed__5();
lean_mark_persistent(l_Lake_loadPackage___closed__5);
l_Lake_loadPackage___closed__6 = _init_l_Lake_loadPackage___closed__6();
lean_mark_persistent(l_Lake_loadPackage___closed__6);
l_Lake_loadWorkspaceRoot___closed__1 = _init_l_Lake_loadWorkspaceRoot___closed__1();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__1);
l_Lake_loadWorkspaceRoot___closed__2 = _init_l_Lake_loadWorkspaceRoot___closed__2();
lean_mark_persistent(l_Lake_loadWorkspaceRoot___closed__2);
l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3___closed__1 = _init_l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lake_recFetch___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__5___rarg___lambda__3___closed__1);
l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6___closed__1 = _init_l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___spec__6___closed__1);
l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1 = _init_l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lake_Load_Main_0__Lake_resolveDepsAcyclic___rarg___lambda__1___closed__1);
l_Lake_stdMismatchError___closed__1 = _init_l_Lake_stdMismatchError___closed__1();
lean_mark_persistent(l_Lake_stdMismatchError___closed__1);
l_Lake_stdMismatchError___closed__2 = _init_l_Lake_stdMismatchError___closed__2();
lean_mark_persistent(l_Lake_stdMismatchError___closed__2);
l_Lake_stdMismatchError___closed__3 = _init_l_Lake_stdMismatchError___closed__3();
lean_mark_persistent(l_Lake_stdMismatchError___closed__3);
l_Lake_stdMismatchError___closed__4 = _init_l_Lake_stdMismatchError___closed__4();
lean_mark_persistent(l_Lake_stdMismatchError___closed__4);
l_Lake_stdMismatchError___closed__5 = _init_l_Lake_stdMismatchError___closed__5();
lean_mark_persistent(l_Lake_stdMismatchError___closed__5);
l_Lake_stdMismatchError___closed__6 = _init_l_Lake_stdMismatchError___closed__6();
lean_mark_persistent(l_Lake_stdMismatchError___closed__6);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__9___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__2___closed__3);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__2);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__3);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___lambda__3___closed__4);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__2);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__11___closed__3);
l_Lake_Workspace_updateAndMaterialize___lambda__4___closed__1 = _init_l_Lake_Workspace_updateAndMaterialize___lambda__4___closed__1();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterialize___lambda__4___closed__1);
l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__1 = _init_l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__1();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__1);
l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__2 = _init_l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__2();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__2);
l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__3 = _init_l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__3();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterialize___lambda__5___closed__3);
l_Lake_Workspace_updateAndMaterialize___closed__1 = _init_l_Lake_Workspace_updateAndMaterialize___closed__1();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterialize___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__2);
l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__3);
l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__4);
l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__5);
l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__6);
l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__7 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___closed__7);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__5);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__6);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__7);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__8);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___lambda__1___closed__9);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__1);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__2);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__3);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__4);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__5);
l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lake_Workspace_materializeDeps___spec__5___closed__6);
l_Lake_Workspace_materializeDeps___lambda__3___closed__1 = _init_l_Lake_Workspace_materializeDeps___lambda__3___closed__1();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___lambda__3___closed__1);
l_Lake_Workspace_materializeDeps___lambda__3___closed__2 = _init_l_Lake_Workspace_materializeDeps___lambda__3___closed__2();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___lambda__3___closed__2);
l_Lake_Workspace_materializeDeps___closed__1 = _init_l_Lake_Workspace_materializeDeps___closed__1();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___closed__1);
l_Lake_Workspace_materializeDeps___closed__2 = _init_l_Lake_Workspace_materializeDeps___closed__2();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___closed__2);
l_Lake_Workspace_materializeDeps___closed__3 = _init_l_Lake_Workspace_materializeDeps___closed__3();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___closed__3);
l_Lake_Workspace_materializeDeps___closed__4 = _init_l_Lake_Workspace_materializeDeps___closed__4();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

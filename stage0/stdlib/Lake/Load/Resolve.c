// Lean compiler output
// Module: Lake.Load.Resolve
// Imports: Init Lake.Config.Monad Lake.Util.StoreInsts Lake.Build.Topological Lake.Load.Materialize Lake.Load.Package
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_reuseManifest___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_reuseManifest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__2(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_materializeDeps___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_resolveDeps___spec__1(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_updateDep___lambda__2___closed__1;
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_materializeDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_updateAndMaterialize___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_depCycleError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_materializeDeps___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_loadDepPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_reuseManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdMismatchError___boxed(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_saveToFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_updateDep___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11(lean_object*);
lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError(lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___closed__1;
static lean_object* l_Lake_updateDep___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_UpdateT_run(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10(lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_reuseManifest___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__6;
static lean_object* l_Lake_updateDep___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdMismatchError(lean_object*, lean_object*);
static lean_object* l_Lake_updateDep___lambda__4___closed__1;
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_Lake_updateDep___lambda__3___closed__1;
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateDep___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__2;
static lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_materializeDeps___spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_updateDep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_updateAndMaterialize___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_resolveDeps___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps(lean_object*);
static lean_object* l_Lake_updateDep___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_depCycleError___rarg___closed__3;
static lean_object* l_Lake_Workspace_materializeDeps___closed__2;
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_resolveDeps___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reuseManifest___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_reuseManifest___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reuseManifest___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_ResolveT_run___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_resolveDeps___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
extern lean_object* l_Lake_defaultLakeDir;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__1;
static lean_object* l_Lake_depCycleError___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_reuseManifest___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___rarg(lean_object*);
static lean_object* l_Lake_reuseManifest___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateDep___closed__1;
static lean_object* l_Lake_reuseManifest___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_RBNode_erase___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_UpdateT_run___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reuseManifest___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadDepPackage(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateAndMaterialize___closed__1;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8___boxed(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_validateManifest___closed__2;
LEAN_EXPORT lean_object* l_Lake_reuseManifest___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_depCycleError___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_reuseManifest___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_depCycleError___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__4;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_validateManifest___closed__1;
static lean_object* l_Lake_depCycleError___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ResolveT_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_reuseManifest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__14(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_updateDep___closed__3;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps___rarg___lambda__2(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__5;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_1, 18);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadDepPackage(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = 0;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_3);
x_18 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_2);
lean_ctor_set(x_18, 5, x_3);
lean_ctor_set(x_18, 6, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*7, x_4);
x_19 = l_Lake_loadPackageCore(x_11, x_18, x_6, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_21, 1);
lean_dec(x_28);
lean_ctor_set(x_21, 1, x_5);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_20, 0, x_30);
return x_19;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
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
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_40 = x_21;
} else {
 lean_dec_ref(x_21);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_5);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_dec(x_19);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_20, 1);
x_47 = lean_ctor_get(x_20, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_21, 0);
x_50 = lean_ctor_get(x_21, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_22, 0);
lean_inc(x_51);
lean_dec(x_22);
x_52 = l_Lake_Workspace_addFacetsFromEnv(x_51, x_3, x_5);
lean_dec(x_3);
x_53 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_52, x_44);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_ctor_set(x_21, 1, x_55);
lean_ctor_set(x_53, 0, x_20);
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
lean_ctor_set(x_21, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_20);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_free_object(x_21);
lean_dec(x_49);
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_53, 0);
x_61 = lean_io_error_to_string(x_60);
x_62 = 3;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_array_get_size(x_46);
x_65 = lean_array_push(x_46, x_63);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_65);
lean_ctor_set(x_20, 0, x_64);
lean_ctor_set_tag(x_53, 0);
lean_ctor_set(x_53, 0, x_20);
return x_53;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_53, 0);
x_67 = lean_ctor_get(x_53, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_53);
x_68 = lean_io_error_to_string(x_66);
x_69 = 3;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_array_get_size(x_46);
x_72 = lean_array_push(x_46, x_70);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_72);
lean_ctor_set(x_20, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_20);
lean_ctor_set(x_73, 1, x_67);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_21, 0);
lean_inc(x_74);
lean_dec(x_21);
x_75 = lean_ctor_get(x_22, 0);
lean_inc(x_75);
lean_dec(x_22);
x_76 = l_Lake_Workspace_addFacetsFromEnv(x_75, x_3, x_5);
lean_dec(x_3);
x_77 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_76, x_44);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
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
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set(x_20, 0, x_81);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_20);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_74);
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_85 = x_77;
} else {
 lean_dec_ref(x_77);
 x_85 = lean_box(0);
}
x_86 = lean_io_error_to_string(x_83);
x_87 = 3;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_array_get_size(x_46);
x_90 = lean_array_push(x_46, x_88);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_90);
lean_ctor_set(x_20, 0, x_89);
if (lean_is_scalar(x_85)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_85;
 lean_ctor_set_tag(x_91, 0);
}
lean_ctor_set(x_91, 0, x_20);
lean_ctor_set(x_91, 1, x_84);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_20, 1);
lean_inc(x_92);
lean_dec(x_20);
x_93 = lean_ctor_get(x_21, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_94 = x_21;
} else {
 lean_dec_ref(x_21);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_22, 0);
lean_inc(x_95);
lean_dec(x_22);
x_96 = l_Lake_Workspace_addFacetsFromEnv(x_95, x_3, x_5);
lean_dec(x_3);
x_97 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_96, x_44);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_94;
}
lean_ctor_set(x_101, 0, x_93);
lean_ctor_set(x_101, 1, x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_92);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_94);
lean_dec(x_93);
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_97, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_106 = x_97;
} else {
 lean_dec_ref(x_97);
 x_106 = lean_box(0);
}
x_107 = lean_io_error_to_string(x_104);
x_108 = 3;
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
x_110 = lean_array_get_size(x_92);
x_111 = lean_array_push(x_92, x_109);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
if (lean_is_scalar(x_106)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_106;
 lean_ctor_set_tag(x_113, 0);
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_105);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_5);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_19);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_19, 0);
lean_dec(x_115);
x_116 = !lean_is_exclusive(x_20);
if (x_116 == 0)
{
return x_19;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_20, 0);
x_118 = lean_ctor_get(x_20, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_20);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_19, 0, x_119);
return x_19;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_19, 1);
lean_inc(x_120);
lean_dec(x_19);
x_121 = lean_ctor_get(x_20, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_20, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_123 = x_20;
} else {
 lean_dec_ref(x_20);
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
lean_dec(x_5);
lean_dec(x_3);
x_126 = !lean_is_exclusive(x_19);
if (x_126 == 0)
{
return x_19;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_19, 0);
x_128 = lean_ctor_get(x_19, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_19);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadDepPackage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lake_loadDepPackage(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ResolveT_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ResolveT_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ResolveT_run___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lake_depCycleError___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  ", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_depCycleError___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = l_Lake_depCycleError___rarg___lambda__1___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_7 = lean_string_append(x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_depCycleError___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_depCycleError___rarg___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_depCycleError___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_depCycleError___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dependency cycle detected:\n", 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_box(0);
x_4 = l_Lake_depCycleError___rarg___closed__1;
x_5 = l_List_mapTR_loop___rarg(x_4, x_2, x_3);
x_6 = l_Lake_depCycleError___rarg___closed__2;
x_7 = l_String_intercalate(x_6, x_5);
x_8 = l_Lake_depCycleError___rarg___closed__3;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_depCycleError___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lake_depCycleError___rarg___lambda__1___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
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
x_18 = l_Lake_depCycleError___rarg___lambda__1___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__2(x_4, x_7);
x_9 = l_Lake_depCycleError___rarg___closed__2;
x_10 = l_String_intercalate(x_9, x_8);
x_11 = l_Lake_depCycleError___rarg___closed__3;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_6);
x_18 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg(x_1, x_2, lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_3 = l_StateT_instMonad___rarg(x_1);
x_4 = l_Lake_instMonadCallStackOfCallStackTOfMonad___rarg(x_3);
x_5 = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___rarg___lambda__1___boxed), 6, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_ctor_set(x_3, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_apply_2(x_2, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_9, x_6);
x_11 = lean_box(0);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_4, 0, x_11);
x_12 = lean_apply_2(x_1, lean_box(0), x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_14, x_16, x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_2, 0, x_19);
x_20 = lean_apply_2(x_1, lean_box(0), x_2);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_24, x_27, x_23);
x_29 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_25;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
x_32 = lean_apply_2(x_1, lean_box(0), x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_apply_4(x_1, x_2, x_3, x_8, x_9);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_4);
lean_inc(x_5);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_11);
x_13 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__2), 2, 1);
lean_closure_set(x_13, 0, x_4);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_apply_4(x_1, x_6, x_7, x_2, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": package requires itself (or a package with the same name)", 59);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__3___boxed), 9, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_name_eq(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_apply_2(x_4, lean_box(0), x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_20, 0, x_11);
lean_closure_set(x_20, 1, x_9);
x_21 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = 1;
x_23 = l_Lean_Name_toString(x_13, x_22);
x_24 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_apply_2(x_6, lean_box(0), x_27);
lean_inc(x_4);
x_29 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__5), 3, 2);
lean_closure_set(x_29, 0, x_10);
lean_closure_set(x_29, 1, x_4);
lean_inc(x_5);
x_30 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_28, x_29);
x_31 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_31, 0, x_8);
lean_closure_set(x_31, 1, x_4);
lean_inc(x_5);
x_32 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_30, x_31);
x_33 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_33, 0, x_11);
lean_closure_set(x_33, 1, x_9);
x_34 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_32, x_33);
return x_34;
}
}
}
static lean_object* _init_l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___boxed), 10, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_6);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1;
x_17 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2;
x_18 = l_Lake_RBNode_dFind___rarg(x_16, x_17, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_box(0);
lean_ctor_set(x_10, 0, x_19);
x_20 = lean_apply_2(x_4, lean_box(0), x_8);
x_21 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_21, 0, x_13);
lean_closure_set(x_21, 1, x_7);
x_22 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_23 = lean_box(0);
lean_ctor_set(x_10, 0, x_23);
x_24 = lean_apply_2(x_4, lean_box(0), x_8);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___boxed), 10, 6);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_3);
lean_closure_set(x_27, 3, x_4);
lean_closure_set(x_27, 4, x_5);
lean_closure_set(x_27, 5, x_6);
x_28 = lean_ctor_get(x_25, 3);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
lean_dec(x_3);
x_30 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1;
x_31 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2;
x_32 = l_Lake_RBNode_dFind___rarg(x_30, x_31, x_28, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_8, 0, x_34);
x_35 = lean_apply_2(x_4, lean_box(0), x_8);
x_36 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_36, 0, x_27);
lean_closure_set(x_36, 1, x_7);
x_37 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_35, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_5);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_8, 0, x_39);
x_40 = lean_apply_2(x_4, lean_box(0), x_8);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_8, 0);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_8);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_45 = x_41;
} else {
 lean_dec_ref(x_41);
 x_45 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___boxed), 10, 6);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_2);
lean_closure_set(x_46, 2, x_3);
lean_closure_set(x_46, 3, x_4);
lean_closure_set(x_46, 4, x_5);
lean_closure_set(x_46, 5, x_6);
x_47 = lean_ctor_get(x_43, 3);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
lean_dec(x_3);
x_49 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1;
x_50 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2;
x_51 = l_Lake_RBNode_dFind___rarg(x_49, x_50, x_47, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_45;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_44);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_42);
x_55 = lean_apply_2(x_4, lean_box(0), x_54);
x_56 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_56, 0, x_46);
lean_closure_set(x_56, 1, x_7);
x_57 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_55, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_5);
x_58 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_45;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_44);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_42);
x_61 = lean_apply_2(x_4, lean_box(0), x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_1);
lean_inc(x_2);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_12, x_13);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__7), 8, 7);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_1);
lean_closure_set(x_15, 4, x_2);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_9);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__8___boxed), 10, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_6);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = l_Lean_NameMap_contains___rarg(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_box(0);
lean_ctor_set(x_10, 0, x_16);
x_17 = lean_apply_2(x_1, lean_box(0), x_8);
x_18 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_7);
x_19 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
x_20 = lean_box(0);
lean_ctor_set(x_10, 0, x_20);
x_21 = lean_apply_2(x_1, lean_box(0), x_8);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__8___boxed), 10, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec(x_5);
x_26 = l_Lean_NameMap_contains___rarg(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_8, 0, x_28);
x_29 = lean_apply_2(x_1, lean_box(0), x_8);
x_30 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_30, 0, x_24);
lean_closure_set(x_30, 1, x_7);
x_31 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_29, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_8, 0, x_33);
x_34 = lean_apply_2(x_1, lean_box(0), x_8);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_8);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_40 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__8___boxed), 10, 6);
lean_closure_set(x_40, 0, x_1);
lean_closure_set(x_40, 1, x_2);
lean_closure_set(x_40, 2, x_3);
lean_closure_set(x_40, 3, x_4);
lean_closure_set(x_40, 4, x_5);
lean_closure_set(x_40, 5, x_6);
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
lean_dec(x_5);
x_42 = l_Lean_NameMap_contains___rarg(x_37, x_41);
lean_dec(x_41);
lean_dec(x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
x_46 = lean_apply_2(x_1, lean_box(0), x_45);
x_47 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_47, 0, x_40);
lean_closure_set(x_47, 1, x_7);
x_48 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_46, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_2);
x_49 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_39;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_38);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_36);
x_52 = lean_apply_2(x_1, lean_box(0), x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_inc(x_13);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__9), 8, 7);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_11);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_6);
lean_closure_set(x_16, 5, x_4);
lean_closure_set(x_16, 6, x_8);
x_17 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_7, x_1);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
x_9 = lean_apply_2(x_2, lean_box(0), x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_10, x_1);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_3, 0, x_13);
x_14 = lean_apply_2(x_2, lean_box(0), x_3);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_19 = x_15;
} else {
 lean_dec_ref(x_15);
 x_19 = lean_box(0);
}
x_20 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_17, x_1);
lean_dec(x_17);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_apply_2(x_2, lean_box(0), x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__12(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__13(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_2(x_1, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_2, 0, x_9);
x_10 = lean_apply_2(x_1, lean_box(0), x_2);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_15 = x_11;
} else {
 lean_dec_ref(x_11);
 x_15 = lean_box(0);
}
if (lean_is_scalar(x_15)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_15;
}
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = lean_apply_2(x_1, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1;
x_10 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2;
x_11 = l_Lake_RBNode_dFind___rarg(x_9, x_10, x_8, x_1);
lean_ctor_set(x_5, 0, x_11);
x_12 = lean_apply_2(x_2, lean_box(0), x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_ctor_get(x_13, 3);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1;
x_17 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2;
x_18 = l_Lake_RBNode_dFind___rarg(x_16, x_17, x_15, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_3, 0, x_19);
x_20 = lean_apply_2(x_2, lean_box(0), x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_23, 3);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1;
x_28 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2;
x_29 = l_Lake_RBNode_dFind___rarg(x_27, x_28, x_26, x_1);
if (lean_is_scalar(x_25)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_25;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
x_32 = lean_apply_2(x_2, lean_box(0), x_31);
return x_32;
}
}
}
static lean_object* _init_l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": impossible resolution state reached", 37);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = 1;
x_10 = l_Lean_Name_toString(x_1, x_9);
x_11 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
lean_inc(x_3);
x_16 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__5), 3, 2);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_3);
lean_inc(x_4);
x_17 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_3);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___boxed), 8, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
x_15 = lean_apply_2(x_3, lean_box(0), x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_5);
x_17 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
lean_inc(x_4);
lean_inc(x_3);
x_19 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___boxed), 8, 4);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_6, 0, x_21);
x_22 = lean_apply_2(x_3, lean_box(0), x_6);
x_23 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_5);
x_24 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_27 = x_7;
} else {
 lean_dec_ref(x_7);
 x_27 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_3);
x_28 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___boxed), 8, 4);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_4);
x_29 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
x_32 = lean_apply_2(x_3, lean_box(0), x_31);
x_33 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_33, 0, x_28);
lean_closure_set(x_33, 1, x_5);
x_34 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_32, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_6, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_7, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_39);
x_40 = lean_apply_2(x_3, lean_box(0), x_6);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_dec(x_7);
x_42 = lean_ctor_get(x_8, 0);
lean_inc(x_42);
lean_dec(x_8);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_6, 0, x_43);
x_44 = lean_apply_2(x_3, lean_box(0), x_6);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
lean_dec(x_6);
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
x_48 = lean_ctor_get(x_8, 0);
lean_inc(x_48);
lean_dec(x_8);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
x_51 = lean_apply_2(x_3, lean_box(0), x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__12), 2, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_2);
lean_inc(x_11);
x_12 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_10, x_11);
lean_inc(x_2);
lean_inc(x_11);
x_13 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_12, x_11);
lean_inc(x_2);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_13, x_11);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_1);
lean_inc(x_2);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_14, x_15);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__13), 2, 1);
lean_closure_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_16, x_17);
lean_inc(x_1);
lean_inc(x_3);
x_19 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__14), 3, 2);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_1);
lean_inc(x_2);
x_20 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_18, x_19);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__16), 6, 5);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_4);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_2);
lean_closure_set(x_21, 4, x_7);
x_22 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_4(x_1, x_2, x_9, x_3, x_8);
x_11 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__13), 2, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__17___boxed), 8, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
x_15 = lean_box(0);
lean_ctor_set(x_8, 0, x_15);
x_16 = lean_apply_2(x_1, lean_box(0), x_7);
x_17 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_5);
x_18 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__17___boxed), 8, 4);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_7, 0, x_22);
x_23 = lean_apply_2(x_1, lean_box(0), x_7);
x_24 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_24, 0, x_20);
lean_closure_set(x_24, 1, x_5);
x_25 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_28 = x_8;
} else {
 lean_dec_ref(x_8);
 x_28 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_29 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__17___boxed), 8, 4);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
x_30 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
x_33 = lean_apply_2(x_1, lean_box(0), x_32);
x_34 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_34, 0, x_29);
lean_closure_set(x_34, 1, x_5);
x_35 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_33, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_7, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_8, 1);
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_9, 0);
lean_inc(x_41);
lean_dec(x_9);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1;
x_45 = l_Lean_RBNode_erase___rarg(x_44, x_43, x_39);
x_46 = lean_box(0);
lean_ctor_set(x_8, 1, x_45);
lean_ctor_set(x_8, 0, x_46);
lean_inc(x_1);
x_47 = lean_apply_2(x_1, lean_box(0), x_7);
lean_inc(x_2);
x_48 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__18), 6, 5);
lean_closure_set(x_48, 0, x_6);
lean_closure_set(x_48, 1, x_41);
lean_closure_set(x_48, 2, x_5);
lean_closure_set(x_48, 3, x_1);
lean_closure_set(x_48, 4, x_2);
x_49 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_47, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_dec(x_8);
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
lean_dec(x_9);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1;
x_55 = l_Lean_RBNode_erase___rarg(x_54, x_53, x_50);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_7, 0, x_57);
lean_inc(x_1);
x_58 = lean_apply_2(x_1, lean_box(0), x_7);
lean_inc(x_2);
x_59 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__18), 6, 5);
lean_closure_set(x_59, 0, x_6);
lean_closure_set(x_59, 1, x_51);
lean_closure_set(x_59, 2, x_5);
lean_closure_set(x_59, 3, x_1);
lean_closure_set(x_59, 4, x_2);
x_60 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_58, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_ctor_get(x_7, 1);
lean_inc(x_61);
lean_dec(x_7);
x_62 = lean_ctor_get(x_8, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_63 = x_8;
} else {
 lean_dec_ref(x_8);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_ctor_get(x_64, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 2);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1;
x_68 = l_Lean_RBNode_erase___rarg(x_67, x_66, x_62);
x_69 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_61);
lean_inc(x_1);
x_72 = lean_apply_2(x_1, lean_box(0), x_71);
lean_inc(x_2);
x_73 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__18), 6, 5);
lean_closure_set(x_73, 0, x_6);
lean_closure_set(x_73, 1, x_64);
lean_closure_set(x_73, 2, x_5);
lean_closure_set(x_73, 3, x_1);
lean_closure_set(x_73, 4, x_2);
x_74 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_72, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_8);
lean_inc(x_12);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
lean_inc(x_12);
lean_inc(x_9);
x_15 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__11___boxed), 3, 2);
lean_closure_set(x_15, 0, x_9);
lean_closure_set(x_15, 1, x_12);
lean_inc(x_2);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_14, x_15);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__19), 7, 6);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_9);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_7);
lean_closure_set(x_17, 5, x_4);
x_18 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_1);
x_8 = lean_apply_2(x_2, lean_box(0), x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_3, 0, x_10);
x_11 = lean_apply_2(x_2, lean_box(0), x_3);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
if (lean_is_scalar(x_15)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_15;
}
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_apply_2(x_2, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get(x_1, 5);
x_17 = lean_ctor_get(x_1, 8);
x_18 = lean_ctor_get(x_1, 9);
x_19 = lean_ctor_get(x_1, 10);
x_20 = lean_ctor_get(x_1, 11);
x_21 = lean_ctor_get(x_1, 12);
x_22 = lean_ctor_get(x_1, 13);
x_23 = lean_ctor_get(x_1, 14);
x_24 = lean_ctor_get(x_1, 15);
x_25 = lean_ctor_get(x_1, 16);
x_26 = lean_ctor_get(x_1, 17);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_27 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 2, x_13);
lean_ctor_set(x_27, 3, x_14);
lean_ctor_set(x_27, 4, x_15);
lean_ctor_set(x_27, 5, x_16);
lean_ctor_set(x_27, 6, x_9);
lean_ctor_set(x_27, 7, x_2);
lean_ctor_set(x_27, 8, x_17);
lean_ctor_set(x_27, 9, x_18);
lean_ctor_set(x_27, 10, x_19);
lean_ctor_set(x_27, 11, x_20);
lean_ctor_set(x_27, 12, x_21);
lean_ctor_set(x_27, 13, x_22);
lean_ctor_set(x_27, 14, x_23);
lean_ctor_set(x_27, 15, x_24);
lean_ctor_set(x_27, 16, x_25);
lean_ctor_set(x_27, 17, x_26);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_27);
x_30 = l_Lake_Workspace_addPackage(x_27, x_7);
x_31 = lean_box(0);
lean_ctor_set(x_6, 1, x_30);
lean_ctor_set(x_6, 0, x_31);
lean_inc(x_29);
x_32 = lean_apply_2(x_29, lean_box(0), x_6);
lean_inc(x_29);
x_33 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_33, 0, x_10);
lean_closure_set(x_33, 1, x_29);
lean_inc(x_4);
x_34 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_32, x_33);
x_35 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__21), 3, 2);
lean_closure_set(x_35, 0, x_27);
lean_closure_set(x_35, 1, x_29);
x_36 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_34, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_37 = lean_ctor_get(x_6, 0);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 2);
x_42 = lean_ctor_get(x_1, 3);
x_43 = lean_ctor_get(x_1, 4);
x_44 = lean_ctor_get(x_1, 5);
x_45 = lean_ctor_get(x_1, 8);
x_46 = lean_ctor_get(x_1, 9);
x_47 = lean_ctor_get(x_1, 10);
x_48 = lean_ctor_get(x_1, 11);
x_49 = lean_ctor_get(x_1, 12);
x_50 = lean_ctor_get(x_1, 13);
x_51 = lean_ctor_get(x_1, 14);
x_52 = lean_ctor_get(x_1, 15);
x_53 = lean_ctor_get(x_1, 16);
x_54 = lean_ctor_get(x_1, 17);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
x_55 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 2, x_41);
lean_ctor_set(x_55, 3, x_42);
lean_ctor_set(x_55, 4, x_43);
lean_ctor_set(x_55, 5, x_44);
lean_ctor_set(x_55, 6, x_37);
lean_ctor_set(x_55, 7, x_2);
lean_ctor_set(x_55, 8, x_45);
lean_ctor_set(x_55, 9, x_46);
lean_ctor_set(x_55, 10, x_47);
lean_ctor_set(x_55, 11, x_48);
lean_ctor_set(x_55, 12, x_49);
lean_ctor_set(x_55, 13, x_50);
lean_ctor_set(x_55, 14, x_51);
lean_ctor_set(x_55, 15, x_52);
lean_ctor_set(x_55, 16, x_53);
lean_ctor_set(x_55, 17, x_54);
x_56 = lean_ctor_get(x_3, 0);
lean_inc(x_56);
lean_dec(x_3);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_55);
x_58 = l_Lake_Workspace_addPackage(x_55, x_7);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
lean_inc(x_57);
x_61 = lean_apply_2(x_57, lean_box(0), x_60);
lean_inc(x_57);
x_62 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_62, 0, x_38);
lean_closure_set(x_62, 1, x_57);
lean_inc(x_4);
x_63 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_61, x_62);
x_64 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__21), 3, 2);
lean_closure_set(x_64, 0, x_55);
lean_closure_set(x_64, 1, x_57);
x_65 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_63, x_64);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__20), 8, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
x_15 = lean_usize_of_nat(x_5);
x_16 = 0;
lean_inc(x_7);
x_17 = l_Array_mapMUnsafe_map___rarg(x_6, x_14, x_15, x_16, x_7);
x_18 = lean_apply_3(x_17, x_13, x_8, x_12);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__22___boxed), 5, 4);
lean_closure_set(x_19, 0, x_9);
lean_closure_set(x_19, 1, x_7);
lean_closure_set(x_19, 2, x_1);
lean_closure_set(x_19, 3, x_2);
x_20 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
x_9 = l_StateT_instMonad___rarg(x_1);
x_10 = l_ReaderT_instMonad___rarg(x_9);
x_11 = l_StateT_instMonad___rarg(x_10);
x_12 = lean_ctor_get(x_4, 7);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__10___boxed), 9, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_13);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_13);
lean_inc(x_17);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__23___boxed), 10, 9);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_5);
lean_closure_set(x_18, 4, x_13);
lean_closure_set(x_18, 5, x_11);
lean_closure_set(x_18, 6, x_12);
lean_closure_set(x_18, 7, x_7);
lean_closure_set(x_18, 8, x_4);
if (x_16 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_8);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
x_25 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_24, x_18);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_13, x_13);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_8);
x_32 = lean_apply_2(x_30, lean_box(0), x_31);
x_33 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_32, x_18);
return x_33;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_34 = 0;
x_35 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_36 = lean_box(0);
x_37 = l_Array_foldlMUnsafe_fold___rarg(x_11, x_14, x_12, x_34, x_35, x_36);
x_38 = lean_apply_3(x_37, x_6, x_7, x_8);
x_39 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_38, x_18);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__11(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__22(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___rarg___lambda__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Lean_Name_quickCmp(x_1, x_6);
switch (x_9) {
case 0:
{
uint8_t x_10; 
x_10 = l_Lean_RBNode_isBlack___rarg(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(x_1, x_5);
x_12 = 0;
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(x_1, x_5);
x_14 = l_Lean_RBNode_balLeft___rarg(x_13, x_6, x_7, x_8);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_15 = l_Lean_RBNode_appendTrees___rarg(x_5, x_8);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___rarg(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(x_1, x_8);
x_18 = 0;
lean_ctor_set(x_2, 3, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(x_1, x_8);
x_20 = l_Lean_RBNode_balRight___rarg(x_5, x_6, x_7, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_25 = l_Lean_Name_quickCmp(x_1, x_22);
switch (x_25) {
case 0:
{
uint8_t x_26; 
x_26 = l_Lean_RBNode_isBlack___rarg(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(x_1, x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(x_1, x_21);
x_31 = l_Lean_RBNode_balLeft___rarg(x_30, x_22, x_23, x_24);
return x_31;
}
}
case 1:
{
lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_22);
x_32 = l_Lean_RBNode_appendTrees___rarg(x_21, x_24);
return x_32;
}
default: 
{
uint8_t x_33; 
x_33 = l_Lean_RBNode_isBlack___rarg(x_24);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(x_1, x_24);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(x_1, x_24);
x_38 = l_Lean_RBNode_balRight___rarg(x_21, x_22, x_23, x_37);
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_8, x_1);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_9);
x_10 = lean_apply_2(x_2, lean_box(0), x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_13, x_1);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_apply_2(x_2, lean_box(0), x_3);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_19, 3);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_22, x_1);
lean_dec(x_22);
if (lean_is_scalar(x_21)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_21;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
x_26 = lean_apply_2(x_2, lean_box(0), x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__12), 2, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_2);
lean_inc(x_11);
x_12 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_10, x_11);
lean_inc(x_2);
lean_inc(x_11);
x_13 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_12, x_11);
lean_inc(x_2);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_13, x_11);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_1);
lean_inc(x_2);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_14, x_15);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__13), 2, 1);
lean_closure_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_16, x_17);
lean_inc(x_1);
lean_inc(x_3);
x_19 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_1);
lean_inc(x_2);
x_20 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_18, x_19);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__16), 6, 5);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_4);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_2);
lean_closure_set(x_21, 4, x_7);
x_22 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2___boxed), 8, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
x_16 = lean_box(0);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_apply_2(x_1, lean_box(0), x_8);
x_18 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_5);
x_19 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2___boxed), 8, 4);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_4);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_8, 0, x_23);
x_24 = lean_apply_2(x_1, lean_box(0), x_8);
x_25 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_25, 0, x_21);
lean_closure_set(x_25, 1, x_5);
x_26 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_29 = x_9;
} else {
 lean_dec_ref(x_9);
 x_29 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_30 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2___boxed), 8, 4);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_3);
lean_closure_set(x_30, 3, x_4);
x_31 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
x_34 = lean_apply_2(x_1, lean_box(0), x_33);
x_35 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_35, 0, x_30);
lean_closure_set(x_35, 1, x_5);
x_36 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_34, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_8, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
lean_dec(x_10);
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_44, x_40);
lean_dec(x_44);
x_46 = lean_box(0);
lean_ctor_set(x_9, 1, x_45);
lean_ctor_set(x_9, 0, x_46);
lean_inc(x_1);
x_47 = lean_apply_2(x_1, lean_box(0), x_8);
lean_inc(x_2);
x_48 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__18), 6, 5);
lean_closure_set(x_48, 0, x_6);
lean_closure_set(x_48, 1, x_42);
lean_closure_set(x_48, 2, x_7);
lean_closure_set(x_48, 3, x_1);
lean_closure_set(x_48, 4, x_2);
x_49 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_47, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_9, 1);
lean_inc(x_50);
lean_dec(x_9);
x_51 = lean_ctor_get(x_10, 0);
lean_inc(x_51);
lean_dec(x_10);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_53, x_50);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_8, 0, x_56);
lean_inc(x_1);
x_57 = lean_apply_2(x_1, lean_box(0), x_8);
lean_inc(x_2);
x_58 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__18), 6, 5);
lean_closure_set(x_58, 0, x_6);
lean_closure_set(x_58, 1, x_51);
lean_closure_set(x_58, 2, x_7);
lean_closure_set(x_58, 3, x_1);
lean_closure_set(x_58, 4, x_2);
x_59 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_57, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_8, 1);
lean_inc(x_60);
lean_dec(x_8);
x_61 = lean_ctor_get(x_9, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_62 = x_9;
} else {
 lean_dec_ref(x_9);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_10, 0);
lean_inc(x_63);
lean_dec(x_10);
x_64 = lean_ctor_get(x_63, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 2);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_65, x_61);
lean_dec(x_65);
x_67 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_60);
lean_inc(x_1);
x_70 = lean_apply_2(x_1, lean_box(0), x_69);
lean_inc(x_2);
x_71 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__18), 6, 5);
lean_closure_set(x_71, 0, x_6);
lean_closure_set(x_71, 1, x_63);
lean_closure_set(x_71, 2, x_7);
lean_closure_set(x_71, 3, x_1);
lean_closure_set(x_71, 4, x_2);
x_72 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_70, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = 1;
x_16 = lean_usize_add(x_1, x_15);
x_17 = lean_array_uset(x_2, x_1, x_13);
x_18 = l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_16, x_17, x_14, x_9, x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_7, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_11);
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_18 = lean_array_uget(x_8, x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_8, x_7, x_19);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
lean_inc(x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_9);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_11);
lean_inc(x_25);
x_27 = lean_apply_2(x_25, lean_box(0), x_26);
lean_inc(x_25);
lean_inc(x_22);
x_28 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__11___boxed), 3, 2);
lean_closure_set(x_28, 0, x_22);
lean_closure_set(x_28, 1, x_25);
lean_inc(x_5);
x_29 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_27, x_28);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_5);
x_30 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__3), 8, 7);
lean_closure_set(x_30, 0, x_25);
lean_closure_set(x_30, 1, x_5);
lean_closure_set(x_30, 2, x_22);
lean_closure_set(x_30, 3, x_2);
lean_closure_set(x_30, 4, x_10);
lean_closure_set(x_30, 5, x_3);
lean_closure_set(x_30, 6, x_4);
lean_inc(x_5);
x_31 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_29, x_30);
x_32 = lean_box_usize(x_7);
x_33 = lean_box_usize(x_6);
x_34 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__4___boxed), 10, 9);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_20);
lean_closure_set(x_34, 2, x_1);
lean_closure_set(x_34, 3, x_2);
lean_closure_set(x_34, 4, x_3);
lean_closure_set(x_34, 5, x_4);
lean_closure_set(x_34, 6, x_5);
lean_closure_set(x_34, 7, x_33);
lean_closure_set(x_34, 8, x_10);
x_35 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_31, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___boxed), 10, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_6);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_box(0);
lean_ctor_set(x_10, 0, x_17);
x_18 = lean_apply_2(x_4, lean_box(0), x_8);
x_19 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_7);
x_20 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_21 = lean_box(0);
lean_ctor_set(x_10, 0, x_21);
x_22 = lean_apply_2(x_4, lean_box(0), x_8);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___boxed), 10, 6);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_5);
lean_closure_set(x_25, 5, x_6);
x_26 = lean_ctor_get(x_23, 3);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
lean_dec(x_3);
x_28 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_8, 0, x_30);
x_31 = lean_apply_2(x_4, lean_box(0), x_8);
x_32 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_32, 0, x_25);
lean_closure_set(x_32, 1, x_7);
x_33 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_31, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_5);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_8, 0, x_35);
x_36 = lean_apply_2(x_4, lean_box(0), x_8);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___boxed), 10, 6);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_2);
lean_closure_set(x_42, 2, x_3);
lean_closure_set(x_42, 3, x_4);
lean_closure_set(x_42, 4, x_5);
lean_closure_set(x_42, 5, x_6);
x_43 = lean_ctor_get(x_39, 3);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
lean_dec(x_3);
x_45 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_41;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_38);
x_49 = lean_apply_2(x_4, lean_box(0), x_48);
x_50 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_50, 0, x_42);
lean_closure_set(x_50, 1, x_7);
x_51 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_49, x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_5);
x_52 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_41;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_38);
x_55 = lean_apply_2(x_4, lean_box(0), x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_1);
lean_inc(x_2);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_12, x_13);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__1), 8, 7);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_1);
lean_closure_set(x_15, 4, x_2);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_9);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__2___boxed), 10, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_6);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = l_Lean_NameMap_contains___rarg(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_box(0);
lean_ctor_set(x_10, 0, x_16);
x_17 = lean_apply_2(x_1, lean_box(0), x_8);
x_18 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_7);
x_19 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
x_20 = lean_box(0);
lean_ctor_set(x_10, 0, x_20);
x_21 = lean_apply_2(x_1, lean_box(0), x_8);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__2___boxed), 10, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec(x_5);
x_26 = l_Lean_NameMap_contains___rarg(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_8, 0, x_28);
x_29 = lean_apply_2(x_1, lean_box(0), x_8);
x_30 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_30, 0, x_24);
lean_closure_set(x_30, 1, x_7);
x_31 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_29, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_8, 0, x_33);
x_34 = lean_apply_2(x_1, lean_box(0), x_8);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_8);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_40 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__2___boxed), 10, 6);
lean_closure_set(x_40, 0, x_1);
lean_closure_set(x_40, 1, x_2);
lean_closure_set(x_40, 2, x_3);
lean_closure_set(x_40, 3, x_4);
lean_closure_set(x_40, 4, x_5);
lean_closure_set(x_40, 5, x_6);
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
lean_dec(x_5);
x_42 = l_Lean_NameMap_contains___rarg(x_37, x_41);
lean_dec(x_41);
lean_dec(x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
x_46 = lean_apply_2(x_1, lean_box(0), x_45);
x_47 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_47, 0, x_40);
lean_closure_set(x_47, 1, x_7);
x_48 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_46, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_2);
x_49 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_39;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_38);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_36);
x_52 = lean_apply_2(x_1, lean_box(0), x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_1, x_14);
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg(x_2, x_3, x_4, x_5, x_6, x_15, x_7, x_12, x_13, x_8, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_6, x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
x_13 = lean_array_uget(x_5, x_6);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_11);
lean_inc(x_17);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_14);
x_20 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__3), 8, 7);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_13);
lean_closure_set(x_20, 5, x_2);
lean_closure_set(x_20, 6, x_10);
lean_inc(x_14);
x_21 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_19, x_20);
x_22 = lean_box_usize(x_6);
x_23 = lean_box_usize(x_7);
x_24 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__4___boxed), 9, 8);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_4);
lean_closure_set(x_24, 5, x_5);
lean_closure_set(x_24, 6, x_23);
lean_closure_set(x_24, 7, x_10);
x_25 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_21, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_9);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_11);
x_30 = lean_apply_2(x_28, lean_box(0), x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_usize_of_nat(x_1);
x_15 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_16 = l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg(x_2, x_3, x_4, x_5, x_6, x_14, x_15, x_7, x_13, x_8, x_12);
lean_inc(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__22___boxed), 5, 4);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_7);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_6);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_6, 7);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_10);
lean_inc(x_14);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___rarg___lambda__1___boxed), 10, 9);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_14);
lean_closure_set(x_15, 6, x_10);
lean_closure_set(x_15, 7, x_8);
lean_closure_set(x_15, 8, x_6);
if (x_13 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_9);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
x_22 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_21, x_15);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_11, x_11);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_9);
x_29 = lean_apply_2(x_27, lean_box(0), x_28);
x_30 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_29, x_15);
return x_30;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_33 = lean_box(0);
x_34 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg(x_1, x_2, x_3, x_6, x_10, x_31, x_32, x_33, x_7, x_8, x_9);
x_35 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_34, x_15);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_resolveDeps___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__2(x_4, x_7);
x_9 = l_Lake_depCycleError___rarg___closed__2;
x_10 = l_String_intercalate(x_9, x_8);
x_11 = l_Lake_depCycleError___rarg___closed__3;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_6);
x_18 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg(x_1, x_2, x_3, x_4, x_11, x_5, x_10);
x_13 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__13), 2, 1);
lean_closure_set(x_13, 0, x_6);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2___boxed), 8, 4);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
x_18 = lean_box(0);
lean_ctor_set(x_11, 0, x_18);
x_19 = lean_apply_2(x_1, lean_box(0), x_10);
x_20 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_5);
x_21 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2___boxed), 8, 4);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_10, 0, x_25);
x_26 = lean_apply_2(x_1, lean_box(0), x_10);
x_27 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_27, 0, x_23);
lean_closure_set(x_27, 1, x_5);
x_28 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_26, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_31 = x_11;
} else {
 lean_dec_ref(x_11);
 x_31 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_32 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2___boxed), 8, 4);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_2);
lean_closure_set(x_32, 2, x_3);
lean_closure_set(x_32, 3, x_4);
x_33 = lean_box(0);
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
x_36 = lean_apply_2(x_1, lean_box(0), x_35);
x_37 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_37, 0, x_32);
lean_closure_set(x_37, 1, x_5);
x_38 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_36, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_10, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_11, 1);
x_43 = lean_ctor_get(x_11, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_12, 0);
lean_inc(x_44);
lean_dec(x_12);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 2);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_46, x_42);
lean_dec(x_46);
x_48 = lean_box(0);
lean_ctor_set(x_11, 1, x_47);
lean_ctor_set(x_11, 0, x_48);
lean_inc(x_1);
x_49 = lean_apply_2(x_1, lean_box(0), x_10);
lean_inc(x_2);
x_50 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__1), 8, 7);
lean_closure_set(x_50, 0, x_6);
lean_closure_set(x_50, 1, x_7);
lean_closure_set(x_50, 2, x_8);
lean_closure_set(x_50, 3, x_44);
lean_closure_set(x_50, 4, x_9);
lean_closure_set(x_50, 5, x_1);
lean_closure_set(x_50, 6, x_2);
x_51 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_49, x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_11, 1);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_ctor_get(x_12, 0);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_ctor_get(x_53, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 2);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_55, x_52);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_10, 0, x_58);
lean_inc(x_1);
x_59 = lean_apply_2(x_1, lean_box(0), x_10);
lean_inc(x_2);
x_60 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__1), 8, 7);
lean_closure_set(x_60, 0, x_6);
lean_closure_set(x_60, 1, x_7);
lean_closure_set(x_60, 2, x_8);
lean_closure_set(x_60, 3, x_53);
lean_closure_set(x_60, 4, x_9);
lean_closure_set(x_60, 5, x_1);
lean_closure_set(x_60, 6, x_2);
x_61 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_59, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_10, 1);
lean_inc(x_62);
lean_dec(x_10);
x_63 = lean_ctor_get(x_11, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_64 = x_11;
} else {
 lean_dec_ref(x_11);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_12, 0);
lean_inc(x_65);
lean_dec(x_12);
x_66 = lean_ctor_get(x_65, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 2);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_67, x_63);
lean_dec(x_67);
x_69 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_62);
lean_inc(x_1);
x_72 = lean_apply_2(x_1, lean_box(0), x_71);
lean_inc(x_2);
x_73 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__1), 8, 7);
lean_closure_set(x_73, 0, x_6);
lean_closure_set(x_73, 1, x_7);
lean_closure_set(x_73, 2, x_8);
lean_closure_set(x_73, 3, x_65);
lean_closure_set(x_73, 4, x_9);
lean_closure_set(x_73, 5, x_1);
lean_closure_set(x_73, 6, x_2);
x_74 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_72, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = 1;
x_18 = lean_usize_add(x_1, x_17);
x_19 = lean_array_uset(x_2, x_1, x_15);
x_20 = l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18, x_19, x_16, x_11, x_14);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_9, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_13);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_array_uget(x_10, x_9);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_uset(x_10, x_9, x_21);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
lean_inc(x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_11);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_13);
lean_inc(x_27);
x_29 = lean_apply_2(x_27, lean_box(0), x_28);
lean_inc(x_27);
lean_inc(x_24);
x_30 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__11___boxed), 3, 2);
lean_closure_set(x_30, 0, x_24);
lean_closure_set(x_30, 1, x_27);
lean_inc(x_4);
x_31 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_29, x_30);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_4);
x_32 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__2), 10, 9);
lean_closure_set(x_32, 0, x_27);
lean_closure_set(x_32, 1, x_4);
lean_closure_set(x_32, 2, x_24);
lean_closure_set(x_32, 3, x_6);
lean_closure_set(x_32, 4, x_12);
lean_closure_set(x_32, 5, x_1);
lean_closure_set(x_32, 6, x_2);
lean_closure_set(x_32, 7, x_3);
lean_closure_set(x_32, 8, x_7);
lean_inc(x_4);
x_33 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_31, x_32);
x_34 = lean_box_usize(x_9);
x_35 = lean_box_usize(x_8);
x_36 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__3___boxed), 12, 11);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_22);
lean_closure_set(x_36, 2, x_1);
lean_closure_set(x_36, 3, x_2);
lean_closure_set(x_36, 4, x_3);
lean_closure_set(x_36, 5, x_4);
lean_closure_set(x_36, 6, x_5);
lean_closure_set(x_36, 7, x_6);
lean_closure_set(x_36, 8, x_7);
lean_closure_set(x_36, 9, x_35);
lean_closure_set(x_36, 10, x_12);
x_37 = lean_apply_4(x_23, lean_box(0), lean_box(0), x_33, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___boxed), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_usize_of_nat(x_1);
x_17 = 0;
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16, x_17, x_9, x_15, x_10, x_14);
lean_inc(x_5);
x_19 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__22___boxed), 5, 4);
lean_closure_set(x_19, 0, x_11);
lean_closure_set(x_19, 1, x_9);
lean_closure_set(x_19, 2, x_6);
lean_closure_set(x_19, 3, x_5);
x_20 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 7);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_7);
lean_inc(x_9);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10___rarg___lambda__1___boxed), 12, 11);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_15);
lean_closure_set(x_16, 5, x_4);
lean_closure_set(x_16, 6, x_5);
lean_closure_set(x_16, 7, x_6);
lean_closure_set(x_16, 8, x_11);
lean_closure_set(x_16, 9, x_9);
lean_closure_set(x_16, 10, x_7);
if (x_14 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_10);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
x_23 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_22, x_16);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_12, x_12);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
lean_dec(x_4);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_10);
x_30 = lean_apply_2(x_28, lean_box(0), x_29);
x_31 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_30, x_16);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_34 = lean_box(0);
x_35 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg(x_4, x_5, x_3, x_7, x_11, x_32, x_33, x_34, x_8, x_9, x_10);
x_36 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_35, x_16);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10___rarg(x_1, x_2, x_3, x_1, x_2, x_9, x_4, x_10, x_5, x_8);
return x_11;
}
}
static lean_object* _init_l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___closed__1() {
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
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_1, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_14);
lean_ctor_set(x_9, 0, x_1);
lean_inc(x_9);
lean_ctor_set(x_11, 1, x_13);
lean_ctor_set(x_11, 0, x_9);
lean_inc(x_2);
x_17 = lean_apply_2(x_2, lean_box(0), x_11);
x_18 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_2);
lean_inc(x_3);
x_19 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_17, x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__1), 6, 5);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_5);
lean_closure_set(x_20, 2, x_6);
lean_closure_set(x_20, 3, x_7);
lean_closure_set(x_20, 4, x_9);
x_21 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_11);
lean_dec(x_6);
x_22 = lean_box(0);
x_23 = l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___closed__1;
x_24 = l_List_partition_loop___at_Lake_Workspace_resolveDeps___spec__7(x_1, x_14, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_1);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_25);
lean_ctor_set(x_9, 0, x_1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_List_appendTR___rarg(x_9, x_26);
x_28 = l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8___rarg(x_4, x_5, x_7, x_27, x_8, x_13);
lean_dec(x_7);
x_29 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_29, 0, x_15);
lean_closure_set(x_29, 1, x_2);
x_30 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_28, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_9, 1);
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_1, x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_32);
lean_ctor_set(x_9, 0, x_1);
lean_inc(x_9);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_9);
lean_ctor_set(x_35, 1, x_31);
lean_inc(x_2);
x_36 = lean_apply_2(x_2, lean_box(0), x_35);
x_37 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_37, 0, x_33);
lean_closure_set(x_37, 1, x_2);
lean_inc(x_3);
x_38 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_36, x_37);
x_39 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__1), 6, 5);
lean_closure_set(x_39, 0, x_4);
lean_closure_set(x_39, 1, x_5);
lean_closure_set(x_39, 2, x_6);
lean_closure_set(x_39, 3, x_7);
lean_closure_set(x_39, 4, x_9);
x_40 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_38, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_6);
x_41 = lean_box(0);
x_42 = l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___closed__1;
x_43 = l_List_partition_loop___at_Lake_Workspace_resolveDeps___spec__7(x_1, x_32, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_1);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_44);
lean_ctor_set(x_9, 0, x_1);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_41);
x_46 = l_List_appendTR___rarg(x_9, x_45);
x_47 = l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8___rarg(x_4, x_5, x_7, x_46, x_8, x_31);
lean_dec(x_7);
x_48 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_48, 0, x_33);
lean_closure_set(x_48, 1, x_2);
x_49 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_47, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_9, 0);
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_9);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
x_55 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_1, x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_52);
lean_inc(x_56);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
lean_inc(x_2);
x_58 = lean_apply_2(x_2, lean_box(0), x_57);
x_59 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_59, 0, x_53);
lean_closure_set(x_59, 1, x_2);
lean_inc(x_3);
x_60 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_58, x_59);
x_61 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__1), 6, 5);
lean_closure_set(x_61, 0, x_4);
lean_closure_set(x_61, 1, x_5);
lean_closure_set(x_61, 2, x_6);
lean_closure_set(x_61, 3, x_7);
lean_closure_set(x_61, 4, x_56);
x_62 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_60, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_54);
lean_dec(x_6);
x_63 = lean_box(0);
x_64 = l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___closed__1;
x_65 = l_List_partition_loop___at_Lake_Workspace_resolveDeps___spec__7(x_1, x_52, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_1);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_63);
x_69 = l_List_appendTR___rarg(x_67, x_68);
x_70 = l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8___rarg(x_4, x_5, x_7, x_69, x_8, x_51);
lean_dec(x_7);
x_71 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_71, 0, x_53);
lean_closure_set(x_71, 1, x_2);
x_72 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_70, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_inc(x_12);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
lean_inc(x_12);
x_15 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps_go___rarg___lambda__1), 3, 2);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_12);
lean_inc(x_10);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_15);
lean_inc(x_10);
x_17 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___boxed), 9, 8);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_10);
lean_closure_set(x_17, 3, x_1);
lean_closure_set(x_17, 4, x_2);
lean_closure_set(x_17, 5, x_3);
lean_closure_set(x_17, 6, x_4);
lean_closure_set(x_17, 7, x_6);
x_18 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_resolveDeps___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_resolveDeps___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___at_Lake_Workspace_resolveDeps___spec__1___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
lean_ctor_set(x_3, 1, x_4);
x_9 = lean_apply_2(x_6, lean_box(0), x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_apply_2(x_6, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_4);
x_9 = lean_apply_2(x_6, lean_box(0), x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
x_15 = lean_ctor_get(x_3, 6);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set(x_16, 5, x_14);
lean_ctor_set(x_16, 6, x_15);
x_17 = lean_apply_2(x_6, lean_box(0), x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = lean_box(0);
lean_inc(x_1);
x_9 = l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg(x_1, x_2, x_4, x_6, x_7, x_8, x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps___rarg___lambda__1), 2, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_5);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps___rarg___lambda__2), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Workspace_resolveDeps___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at_Lake_Workspace_resolveDeps___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___lambda__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_12, x_13, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___lambda__4(x_10, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_resolveDeps___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_12, x_13, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_resolveDeps___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at_Lake_Workspace_resolveDeps___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at_Lake_Workspace_resolveDeps___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_15 = l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___lambda__3(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_16 = l_Array_mapMUnsafe_map___at_Lake_Workspace_resolveDeps___spec__5___at_Lake_Workspace_resolveDeps___spec__11___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_15, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_resolveDeps___spec__2___at_Lake_Workspace_resolveDeps___spec__10___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
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
LEAN_EXPORT lean_object* l_Lake_UpdateT_run___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_UpdateT_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_UpdateT_run___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_reuseManifest___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_5);
x_10 = lean_array_uget(x_2, x_3);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = l_Lean_NameSet_contains(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_6, x_12, x_10);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_box(0);
x_3 = x_16;
x_5 = x_17;
x_6 = x_14;
goto _start;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_10);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_box(0);
x_3 = x_20;
x_5 = x_21;
goto _start;
}
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_dec(x_10);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_box(0);
x_3 = x_24;
x_5 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
}
static lean_object* _init_l_Lake_reuseManifest___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ignoring previous manifest because it failed to load: ", 56);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_reuseManifest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_Lake_reuseManifest___lambda__1___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_io_error_to_string(x_2);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_string_append(x_12, x_7);
x_14 = 2;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_push(x_5, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
static lean_object* _init_l_Lake_reuseManifest___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("could not rename workspace packages directory: ", 47);
return x_1;
}
}
static lean_object* _init_l_Lake_reuseManifest___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("workspace packages directory changed; renaming '", 48);
return x_1;
}
}
static lean_object* _init_l_Lake_reuseManifest___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' to '", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_reuseManifest___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_reuseManifest___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_57; 
x_57 = lean_ctor_get(x_1, 2);
lean_inc(x_57);
lean_dec(x_1);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_6);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
lean_dec(x_2);
lean_inc(x_63);
lean_inc(x_64);
x_65 = l_System_FilePath_join(x_64, x_63);
x_66 = l_System_FilePath_pathExists(x_65, x_7);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
x_70 = l_System_FilePath_normalize(x_63);
x_71 = lean_ctor_get(x_3, 0);
lean_inc(x_71);
lean_dec(x_3);
lean_inc(x_71);
x_72 = l_System_FilePath_normalize(x_71);
x_73 = lean_string_dec_eq(x_70, x_72);
lean_dec(x_72);
lean_dec(x_70);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = lean_unbox(x_68);
lean_dec(x_68);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_71);
lean_dec(x_65);
lean_dec(x_64);
lean_free_object(x_57);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_5);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_6);
lean_ctor_set(x_66, 0, x_77);
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_66);
x_78 = l_Lake_reuseManifest___lambda__2___closed__2;
x_79 = lean_string_append(x_78, x_65);
x_80 = l_Lake_reuseManifest___lambda__2___closed__3;
x_81 = lean_string_append(x_79, x_80);
x_82 = l_System_FilePath_join(x_64, x_71);
x_83 = lean_string_append(x_81, x_82);
x_84 = l_Lake_reuseManifest___lambda__2___closed__4;
x_85 = lean_string_append(x_83, x_84);
x_86 = 1;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_array_push(x_6, x_87);
lean_inc(x_82);
x_89 = l_Lake_createParentDirs(x_82, x_69);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 1);
x_92 = lean_ctor_get(x_89, 0);
lean_dec(x_92);
x_93 = lean_io_rename(x_65, x_82, x_91);
lean_dec(x_82);
lean_dec(x_65);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
lean_ctor_set(x_57, 0, x_95);
lean_ctor_set(x_93, 1, x_5);
lean_ctor_set(x_93, 0, x_57);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 0, x_93);
x_8 = x_89;
x_9 = x_96;
goto block_56;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 0);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_93);
lean_ctor_set(x_57, 0, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_57);
lean_ctor_set(x_99, 1, x_5);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 0, x_99);
x_8 = x_89;
x_9 = x_98;
goto block_56;
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_93);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_93, 0);
x_102 = lean_ctor_get(x_93, 1);
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_101);
lean_ctor_set_tag(x_93, 0);
lean_ctor_set(x_93, 1, x_5);
lean_ctor_set(x_93, 0, x_57);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 0, x_93);
x_8 = x_89;
x_9 = x_102;
goto block_56;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_93, 0);
x_104 = lean_ctor_get(x_93, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_93);
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_57);
lean_ctor_set(x_105, 1, x_5);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 0, x_105);
x_8 = x_89;
x_9 = x_104;
goto block_56;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_89, 1);
lean_inc(x_106);
lean_dec(x_89);
x_107 = lean_io_rename(x_65, x_82, x_106);
lean_dec(x_82);
lean_dec(x_65);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
lean_ctor_set(x_57, 0, x_108);
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_57);
lean_ctor_set(x_111, 1, x_5);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_88);
x_8 = x_112;
x_9 = x_109;
goto block_56;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_115 = x_107;
} else {
 lean_dec_ref(x_107);
 x_115 = lean_box(0);
}
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_113);
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
 lean_ctor_set_tag(x_116, 0);
}
lean_ctor_set(x_116, 0, x_57);
lean_ctor_set(x_116, 1, x_5);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_88);
x_8 = x_117;
x_9 = x_114;
goto block_56;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_82);
lean_dec(x_65);
x_118 = !lean_is_exclusive(x_89);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_89, 0);
x_120 = lean_ctor_get(x_89, 1);
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_119);
lean_ctor_set_tag(x_89, 0);
lean_ctor_set(x_89, 1, x_5);
lean_ctor_set(x_89, 0, x_57);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_89);
lean_ctor_set(x_121, 1, x_88);
x_8 = x_121;
x_9 = x_120;
goto block_56;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_89, 0);
x_123 = lean_ctor_get(x_89, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_89);
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_57);
lean_ctor_set(x_124, 1, x_5);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_88);
x_8 = x_125;
x_9 = x_123;
goto block_56;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_64);
lean_free_object(x_57);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_5);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_6);
lean_ctor_set(x_66, 0, x_128);
return x_66;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_129 = lean_ctor_get(x_66, 0);
x_130 = lean_ctor_get(x_66, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_66);
x_131 = l_System_FilePath_normalize(x_63);
x_132 = lean_ctor_get(x_3, 0);
lean_inc(x_132);
lean_dec(x_3);
lean_inc(x_132);
x_133 = l_System_FilePath_normalize(x_132);
x_134 = lean_string_dec_eq(x_131, x_133);
lean_dec(x_133);
lean_dec(x_131);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = lean_unbox(x_129);
lean_dec(x_129);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_132);
lean_dec(x_65);
lean_dec(x_64);
lean_free_object(x_57);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_5);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_6);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_130);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_140 = l_Lake_reuseManifest___lambda__2___closed__2;
x_141 = lean_string_append(x_140, x_65);
x_142 = l_Lake_reuseManifest___lambda__2___closed__3;
x_143 = lean_string_append(x_141, x_142);
x_144 = l_System_FilePath_join(x_64, x_132);
x_145 = lean_string_append(x_143, x_144);
x_146 = l_Lake_reuseManifest___lambda__2___closed__4;
x_147 = lean_string_append(x_145, x_146);
x_148 = 1;
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_148);
x_150 = lean_array_push(x_6, x_149);
lean_inc(x_144);
x_151 = l_Lake_createParentDirs(x_144, x_130);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = lean_io_rename(x_65, x_144, x_152);
lean_dec(x_144);
lean_dec(x_65);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
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
lean_ctor_set(x_57, 0, x_155);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_57);
lean_ctor_set(x_158, 1, x_5);
if (lean_is_scalar(x_153)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_153;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_150);
x_8 = x_159;
x_9 = x_156;
goto block_56;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_154, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_154, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_162 = x_154;
} else {
 lean_dec_ref(x_154);
 x_162 = lean_box(0);
}
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_160);
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_162;
 lean_ctor_set_tag(x_163, 0);
}
lean_ctor_set(x_163, 0, x_57);
lean_ctor_set(x_163, 1, x_5);
if (lean_is_scalar(x_153)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_153;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_150);
x_8 = x_164;
x_9 = x_161;
goto block_56;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_144);
lean_dec(x_65);
x_165 = lean_ctor_get(x_151, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_151, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_167 = x_151;
} else {
 lean_dec_ref(x_151);
 x_167 = lean_box(0);
}
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_165);
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
 lean_ctor_set_tag(x_168, 0);
}
lean_ctor_set(x_168, 0, x_57);
lean_ctor_set(x_168, 1, x_5);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_150);
x_8 = x_169;
x_9 = x_166;
goto block_56;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_65);
lean_dec(x_64);
lean_free_object(x_57);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_5);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_6);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_130);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_174 = lean_ctor_get(x_57, 0);
lean_inc(x_174);
lean_dec(x_57);
x_175 = lean_ctor_get(x_2, 0);
lean_inc(x_175);
lean_dec(x_2);
lean_inc(x_174);
lean_inc(x_175);
x_176 = l_System_FilePath_join(x_175, x_174);
x_177 = l_System_FilePath_pathExists(x_176, x_7);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_180 = x_177;
} else {
 lean_dec_ref(x_177);
 x_180 = lean_box(0);
}
x_181 = l_System_FilePath_normalize(x_174);
x_182 = lean_ctor_get(x_3, 0);
lean_inc(x_182);
lean_dec(x_3);
lean_inc(x_182);
x_183 = l_System_FilePath_normalize(x_182);
x_184 = lean_string_dec_eq(x_181, x_183);
lean_dec(x_183);
lean_dec(x_181);
if (x_184 == 0)
{
uint8_t x_185; 
x_185 = lean_unbox(x_178);
lean_dec(x_178);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_182);
lean_dec(x_176);
lean_dec(x_175);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_5);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_6);
if (lean_is_scalar(x_180)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_180;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_179);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_180);
x_190 = l_Lake_reuseManifest___lambda__2___closed__2;
x_191 = lean_string_append(x_190, x_176);
x_192 = l_Lake_reuseManifest___lambda__2___closed__3;
x_193 = lean_string_append(x_191, x_192);
x_194 = l_System_FilePath_join(x_175, x_182);
x_195 = lean_string_append(x_193, x_194);
x_196 = l_Lake_reuseManifest___lambda__2___closed__4;
x_197 = lean_string_append(x_195, x_196);
x_198 = 1;
x_199 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_198);
x_200 = lean_array_push(x_6, x_199);
lean_inc(x_194);
x_201 = l_Lake_createParentDirs(x_194, x_179);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_204 = lean_io_rename(x_176, x_194, x_202);
lean_dec(x_194);
lean_dec(x_176);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
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
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_205);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_5);
if (lean_is_scalar(x_203)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_203;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_200);
x_8 = x_210;
x_9 = x_206;
goto block_56;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_204, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_204, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_213 = x_204;
} else {
 lean_dec_ref(x_204);
 x_213 = lean_box(0);
}
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_211);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_213;
 lean_ctor_set_tag(x_215, 0);
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_5);
if (lean_is_scalar(x_203)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_203;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_200);
x_8 = x_216;
x_9 = x_212;
goto block_56;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_194);
lean_dec(x_176);
x_217 = lean_ctor_get(x_201, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_201, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_219 = x_201;
} else {
 lean_dec_ref(x_201);
 x_219 = lean_box(0);
}
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_217);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_219;
 lean_ctor_set_tag(x_221, 0);
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_5);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_200);
x_8 = x_222;
x_9 = x_218;
goto block_56;
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_182);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_175);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_5);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_6);
if (lean_is_scalar(x_180)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_180;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_179);
return x_226;
}
}
}
block_56:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_io_error_to_string(x_15);
x_17 = l_Lake_reuseManifest___lambda__2___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_13);
x_24 = lean_array_push(x_13, x_22);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_24);
lean_ctor_set(x_8, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_io_error_to_string(x_27);
x_29 = l_Lake_reuseManifest___lambda__2___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_26);
x_36 = lean_array_push(x_26, x_34);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_9);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_11);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_10, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_9);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_dec(x_10);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_8, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_9);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_dec(x_8);
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
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_9);
return x_55;
}
}
}
}
}
static lean_object* _init_l_Lake_reuseManifest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": no previous manifest, creating one from scratch", 49);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_reuseManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = 0;
x_10 = l_Lean_Name_toString(x_8, x_9);
x_105 = lean_ctor_get(x_6, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_6, 4);
lean_inc(x_106);
x_107 = l_System_FilePath_join(x_105, x_106);
x_108 = l_Lake_Manifest_load(x_107, x_5);
lean_dec(x_107);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_108, 1, x_3);
lean_ctor_set(x_108, 0, x_112);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_4);
x_11 = x_113;
x_12 = x_111;
goto block_104;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_108, 0);
x_115 = lean_ctor_get(x_108, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_108);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_3);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_4);
x_11 = x_118;
x_12 = x_115;
goto block_104;
}
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_108);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_108, 0);
x_121 = lean_ctor_get(x_108, 1);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set_tag(x_108, 0);
lean_ctor_set(x_108, 1, x_3);
lean_ctor_set(x_108, 0, x_122);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_108);
lean_ctor_set(x_123, 1, x_4);
x_11 = x_123;
x_12 = x_121;
goto block_104;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_108, 0);
x_125 = lean_ctor_get(x_108, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_108);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_124);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_3);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_4);
x_11 = x_128;
x_12 = x_125;
goto block_104;
}
}
block_104:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 11)
{
uint8_t x_16; 
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_22 = lean_string_append(x_21, x_10);
lean_dec(x_10);
x_23 = l_Lake_reuseManifest___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_push(x_17, x_26);
x_28 = lean_box(0);
lean_ctor_set(x_13, 0, x_28);
lean_ctor_set(x_11, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_32 = lean_string_append(x_31, x_10);
lean_dec(x_10);
x_33 = l_Lake_reuseManifest___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = 1;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_push(x_17, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_11, 1, x_37);
lean_ctor_set(x_11, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_12);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_dec(x_11);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_43 = x_13;
} else {
 lean_dec_ref(x_13);
 x_43 = lean_box(0);
}
x_44 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_45 = lean_string_append(x_44, x_10);
lean_dec(x_10);
x_46 = l_Lake_reuseManifest___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = 1;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_array_push(x_41, x_49);
x_51 = lean_box(0);
if (lean_is_scalar(x_43)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_43;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_12);
return x_54;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_dec(x_11);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_dec(x_13);
x_57 = lean_box(0);
x_58 = l_Lake_reuseManifest___lambda__1(x_10, x_15, x_57, x_56, x_55, x_12);
lean_dec(x_10);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_13);
lean_dec(x_10);
x_59 = !lean_is_exclusive(x_11);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_11, 1);
x_61 = lean_ctor_get(x_11, 0);
lean_dec(x_61);
x_62 = lean_io_error_to_string(x_15);
x_63 = 3;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_array_get_size(x_60);
x_66 = lean_array_push(x_60, x_64);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_66);
lean_ctor_set(x_11, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_11);
lean_ctor_set(x_67, 1, x_12);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_11, 1);
lean_inc(x_68);
lean_dec(x_11);
x_69 = lean_io_error_to_string(x_15);
x_70 = 3;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_get_size(x_68);
x_73 = lean_array_push(x_68, x_71);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_12);
return x_75;
}
}
}
}
else
{
lean_dec(x_10);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_11, 1);
lean_inc(x_76);
lean_dec(x_11);
x_77 = lean_ctor_get(x_13, 1);
lean_inc(x_77);
lean_dec(x_13);
x_78 = lean_ctor_get(x_14, 0);
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_box(0);
x_80 = l_Lake_reuseManifest___lambda__2(x_78, x_6, x_7, x_79, x_77, x_76, x_12);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_81 = lean_ctor_get(x_11, 1);
lean_inc(x_81);
lean_dec(x_11);
x_82 = lean_ctor_get(x_13, 1);
lean_inc(x_82);
lean_dec(x_13);
x_83 = lean_ctor_get(x_14, 0);
lean_inc(x_83);
lean_dec(x_14);
x_84 = lean_ctor_get(x_83, 3);
lean_inc(x_84);
x_85 = lean_array_get_size(x_84);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_lt(x_86, x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_84);
x_88 = lean_box(0);
x_89 = l_Lake_reuseManifest___lambda__2(x_83, x_6, x_7, x_88, x_82, x_81, x_12);
return x_89;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_85, x_85);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_85);
lean_dec(x_84);
x_91 = lean_box(0);
x_92 = l_Lake_reuseManifest___lambda__2(x_83, x_6, x_7, x_91, x_82, x_81, x_12);
return x_92;
}
else
{
size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = 0;
x_94 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_95 = lean_box(0);
x_96 = l_Array_foldlMUnsafe_fold___at_Lake_reuseManifest___spec__1(x_2, x_84, x_93, x_94, x_95, x_82, x_81, x_12);
lean_dec(x_84);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_dec(x_98);
x_103 = l_Lake_reuseManifest___lambda__2(x_83, x_6, x_7, x_101, x_102, x_100, x_99);
lean_dec(x_101);
return x_103;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_reuseManifest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_reuseManifest___spec__1(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_reuseManifest___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_reuseManifest___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_reuseManifest___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_reuseManifest___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_reuseManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_reuseManifest(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_updateDep___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = l_Lean_NameMap_contains___rarg(x_8, x_14);
if (x_18 == 0)
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = l_System_FilePath_join(x_21, x_20);
lean_ctor_set(x_17, 0, x_22);
x_23 = 1;
lean_inc(x_14);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_23);
x_24 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_14, x_12);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_box(0);
x_3 = x_26;
x_5 = x_27;
x_8 = x_24;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = l_System_FilePath_join(x_30, x_29);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = 1;
lean_inc(x_14);
lean_ctor_set(x_12, 3, x_32);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_33);
x_34 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_14, x_12);
x_35 = 1;
x_36 = lean_usize_add(x_3, x_35);
x_37 = lean_box(0);
x_3 = x_36;
x_5 = x_37;
x_8 = x_34;
goto _start;
}
}
else
{
uint8_t x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_39 = 1;
lean_inc(x_14);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_39);
x_40 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_14, x_12);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_43 = lean_box(0);
x_3 = x_42;
x_5 = x_43;
x_8 = x_40;
goto _start;
}
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
lean_free_object(x_12);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_45 = 1;
x_46 = lean_usize_add(x_3, x_45);
x_47 = lean_box(0);
x_3 = x_46;
x_5 = x_47;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_12, 0);
x_50 = lean_ctor_get(x_12, 1);
x_51 = lean_ctor_get(x_12, 2);
x_52 = lean_ctor_get(x_12, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_12);
x_53 = l_Lean_NameMap_contains___rarg(x_8, x_49);
if (x_53 == 0)
{
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
x_57 = l_System_FilePath_join(x_56, x_54);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
x_59 = 1;
lean_inc(x_49);
x_60 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_50);
lean_ctor_set(x_60, 2, x_51);
lean_ctor_set(x_60, 3, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*4, x_59);
x_61 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_49, x_60);
x_62 = 1;
x_63 = lean_usize_add(x_3, x_62);
x_64 = lean_box(0);
x_3 = x_63;
x_5 = x_64;
x_8 = x_61;
goto _start;
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; lean_object* x_71; 
x_66 = 1;
lean_inc(x_49);
x_67 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_67, 0, x_49);
lean_ctor_set(x_67, 1, x_50);
lean_ctor_set(x_67, 2, x_51);
lean_ctor_set(x_67, 3, x_52);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_66);
x_68 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_49, x_67);
x_69 = 1;
x_70 = lean_usize_add(x_3, x_69);
x_71 = lean_box(0);
x_3 = x_70;
x_5 = x_71;
x_8 = x_68;
goto _start;
}
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
x_73 = 1;
x_74 = lean_usize_add(x_3, x_73);
x_75 = lean_box(0);
x_3 = x_74;
x_5 = x_75;
goto _start;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_1);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_5);
lean_ctor_set(x_77, 1, x_7);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_8);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_9);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_10);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
static lean_object* _init_l_Lake_updateDep___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ignoring dependency manifest because it failed to load: ", 58);
return x_1;
}
}
static lean_object* _init_l_Lake_updateDep___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ignoring missing dependency manifest '", 40);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_82; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = l_System_FilePath_join(x_8, x_9);
x_82 = l_Lake_Manifest_load(x_10, x_7);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_82, 1, x_4);
lean_ctor_set(x_82, 0, x_86);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_5);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_6);
x_11 = x_88;
x_12 = x_85;
goto block_81;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_82, 0);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_82);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_4);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_5);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_6);
x_11 = x_94;
x_12 = x_90;
goto block_81;
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_82);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get(x_82, 1);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_tag(x_82, 0);
lean_ctor_set(x_82, 1, x_4);
lean_ctor_set(x_82, 0, x_98);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_82);
lean_ctor_set(x_99, 1, x_5);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_6);
x_11 = x_100;
x_12 = x_97;
goto block_81;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_82, 0);
x_102 = lean_ctor_get(x_82, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_82);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_4);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_5);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_6);
x_11 = x_106;
x_12 = x_102;
goto block_81;
}
}
block_81:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 11)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = l_Lean_Name_toString(x_21, x_22);
x_24 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lake_updateDep___lambda__2___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_10);
lean_dec(x_10);
x_29 = l_Lake_reuseManifest___lambda__2___closed__4;
x_30 = lean_string_append(x_28, x_29);
x_31 = 2;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_push(x_17, x_32);
x_34 = lean_box(0);
x_35 = l_Lake_updateDep___lambda__1(x_1, x_34, x_3, x_19, x_18, x_33, x_12);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_10);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_dec(x_11);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 2);
lean_inc(x_40);
lean_dec(x_39);
x_41 = 1;
x_42 = l_Lean_Name_toString(x_40, x_41);
x_43 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = l_Lake_updateDep___lambda__2___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_io_error_to_string(x_16);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = lean_string_append(x_48, x_43);
x_50 = 2;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_push(x_36, x_51);
x_53 = lean_box(0);
x_54 = l_Lake_updateDep___lambda__1(x_1, x_53, x_3, x_38, x_37, x_52, x_12);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_10);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_dec(x_11);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_dec(x_13);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_dec(x_14);
x_58 = lean_ctor_get(x_15, 0);
lean_inc(x_58);
lean_dec(x_15);
x_59 = lean_ctor_get(x_58, 3);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_array_get_size(x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_lt(x_61, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_59);
x_63 = lean_box(0);
x_64 = l_Lake_updateDep___lambda__1(x_1, x_63, x_3, x_57, x_56, x_55, x_12);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_60, x_60);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
lean_dec(x_59);
x_66 = lean_box(0);
x_67 = l_Lake_updateDep___lambda__1(x_1, x_66, x_3, x_57, x_56, x_55, x_12);
return x_67;
}
else
{
size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_68 = 0;
x_69 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_70 = lean_box(0);
lean_inc(x_1);
x_71 = l_Array_foldlMUnsafe_fold___at_Lake_updateDep___spec__1(x_1, x_59, x_68, x_69, x_70, x_3, x_57, x_56, x_55, x_12);
lean_dec(x_59);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_dec(x_74);
x_80 = l_Lake_updateDep___lambda__1(x_1, x_78, x_3, x_79, x_77, x_76, x_75);
lean_dec(x_78);
return x_80;
}
}
}
}
}
}
static lean_object* _init_l_Lake_updateDep___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": package '", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_updateDep___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' was required as '", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_10 = 1;
x_11 = l_Lean_Name_toString(x_1, x_10);
x_12 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lake_updateDep___lambda__3___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_Name_toString(x_2, x_10);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_Lake_updateDep___lambda__3___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_Name_toString(x_3, x_10);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l_Lake_reuseManifest___lambda__2___closed__4;
x_23 = lean_string_append(x_21, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_array_get_size(x_8);
x_27 = lean_array_push(x_8, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
static lean_object* _init_l_Lake_updateDep___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' was downloaded incorrectly; you will need to manually delete '", 64);
return x_1;
}
}
static lean_object* _init_l_Lake_updateDep___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("': ", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_45; 
x_11 = lean_ctor_get(x_1, 0);
x_45 = l_IO_FS_removeDirAll(x_11, x_10);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_45, 1, x_7);
lean_ctor_set(x_45, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_8);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_9);
x_12 = x_51;
x_13 = x_48;
goto block_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_45);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_7);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_8);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_9);
x_12 = x_57;
x_13 = x_53;
goto block_44;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_tag(x_45, 0);
lean_ctor_set(x_45, 1, x_7);
lean_ctor_set(x_45, 0, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_45);
lean_ctor_set(x_62, 1, x_8);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_9);
x_12 = x_63;
x_13 = x_60;
goto block_44;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_45, 0);
x_65 = lean_ctor_get(x_45, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_45);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_7);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_9);
x_12 = x_69;
x_13 = x_65;
goto block_44;
}
}
block_44:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
lean_inc(x_4);
x_22 = l_Lean_Name_toString(x_4, x_21);
x_23 = l_Lake_reuseManifest___lambda__2___closed__4;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lake_updateDep___lambda__4___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_11);
x_28 = l_Lake_updateDep___lambda__4___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_io_error_to_string(x_20);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_push(x_17, x_35);
x_37 = lean_box(0);
x_38 = l_Lake_updateDep___lambda__3(x_2, x_3, x_4, x_37, x_6, x_19, x_18, x_36, x_13);
lean_dec(x_18);
lean_dec(x_19);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_16);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_dec(x_12);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_dec(x_14);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_dec(x_15);
x_42 = lean_box(0);
x_43 = l_Lake_updateDep___lambda__3(x_2, x_3, x_4, x_42, x_6, x_41, x_40, x_39, x_13);
lean_dec(x_40);
lean_dec(x_41);
return x_43;
}
}
}
}
static lean_object* _init_l_Lake_updateDep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("std", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_updateDep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_updateDep___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_updateDep___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" @ ", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_updateDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_221; lean_object* x_222; lean_object* x_267; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_name_eq(x_10, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_267 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_6, x_15);
if (x_14 == 0)
{
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; 
x_268 = lean_ctor_get(x_5, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_11, 0);
lean_inc(x_269);
lean_dec(x_11);
x_270 = lean_ctor_get(x_12, 0);
lean_inc(x_270);
lean_dec(x_12);
x_271 = lean_ctor_get(x_1, 1);
lean_inc(x_271);
lean_dec(x_1);
x_272 = 1;
lean_inc(x_2);
x_273 = l_Lake_Dependency_materialize(x_2, x_272, x_268, x_269, x_270, x_271, x_7, x_8);
lean_dec(x_268);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
uint8_t x_275; 
x_275 = !lean_is_exclusive(x_273);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_276 = lean_ctor_get(x_273, 1);
x_277 = lean_ctor_get(x_273, 0);
lean_dec(x_277);
x_278 = !lean_is_exclusive(x_274);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_274, 0);
lean_ctor_set(x_273, 1, x_5);
lean_ctor_set(x_273, 0, x_279);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_273);
lean_ctor_set(x_280, 1, x_6);
lean_ctor_set(x_274, 0, x_280);
x_221 = x_274;
x_222 = x_276;
goto block_266;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_274, 0);
x_282 = lean_ctor_get(x_274, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_274);
lean_ctor_set(x_273, 1, x_5);
lean_ctor_set(x_273, 0, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_273);
lean_ctor_set(x_283, 1, x_6);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_282);
x_221 = x_284;
x_222 = x_276;
goto block_266;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_285 = lean_ctor_get(x_273, 1);
lean_inc(x_285);
lean_dec(x_273);
x_286 = lean_ctor_get(x_274, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_274, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_288 = x_274;
} else {
 lean_dec_ref(x_274);
 x_288 = lean_box(0);
}
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_5);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_6);
if (lean_is_scalar(x_288)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_288;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_287);
x_221 = x_291;
x_222 = x_285;
goto block_266;
}
}
else
{
lean_object* x_292; uint8_t x_293; 
lean_dec(x_6);
lean_dec(x_5);
x_292 = lean_ctor_get(x_273, 1);
lean_inc(x_292);
lean_dec(x_273);
x_293 = !lean_is_exclusive(x_274);
if (x_293 == 0)
{
x_221 = x_274;
x_222 = x_292;
goto block_266;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_274, 0);
x_295 = lean_ctor_get(x_274, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_274);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_221 = x_296;
x_222 = x_292;
goto block_266;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_1);
x_297 = lean_ctor_get(x_267, 0);
lean_inc(x_297);
lean_dec(x_267);
x_298 = lean_ctor_get(x_5, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_11, 0);
lean_inc(x_299);
lean_dec(x_11);
x_300 = lean_ctor_get(x_12, 0);
lean_inc(x_300);
lean_dec(x_12);
x_301 = l_Lake_PackageEntry_materialize(x_297, x_298, x_299, x_300, x_7, x_8);
lean_dec(x_298);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
if (lean_obj_tag(x_302) == 0)
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_301);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_301, 1);
x_305 = lean_ctor_get(x_301, 0);
lean_dec(x_305);
x_306 = !lean_is_exclusive(x_302);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_302, 0);
lean_ctor_set(x_301, 1, x_5);
lean_ctor_set(x_301, 0, x_307);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_301);
lean_ctor_set(x_308, 1, x_6);
lean_ctor_set(x_302, 0, x_308);
x_16 = x_302;
x_17 = x_304;
goto block_220;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_302, 0);
x_310 = lean_ctor_get(x_302, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_302);
lean_ctor_set(x_301, 1, x_5);
lean_ctor_set(x_301, 0, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_301);
lean_ctor_set(x_311, 1, x_6);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_310);
x_16 = x_312;
x_17 = x_304;
goto block_220;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_313 = lean_ctor_get(x_301, 1);
lean_inc(x_313);
lean_dec(x_301);
x_314 = lean_ctor_get(x_302, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_302, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_316 = x_302;
} else {
 lean_dec_ref(x_302);
 x_316 = lean_box(0);
}
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_5);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_6);
if (lean_is_scalar(x_316)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_316;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_315);
x_16 = x_319;
x_17 = x_313;
goto block_220;
}
}
else
{
lean_object* x_320; uint8_t x_321; 
lean_dec(x_6);
lean_dec(x_5);
x_320 = lean_ctor_get(x_301, 1);
lean_inc(x_320);
lean_dec(x_301);
x_321 = !lean_is_exclusive(x_302);
if (x_321 == 0)
{
x_16 = x_302;
x_17 = x_320;
goto block_220;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_302, 0);
x_323 = lean_ctor_get(x_302, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_302);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_16 = x_324;
x_17 = x_320;
goto block_220;
}
}
}
}
else
{
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; lean_object* x_331; 
x_325 = lean_ctor_get(x_5, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_11, 0);
lean_inc(x_326);
lean_dec(x_11);
x_327 = lean_ctor_get(x_12, 0);
lean_inc(x_327);
lean_dec(x_12);
x_328 = lean_ctor_get(x_1, 1);
lean_inc(x_328);
lean_dec(x_1);
x_329 = 0;
lean_inc(x_2);
x_330 = l_Lake_Dependency_materialize(x_2, x_329, x_325, x_326, x_327, x_328, x_7, x_8);
lean_dec(x_325);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
if (lean_obj_tag(x_331) == 0)
{
uint8_t x_332; 
x_332 = !lean_is_exclusive(x_330);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_333 = lean_ctor_get(x_330, 1);
x_334 = lean_ctor_get(x_330, 0);
lean_dec(x_334);
x_335 = !lean_is_exclusive(x_331);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_331, 0);
lean_ctor_set(x_330, 1, x_5);
lean_ctor_set(x_330, 0, x_336);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_330);
lean_ctor_set(x_337, 1, x_6);
lean_ctor_set(x_331, 0, x_337);
x_221 = x_331;
x_222 = x_333;
goto block_266;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_338 = lean_ctor_get(x_331, 0);
x_339 = lean_ctor_get(x_331, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_331);
lean_ctor_set(x_330, 1, x_5);
lean_ctor_set(x_330, 0, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_330);
lean_ctor_set(x_340, 1, x_6);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_339);
x_221 = x_341;
x_222 = x_333;
goto block_266;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_342 = lean_ctor_get(x_330, 1);
lean_inc(x_342);
lean_dec(x_330);
x_343 = lean_ctor_get(x_331, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_331, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_345 = x_331;
} else {
 lean_dec_ref(x_331);
 x_345 = lean_box(0);
}
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_5);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_6);
if (lean_is_scalar(x_345)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_345;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_344);
x_221 = x_348;
x_222 = x_342;
goto block_266;
}
}
else
{
lean_object* x_349; uint8_t x_350; 
lean_dec(x_6);
lean_dec(x_5);
x_349 = lean_ctor_get(x_330, 1);
lean_inc(x_349);
lean_dec(x_330);
x_350 = !lean_is_exclusive(x_331);
if (x_350 == 0)
{
x_221 = x_331;
x_222 = x_349;
goto block_266;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_331, 0);
x_352 = lean_ctor_get(x_331, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_331);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
x_221 = x_353;
x_222 = x_349;
goto block_266;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_1);
x_354 = lean_ctor_get(x_267, 0);
lean_inc(x_354);
lean_dec(x_267);
x_355 = lean_ctor_get(x_5, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_11, 0);
lean_inc(x_356);
lean_dec(x_11);
x_357 = lean_ctor_get(x_12, 0);
lean_inc(x_357);
lean_dec(x_12);
x_358 = l_Lake_PackageEntry_materialize(x_354, x_355, x_356, x_357, x_7, x_8);
lean_dec(x_355);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
if (lean_obj_tag(x_359) == 0)
{
uint8_t x_360; 
x_360 = !lean_is_exclusive(x_358);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_361 = lean_ctor_get(x_358, 1);
x_362 = lean_ctor_get(x_358, 0);
lean_dec(x_362);
x_363 = !lean_is_exclusive(x_359);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_359, 0);
lean_ctor_set(x_358, 1, x_5);
lean_ctor_set(x_358, 0, x_364);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_358);
lean_ctor_set(x_365, 1, x_6);
lean_ctor_set(x_359, 0, x_365);
x_16 = x_359;
x_17 = x_361;
goto block_220;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_366 = lean_ctor_get(x_359, 0);
x_367 = lean_ctor_get(x_359, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_359);
lean_ctor_set(x_358, 1, x_5);
lean_ctor_set(x_358, 0, x_366);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_358);
lean_ctor_set(x_368, 1, x_6);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_367);
x_16 = x_369;
x_17 = x_361;
goto block_220;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_370 = lean_ctor_get(x_358, 1);
lean_inc(x_370);
lean_dec(x_358);
x_371 = lean_ctor_get(x_359, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_359, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_373 = x_359;
} else {
 lean_dec_ref(x_359);
 x_373 = lean_box(0);
}
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_5);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_6);
if (lean_is_scalar(x_373)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_373;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_372);
x_16 = x_376;
x_17 = x_370;
goto block_220;
}
}
else
{
lean_object* x_377; uint8_t x_378; 
lean_dec(x_6);
lean_dec(x_5);
x_377 = lean_ctor_get(x_358, 1);
lean_inc(x_377);
lean_dec(x_358);
x_378 = !lean_is_exclusive(x_359);
if (x_378 == 0)
{
x_16 = x_359;
x_17 = x_377;
goto block_220;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_359, 0);
x_380 = lean_ctor_get(x_359, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_359);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
x_16 = x_381;
x_17 = x_377;
goto block_220;
}
}
}
}
block_220:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
x_102 = lean_ctor_get(x_2, 2);
lean_inc(x_102);
lean_dec(x_2);
x_103 = 1;
lean_inc(x_24);
x_104 = l_Lake_loadDepPackage(x_24, x_102, x_3, x_103, x_25, x_20, x_17);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
x_110 = !lean_is_exclusive(x_106);
if (x_110 == 0)
{
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_106);
lean_ctor_set(x_105, 0, x_19);
x_26 = x_105;
x_27 = x_107;
goto block_101;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 0);
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_106);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_113);
lean_ctor_set(x_105, 0, x_19);
x_26 = x_105;
x_27 = x_107;
goto block_101;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_105, 1);
lean_inc(x_114);
lean_dec(x_105);
x_115 = lean_ctor_get(x_106, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_106, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_117 = x_106;
} else {
 lean_dec_ref(x_106);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_118);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_19);
lean_ctor_set(x_119, 1, x_114);
x_26 = x_119;
x_27 = x_107;
goto block_101;
}
}
else
{
lean_object* x_120; uint8_t x_121; 
lean_free_object(x_19);
lean_dec(x_21);
x_120 = lean_ctor_get(x_104, 1);
lean_inc(x_120);
lean_dec(x_104);
x_121 = !lean_is_exclusive(x_105);
if (x_121 == 0)
{
x_26 = x_105;
x_27 = x_120;
goto block_101;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_105, 0);
x_123 = lean_ctor_get(x_105, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_105);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_26 = x_124;
x_27 = x_120;
goto block_101;
}
}
}
else
{
uint8_t x_125; 
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_10);
x_125 = !lean_is_exclusive(x_104);
if (x_125 == 0)
{
return x_104;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_104, 0);
x_127 = lean_ctor_get(x_104, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_104);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
block_101:
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
lean_dec(x_22);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_name_eq(x_35, x_15);
x_37 = l_instDecidableNot___rarg(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_10);
x_38 = lean_box(0);
x_39 = l_Lake_updateDep___lambda__2(x_32, x_38, x_4, x_33, x_31, x_30, x_27);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lake_updateDep___closed__2;
x_41 = lean_name_eq(x_15, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_24);
x_42 = lean_box(0);
x_43 = l_Lake_updateDep___lambda__4(x_32, x_10, x_35, x_15, x_42, x_4, x_33, x_31, x_30, x_27);
lean_dec(x_32);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_24, 2);
lean_inc(x_44);
lean_dec(x_24);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
lean_dec(x_44);
x_46 = 1;
lean_inc(x_35);
x_47 = l_Lean_Name_toString(x_35, x_46);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_45);
x_48 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_49 = l_Lake_stdMismatchError(x_47, x_48);
lean_dec(x_47);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_push(x_30, x_51);
x_53 = lean_box(0);
x_54 = l_Lake_updateDep___lambda__4(x_32, x_10, x_35, x_15, x_53, x_4, x_33, x_31, x_52, x_27);
lean_dec(x_32);
return x_54;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_45, 2);
lean_inc(x_55);
lean_dec(x_45);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_57 = l_Lake_stdMismatchError(x_47, x_56);
lean_dec(x_47);
x_58 = 3;
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_array_push(x_30, x_59);
x_61 = lean_box(0);
x_62 = l_Lake_updateDep___lambda__4(x_32, x_10, x_35, x_15, x_61, x_4, x_33, x_31, x_60, x_27);
lean_dec(x_32);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = l_String_quote(x_64);
lean_dec(x_64);
lean_ctor_set_tag(x_55, 3);
lean_ctor_set(x_55, 0, x_65);
x_66 = l_Std_Format_defWidth;
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_format_pretty(x_55, x_66, x_67, x_67);
x_69 = l_Lake_updateDep___closed__3;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_72 = lean_string_append(x_70, x_71);
x_73 = l_Lake_stdMismatchError(x_47, x_72);
lean_dec(x_72);
lean_dec(x_47);
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_array_push(x_30, x_75);
x_77 = lean_box(0);
x_78 = l_Lake_updateDep___lambda__4(x_32, x_10, x_35, x_15, x_77, x_4, x_33, x_31, x_76, x_27);
lean_dec(x_32);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_79 = lean_ctor_get(x_55, 0);
lean_inc(x_79);
lean_dec(x_55);
x_80 = l_String_quote(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = l_Std_Format_defWidth;
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_format_pretty(x_81, x_82, x_83, x_83);
x_85 = l_Lake_updateDep___closed__3;
x_86 = lean_string_append(x_85, x_84);
lean_dec(x_84);
x_87 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_88 = lean_string_append(x_86, x_87);
x_89 = l_Lake_stdMismatchError(x_47, x_88);
lean_dec(x_88);
lean_dec(x_47);
x_90 = 3;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_push(x_30, x_91);
x_93 = lean_box(0);
x_94 = l_Lake_updateDep___lambda__4(x_32, x_10, x_35, x_15, x_93, x_4, x_33, x_31, x_92, x_27);
lean_dec(x_32);
return x_94;
}
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_10);
x_95 = !lean_is_exclusive(x_26);
if (x_95 == 0)
{
lean_object* x_96; 
if (lean_is_scalar(x_22)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_22;
}
lean_ctor_set(x_96, 0, x_26);
lean_ctor_set(x_96, 1, x_27);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_26, 0);
x_98 = lean_ctor_get(x_26, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_26);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_22)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_22;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_27);
return x_100;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
x_129 = lean_ctor_get(x_19, 0);
x_130 = lean_ctor_get(x_19, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_19);
x_191 = lean_ctor_get(x_2, 2);
lean_inc(x_191);
lean_dec(x_2);
x_192 = 1;
lean_inc(x_129);
x_193 = l_Lake_loadDepPackage(x_129, x_191, x_3, x_192, x_130, x_20, x_17);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_198 = x_194;
} else {
 lean_dec_ref(x_194);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_195, 0);
lean_inc(x_199);
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
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_21);
if (lean_is_scalar(x_198)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_198;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_197);
x_131 = x_204;
x_132 = x_196;
goto block_190;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_21);
x_205 = lean_ctor_get(x_193, 1);
lean_inc(x_205);
lean_dec(x_193);
x_206 = lean_ctor_get(x_194, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_194, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_208 = x_194;
} else {
 lean_dec_ref(x_194);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
x_131 = x_209;
x_132 = x_205;
goto block_190;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_129);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_10);
x_210 = lean_ctor_get(x_193, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_193, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_212 = x_193;
} else {
 lean_dec_ref(x_193);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
block_190:
{
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; 
lean_dec(x_22);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
x_139 = lean_ctor_get(x_137, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 2);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_name_eq(x_140, x_15);
x_142 = l_instDecidableNot___rarg(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_140);
lean_dec(x_129);
lean_dec(x_15);
lean_dec(x_10);
x_143 = lean_box(0);
x_144 = l_Lake_updateDep___lambda__2(x_137, x_143, x_4, x_138, x_136, x_135, x_132);
return x_144;
}
else
{
lean_object* x_145; uint8_t x_146; 
x_145 = l_Lake_updateDep___closed__2;
x_146 = lean_name_eq(x_15, x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_129);
x_147 = lean_box(0);
x_148 = l_Lake_updateDep___lambda__4(x_137, x_10, x_140, x_15, x_147, x_4, x_138, x_136, x_135, x_132);
lean_dec(x_137);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_129, 2);
lean_inc(x_149);
lean_dec(x_129);
x_150 = lean_ctor_get(x_149, 3);
lean_inc(x_150);
lean_dec(x_149);
x_151 = 1;
lean_inc(x_140);
x_152 = l_Lean_Name_toString(x_140, x_151);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_150);
x_153 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_154 = l_Lake_stdMismatchError(x_152, x_153);
lean_dec(x_152);
x_155 = 3;
x_156 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_155);
x_157 = lean_array_push(x_135, x_156);
x_158 = lean_box(0);
x_159 = l_Lake_updateDep___lambda__4(x_137, x_10, x_140, x_15, x_158, x_4, x_138, x_136, x_157, x_132);
lean_dec(x_137);
return x_159;
}
else
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_150, 2);
lean_inc(x_160);
lean_dec(x_150);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_162 = l_Lake_stdMismatchError(x_152, x_161);
lean_dec(x_152);
x_163 = 3;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
x_165 = lean_array_push(x_135, x_164);
x_166 = lean_box(0);
x_167 = l_Lake_updateDep___lambda__4(x_137, x_10, x_140, x_15, x_166, x_4, x_138, x_136, x_165, x_132);
lean_dec(x_137);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_168 = lean_ctor_get(x_160, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_169 = x_160;
} else {
 lean_dec_ref(x_160);
 x_169 = lean_box(0);
}
x_170 = l_String_quote(x_168);
lean_dec(x_168);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(3, 1, 0);
} else {
 x_171 = x_169;
 lean_ctor_set_tag(x_171, 3);
}
lean_ctor_set(x_171, 0, x_170);
x_172 = l_Std_Format_defWidth;
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_format_pretty(x_171, x_172, x_173, x_173);
x_175 = l_Lake_updateDep___closed__3;
x_176 = lean_string_append(x_175, x_174);
lean_dec(x_174);
x_177 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_178 = lean_string_append(x_176, x_177);
x_179 = l_Lake_stdMismatchError(x_152, x_178);
lean_dec(x_178);
lean_dec(x_152);
x_180 = 3;
x_181 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*1, x_180);
x_182 = lean_array_push(x_135, x_181);
x_183 = lean_box(0);
x_184 = l_Lake_updateDep___lambda__4(x_137, x_10, x_140, x_15, x_183, x_4, x_138, x_136, x_182, x_132);
lean_dec(x_137);
return x_184;
}
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_129);
lean_dec(x_15);
lean_dec(x_10);
x_185 = lean_ctor_get(x_131, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_131, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_187 = x_131;
} else {
 lean_dec_ref(x_131);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
if (lean_is_scalar(x_22)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_22;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_132);
return x_189;
}
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_214 = !lean_is_exclusive(x_16);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_16);
lean_ctor_set(x_215, 1, x_17);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_16, 0);
x_217 = lean_ctor_get(x_16, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_16);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_17);
return x_219;
}
}
}
block_266:
{
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = !lean_is_exclusive(x_221);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_221, 0);
lean_dec(x_226);
x_227 = !lean_is_exclusive(x_223);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_223, 1);
x_229 = lean_ctor_get(x_223, 0);
lean_dec(x_229);
x_230 = !lean_is_exclusive(x_224);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_224, 0);
x_232 = lean_ctor_get(x_231, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_228, x_233, x_232);
lean_ctor_set(x_223, 1, x_234);
x_16 = x_221;
x_17 = x_222;
goto block_220;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_235 = lean_ctor_get(x_224, 0);
x_236 = lean_ctor_get(x_224, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_224);
x_237 = lean_ctor_get(x_235, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_228, x_238, x_237);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_235);
lean_ctor_set(x_240, 1, x_236);
lean_ctor_set(x_223, 1, x_239);
lean_ctor_set(x_223, 0, x_240);
x_16 = x_221;
x_17 = x_222;
goto block_220;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_241 = lean_ctor_get(x_223, 1);
lean_inc(x_241);
lean_dec(x_223);
x_242 = lean_ctor_get(x_224, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_224, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_244 = x_224;
} else {
 lean_dec_ref(x_224);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_242, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_241, x_246, x_245);
if (lean_is_scalar(x_244)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_244;
}
lean_ctor_set(x_248, 0, x_242);
lean_ctor_set(x_248, 1, x_243);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
lean_ctor_set(x_221, 0, x_249);
x_16 = x_221;
x_17 = x_222;
goto block_220;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_250 = lean_ctor_get(x_221, 1);
lean_inc(x_250);
lean_dec(x_221);
x_251 = lean_ctor_get(x_223, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_252 = x_223;
} else {
 lean_dec_ref(x_223);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_224, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_224, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_255 = x_224;
} else {
 lean_dec_ref(x_224);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_253, 2);
lean_inc(x_256);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_251, x_257, x_256);
if (lean_is_scalar(x_255)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_255;
}
lean_ctor_set(x_259, 0, x_253);
lean_ctor_set(x_259, 1, x_254);
if (lean_is_scalar(x_252)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_252;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_250);
x_16 = x_261;
x_17 = x_222;
goto block_220;
}
}
else
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_221);
if (x_262 == 0)
{
x_16 = x_221;
x_17 = x_222;
goto block_220;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_221, 0);
x_264 = lean_ctor_get(x_221, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_221);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_16 = x_265;
x_17 = x_222;
goto block_220;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_updateDep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_updateDep___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_updateDep___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_updateDep___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_updateDep___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_updateDep___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_updateDep___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_updateDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_updateDep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": running post-update hooks", 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_16 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2___closed__1;
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
x_38 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1(x_9, x_13, x_10, x_35, x_36, x_37, x_5, x_22, x_7);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_1, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_7, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 4);
lean_inc(x_17);
lean_dec(x_7);
lean_ctor_set(x_10, 0, x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 1, x_16);
x_21 = lean_array_push(x_5, x_15);
x_3 = x_12;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
x_25 = lean_ctor_get(x_15, 3);
lean_inc(x_25);
lean_inc(x_23);
lean_dec(x_15);
x_26 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_10);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_24);
x_27 = lean_array_push(x_5, x_26);
x_3 = x_12;
x_5 = x_27;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_7, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_7, 4);
lean_inc(x_31);
lean_dec(x_7);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_29, sizeof(void*)*4);
x_35 = lean_ctor_get(x_29, 3);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 4, 1);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_34);
x_38 = lean_array_push(x_5, x_37);
x_3 = x_12;
x_5 = x_38;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = 1;
x_10 = l_Lean_Name_toString(x_1, x_9);
x_11 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = 3;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_array_get_size(x_7);
x_18 = lean_array_push(x_7, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_9, x_1);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_41; lean_object* x_42; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec(x_17);
x_42 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_5, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_box(0);
x_44 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__2(x_41, x_43, x_5, x_6, x_7, x_8, x_9, x_10);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_20 = x_45;
x_21 = x_46;
goto block_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_49, x_5);
lean_dec(x_49);
lean_inc(x_1);
lean_inc(x_6);
x_51 = lean_apply_7(x_1, x_47, x_50, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_53, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_54, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_55);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_54, 0, x_66);
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_54, 1);
lean_inc(x_67);
lean_dec(x_54);
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_55, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_70 = x_55;
} else {
 lean_dec_ref(x_55);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
lean_ctor_set(x_53, 0, x_72);
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
lean_dec(x_53);
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_75 = x_54;
} else {
 lean_dec_ref(x_54);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_55, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_78 = x_55;
} else {
 lean_dec_ref(x_55);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
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
lean_ctor_set(x_52, 0, x_81);
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_52, 1);
lean_inc(x_82);
lean_dec(x_52);
x_83 = lean_ctor_get(x_53, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_84 = x_53;
} else {
 lean_dec_ref(x_53);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_54, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_86 = x_54;
} else {
 lean_dec_ref(x_54);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_55, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_55, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_89 = x_55;
} else {
 lean_dec_ref(x_55);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
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
if (lean_is_scalar(x_84)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_84;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_83);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_82);
x_20 = x_93;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_51, 1);
lean_inc(x_94);
lean_dec(x_51);
x_95 = !lean_is_exclusive(x_52);
if (x_95 == 0)
{
x_20 = x_52;
x_21 = x_94;
goto block_40;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_52, 0);
x_97 = lean_ctor_get(x_52, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_52);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_20 = x_98;
x_21 = x_94;
goto block_40;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_51);
if (x_99 == 0)
{
return x_51;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_51, 0);
x_101 = lean_ctor_get(x_51, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_51);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
block_40:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_array_uset(x_19, x_3, x_28);
x_3 = x_31;
x_4 = x_32;
x_5 = x_29;
x_7 = x_27;
x_8 = x_26;
x_9 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_21);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_21);
return x_39;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_41; lean_object* x_42; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec(x_17);
x_42 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_5, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_box(0);
x_44 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__2(x_41, x_43, x_5, x_6, x_7, x_8, x_9, x_10);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_20 = x_45;
x_21 = x_46;
goto block_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_49, x_5);
lean_dec(x_49);
lean_inc(x_1);
lean_inc(x_6);
x_51 = lean_apply_7(x_1, x_47, x_50, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_53, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_54, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_55);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_54, 0, x_66);
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_54, 1);
lean_inc(x_67);
lean_dec(x_54);
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_55, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_70 = x_55;
} else {
 lean_dec_ref(x_55);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
lean_ctor_set(x_53, 0, x_72);
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
lean_dec(x_53);
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_75 = x_54;
} else {
 lean_dec_ref(x_54);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_55, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_78 = x_55;
} else {
 lean_dec_ref(x_55);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
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
lean_ctor_set(x_52, 0, x_81);
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_52, 1);
lean_inc(x_82);
lean_dec(x_52);
x_83 = lean_ctor_get(x_53, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_84 = x_53;
} else {
 lean_dec_ref(x_53);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_54, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_86 = x_54;
} else {
 lean_dec_ref(x_54);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_55, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_55, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_89 = x_55;
} else {
 lean_dec_ref(x_55);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
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
if (lean_is_scalar(x_84)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_84;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_83);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_82);
x_20 = x_93;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_51, 1);
lean_inc(x_94);
lean_dec(x_51);
x_95 = !lean_is_exclusive(x_52);
if (x_95 == 0)
{
x_20 = x_52;
x_21 = x_94;
goto block_40;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_52, 0);
x_97 = lean_ctor_get(x_52, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_52);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_20 = x_98;
x_21 = x_94;
goto block_40;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_51);
if (x_99 == 0)
{
return x_51;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_51, 0);
x_101 = lean_ctor_get(x_51, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_51);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
block_40:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_array_uset(x_19, x_3, x_28);
x_3 = x_31;
x_4 = x_32;
x_5 = x_29;
x_7 = x_27;
x_8 = x_26;
x_9 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_21);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_21);
return x_39;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_87; 
x_87 = l_Lake_updateDep(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_88, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_89, 1);
x_96 = lean_ctor_get(x_89, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_90);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_90, 1);
lean_ctor_set(x_90, 1, x_5);
lean_ctor_set(x_89, 1, x_98);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_89);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_88, 0, x_99);
x_11 = x_88;
x_12 = x_91;
goto block_86;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_90, 0);
x_101 = lean_ctor_get(x_90, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_90);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_5);
lean_ctor_set(x_89, 1, x_101);
lean_ctor_set(x_89, 0, x_102);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_89);
lean_ctor_set(x_103, 1, x_95);
lean_ctor_set(x_88, 0, x_103);
x_11 = x_88;
x_12 = x_91;
goto block_86;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_89, 1);
lean_inc(x_104);
lean_dec(x_89);
x_105 = lean_ctor_get(x_90, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_90, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_107 = x_90;
} else {
 lean_dec_ref(x_90);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_5);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_104);
lean_ctor_set(x_88, 0, x_110);
x_11 = x_88;
x_12 = x_91;
goto block_86;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_111 = lean_ctor_get(x_88, 1);
lean_inc(x_111);
lean_dec(x_88);
x_112 = lean_ctor_get(x_89, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_113 = x_89;
} else {
 lean_dec_ref(x_89);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_90, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_90, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_116 = x_90;
} else {
 lean_dec_ref(x_90);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_5);
if (lean_is_scalar(x_113)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_113;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_112);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_111);
x_11 = x_120;
x_12 = x_91;
goto block_86;
}
}
else
{
lean_object* x_121; uint8_t x_122; 
lean_dec(x_5);
x_121 = lean_ctor_get(x_87, 1);
lean_inc(x_121);
lean_dec(x_87);
x_122 = !lean_is_exclusive(x_88);
if (x_122 == 0)
{
x_11 = x_88;
x_12 = x_121;
goto block_86;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_88, 0);
x_124 = lean_ctor_get(x_88, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_88);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_11 = x_125;
x_12 = x_121;
goto block_86;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_5);
x_126 = !lean_is_exclusive(x_87);
if (x_126 == 0)
{
return x_87;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_87, 0);
x_128 = lean_ctor_get(x_87, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_87);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
block_86:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
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
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_24, x_26, x_23);
x_28 = lean_box(0);
lean_ctor_set(x_15, 1, x_27);
lean_ctor_set(x_15, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_31, x_33, x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_14, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
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
x_42 = lean_ctor_get(x_39, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_40, x_43, x_39);
x_45 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
lean_ctor_set(x_13, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_11);
lean_ctor_set(x_48, 1, x_12);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
lean_dec(x_13);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_51 = x_14;
} else {
 lean_dec_ref(x_14);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_15, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_15, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_54 = x_15;
} else {
 lean_dec_ref(x_15);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_53, x_56, x_52);
x_58 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_54;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
lean_ctor_set(x_11, 0, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_11);
lean_ctor_set(x_62, 1, x_12);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = lean_ctor_get(x_11, 1);
lean_inc(x_63);
lean_dec(x_11);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_65 = x_13;
} else {
 lean_dec_ref(x_13);
 x_65 = lean_box(0);
}
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
x_68 = lean_ctor_get(x_15, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_15, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_70 = x_15;
} else {
 lean_dec_ref(x_15);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_68, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 2);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_69, x_72, x_68);
x_74 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_70;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
if (lean_is_scalar(x_67)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_67;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_66);
if (lean_is_scalar(x_65)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_65;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_64);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_63);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_12);
return x_79;
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_11);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_11);
lean_ctor_set(x_81, 1, x_12);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_11, 0);
x_83 = lean_ctor_get(x_11, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_11);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_12);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_name_eq(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__1(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
x_18 = l_Lean_Name_toString(x_12, x_17);
x_19 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_array_get_size(x_9);
x_26 = lean_array_push(x_9, x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__2(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_4, x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = l_Lean_NameMap_contains___rarg(x_7, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
lean_inc(x_1);
lean_inc(x_2);
x_18 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__3(x_2, x_14, x_1, x_17, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = 1;
x_30 = lean_usize_add(x_4, x_29);
x_4 = x_30;
x_6 = x_27;
x_7 = x_28;
x_9 = x_26;
x_10 = x_25;
x_11 = x_24;
x_12 = x_23;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_18, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_18;
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
lean_ctor_set(x_18, 0, x_37);
return x_18;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_dec(x_18);
x_39 = lean_ctor_get(x_19, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_41 = x_19;
} else {
 lean_dec_ref(x_19);
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
lean_dec(x_2);
lean_dec(x_1);
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
size_t x_48; size_t x_49; lean_object* x_50; 
lean_dec(x_14);
x_48 = 1;
x_49 = lean_usize_add(x_4, x_48);
x_50 = lean_box(0);
x_4 = x_49;
x_6 = x_50;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_6);
lean_ctor_set(x_52, 1, x_7);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_9);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_10);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_12);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_41; lean_object* x_42; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec(x_17);
x_42 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_5, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_box(0);
x_44 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__2(x_41, x_43, x_5, x_6, x_7, x_8, x_9, x_10);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_20 = x_45;
x_21 = x_46;
goto block_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_49, x_5);
lean_dec(x_49);
lean_inc(x_1);
lean_inc(x_6);
x_51 = lean_apply_7(x_1, x_47, x_50, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_53, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_54, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_55);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_54, 0, x_66);
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_54, 1);
lean_inc(x_67);
lean_dec(x_54);
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_55, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_70 = x_55;
} else {
 lean_dec_ref(x_55);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
lean_ctor_set(x_53, 0, x_72);
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
lean_dec(x_53);
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_75 = x_54;
} else {
 lean_dec_ref(x_54);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_55, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_78 = x_55;
} else {
 lean_dec_ref(x_55);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
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
lean_ctor_set(x_52, 0, x_81);
x_20 = x_52;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_52, 1);
lean_inc(x_82);
lean_dec(x_52);
x_83 = lean_ctor_get(x_53, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_84 = x_53;
} else {
 lean_dec_ref(x_53);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_54, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_86 = x_54;
} else {
 lean_dec_ref(x_54);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_55, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_55, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_89 = x_55;
} else {
 lean_dec_ref(x_55);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
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
if (lean_is_scalar(x_84)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_84;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_83);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_82);
x_20 = x_93;
x_21 = x_56;
goto block_40;
}
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_51, 1);
lean_inc(x_94);
lean_dec(x_51);
x_95 = !lean_is_exclusive(x_52);
if (x_95 == 0)
{
x_20 = x_52;
x_21 = x_94;
goto block_40;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_52, 0);
x_97 = lean_ctor_get(x_52, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_52);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_20 = x_98;
x_21 = x_94;
goto block_40;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_51);
if (x_99 == 0)
{
return x_51;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_51, 0);
x_101 = lean_ctor_get(x_51, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_51);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
block_40:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_array_uset(x_19, x_3, x_28);
x_3 = x_31;
x_4 = x_32;
x_5 = x_29;
x_7 = x_27;
x_8 = x_26;
x_9 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_21);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_21);
return x_39;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_updateAndMaterialize___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 9);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 10);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 11);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 12);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 13);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 14);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 15);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 16);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 17);
lean_inc(x_26);
x_27 = lean_array_get_size(x_16);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; 
x_31 = lean_ctor_get(x_2, 17);
lean_dec(x_31);
x_32 = lean_ctor_get(x_2, 16);
lean_dec(x_32);
x_33 = lean_ctor_get(x_2, 15);
lean_dec(x_33);
x_34 = lean_ctor_get(x_2, 14);
lean_dec(x_34);
x_35 = lean_ctor_get(x_2, 13);
lean_dec(x_35);
x_36 = lean_ctor_get(x_2, 12);
lean_dec(x_36);
x_37 = lean_ctor_get(x_2, 11);
lean_dec(x_37);
x_38 = lean_ctor_get(x_2, 10);
lean_dec(x_38);
x_39 = lean_ctor_get(x_2, 9);
lean_dec(x_39);
x_40 = lean_ctor_get(x_2, 8);
lean_dec(x_40);
x_41 = lean_ctor_get(x_2, 7);
lean_dec(x_41);
x_42 = lean_ctor_get(x_2, 6);
lean_dec(x_42);
x_43 = lean_ctor_get(x_2, 5);
lean_dec(x_43);
x_44 = lean_ctor_get(x_2, 4);
lean_dec(x_44);
x_45 = lean_ctor_get(x_2, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_2, 2);
lean_dec(x_46);
x_47 = lean_ctor_get(x_2, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_2, 0);
lean_dec(x_48);
x_49 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_50 = 0;
lean_inc(x_16);
x_51 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5(x_3, x_49, x_50, x_16, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_51, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_52);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_52, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_53);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_53, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_54, 1);
x_64 = lean_ctor_get(x_54, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_55, 0);
lean_ctor_set(x_2, 6, x_66);
lean_inc(x_2);
x_67 = l_Lake_Workspace_addPackage(x_2, x_63);
lean_ctor_set(x_55, 0, x_2);
lean_ctor_set(x_54, 1, x_67);
return x_51;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_55, 0);
x_69 = lean_ctor_get(x_55, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_55);
lean_ctor_set(x_2, 6, x_68);
lean_inc(x_2);
x_70 = l_Lake_Workspace_addPackage(x_2, x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_2);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_54, 1, x_70);
lean_ctor_set(x_54, 0, x_71);
return x_51;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_54, 1);
lean_inc(x_72);
lean_dec(x_54);
x_73 = lean_ctor_get(x_55, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_55, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_75 = x_55;
} else {
 lean_dec_ref(x_55);
 x_75 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_73);
lean_inc(x_2);
x_76 = l_Lake_Workspace_addPackage(x_2, x_72);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_53, 0, x_78);
return x_51;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_53, 1);
lean_inc(x_79);
lean_dec(x_53);
x_80 = lean_ctor_get(x_54, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_81 = x_54;
} else {
 lean_dec_ref(x_54);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_55, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_55, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_84 = x_55;
} else {
 lean_dec_ref(x_55);
 x_84 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_82);
lean_inc(x_2);
x_85 = l_Lake_Workspace_addPackage(x_2, x_80);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_2);
lean_ctor_set(x_86, 1, x_83);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_79);
lean_ctor_set(x_52, 0, x_88);
return x_51;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_52, 1);
lean_inc(x_89);
lean_dec(x_52);
x_90 = lean_ctor_get(x_53, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_91 = x_53;
} else {
 lean_dec_ref(x_53);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_54, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_93 = x_54;
} else {
 lean_dec_ref(x_54);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_55, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_55, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_96 = x_55;
} else {
 lean_dec_ref(x_55);
 x_96 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_94);
lean_inc(x_2);
x_97 = l_Lake_Workspace_addPackage(x_2, x_92);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_2);
lean_ctor_set(x_98, 1, x_95);
if (lean_is_scalar(x_93)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_93;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_90);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_89);
lean_ctor_set(x_51, 0, x_101);
return x_51;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_102 = lean_ctor_get(x_51, 1);
lean_inc(x_102);
lean_dec(x_51);
x_103 = lean_ctor_get(x_52, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_104 = x_52;
} else {
 lean_dec_ref(x_52);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_53, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_106 = x_53;
} else {
 lean_dec_ref(x_53);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_54, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_108 = x_54;
} else {
 lean_dec_ref(x_54);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_55, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_55, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_111 = x_55;
} else {
 lean_dec_ref(x_55);
 x_111 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_109);
lean_inc(x_2);
x_112 = l_Lake_Workspace_addPackage(x_2, x_107);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_2);
lean_ctor_set(x_113, 1, x_110);
if (lean_is_scalar(x_108)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_108;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
if (lean_is_scalar(x_106)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_106;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_105);
if (lean_is_scalar(x_104)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_104;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_103);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_102);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_free_object(x_2);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_118 = !lean_is_exclusive(x_51);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_51, 0);
lean_dec(x_119);
x_120 = !lean_is_exclusive(x_52);
if (x_120 == 0)
{
return x_51;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_52, 0);
x_122 = lean_ctor_get(x_52, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_52);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_51, 0, x_123);
return x_51;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_51, 1);
lean_inc(x_124);
lean_dec(x_51);
x_125 = lean_ctor_get(x_52, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_52, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_127 = x_52;
} else {
 lean_dec_ref(x_52);
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
lean_free_object(x_2);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_130 = !lean_is_exclusive(x_51);
if (x_130 == 0)
{
return x_51;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_51, 0);
x_132 = lean_ctor_get(x_51, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_51);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
size_t x_134; size_t x_135; lean_object* x_136; 
lean_dec(x_2);
x_134 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_135 = 0;
lean_inc(x_16);
x_136 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5(x_3, x_134, x_135, x_16, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_142 = x_136;
} else {
 lean_dec_ref(x_136);
 x_142 = lean_box(0);
}
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
x_145 = lean_ctor_get(x_138, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_146 = x_138;
} else {
 lean_dec_ref(x_138);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_139, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_148 = x_139;
} else {
 lean_dec_ref(x_139);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_140, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_140, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_151 = x_140;
} else {
 lean_dec_ref(x_140);
 x_151 = lean_box(0);
}
x_152 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_152, 0, x_10);
lean_ctor_set(x_152, 1, x_11);
lean_ctor_set(x_152, 2, x_12);
lean_ctor_set(x_152, 3, x_13);
lean_ctor_set(x_152, 4, x_14);
lean_ctor_set(x_152, 5, x_15);
lean_ctor_set(x_152, 6, x_149);
lean_ctor_set(x_152, 7, x_16);
lean_ctor_set(x_152, 8, x_17);
lean_ctor_set(x_152, 9, x_18);
lean_ctor_set(x_152, 10, x_19);
lean_ctor_set(x_152, 11, x_20);
lean_ctor_set(x_152, 12, x_21);
lean_ctor_set(x_152, 13, x_22);
lean_ctor_set(x_152, 14, x_23);
lean_ctor_set(x_152, 15, x_24);
lean_ctor_set(x_152, 16, x_25);
lean_ctor_set(x_152, 17, x_26);
lean_inc(x_152);
x_153 = l_Lake_Workspace_addPackage(x_152, x_147);
if (lean_is_scalar(x_151)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_151;
}
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_150);
if (lean_is_scalar(x_148)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_148;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
if (lean_is_scalar(x_146)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_146;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_145);
if (lean_is_scalar(x_144)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_144;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_143);
if (lean_is_scalar(x_142)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_142;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_141);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
x_162 = lean_ctor_get(x_137, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_163 = x_137;
} else {
 lean_dec_ref(x_137);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
if (lean_is_scalar(x_160)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_160;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_159);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_166 = lean_ctor_get(x_136, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_136, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_168 = x_136;
} else {
 lean_dec_ref(x_136);
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
uint8_t x_170; 
x_170 = lean_nat_dec_le(x_27, x_27);
if (x_170 == 0)
{
uint8_t x_171; 
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_2);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; size_t x_190; size_t x_191; lean_object* x_192; 
x_172 = lean_ctor_get(x_2, 17);
lean_dec(x_172);
x_173 = lean_ctor_get(x_2, 16);
lean_dec(x_173);
x_174 = lean_ctor_get(x_2, 15);
lean_dec(x_174);
x_175 = lean_ctor_get(x_2, 14);
lean_dec(x_175);
x_176 = lean_ctor_get(x_2, 13);
lean_dec(x_176);
x_177 = lean_ctor_get(x_2, 12);
lean_dec(x_177);
x_178 = lean_ctor_get(x_2, 11);
lean_dec(x_178);
x_179 = lean_ctor_get(x_2, 10);
lean_dec(x_179);
x_180 = lean_ctor_get(x_2, 9);
lean_dec(x_180);
x_181 = lean_ctor_get(x_2, 8);
lean_dec(x_181);
x_182 = lean_ctor_get(x_2, 7);
lean_dec(x_182);
x_183 = lean_ctor_get(x_2, 6);
lean_dec(x_183);
x_184 = lean_ctor_get(x_2, 5);
lean_dec(x_184);
x_185 = lean_ctor_get(x_2, 4);
lean_dec(x_185);
x_186 = lean_ctor_get(x_2, 3);
lean_dec(x_186);
x_187 = lean_ctor_get(x_2, 2);
lean_dec(x_187);
x_188 = lean_ctor_get(x_2, 1);
lean_dec(x_188);
x_189 = lean_ctor_get(x_2, 0);
lean_dec(x_189);
x_190 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_191 = 0;
lean_inc(x_16);
x_192 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__6(x_3, x_190, x_191, x_16, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = !lean_is_exclusive(x_192);
if (x_197 == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_192, 0);
lean_dec(x_198);
x_199 = !lean_is_exclusive(x_193);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_ctor_get(x_193, 0);
lean_dec(x_200);
x_201 = !lean_is_exclusive(x_194);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_194, 0);
lean_dec(x_202);
x_203 = !lean_is_exclusive(x_195);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_204 = lean_ctor_get(x_195, 1);
x_205 = lean_ctor_get(x_195, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_196);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_196, 0);
lean_ctor_set(x_2, 6, x_207);
lean_inc(x_2);
x_208 = l_Lake_Workspace_addPackage(x_2, x_204);
lean_ctor_set(x_196, 0, x_2);
lean_ctor_set(x_195, 1, x_208);
return x_192;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_196, 0);
x_210 = lean_ctor_get(x_196, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_196);
lean_ctor_set(x_2, 6, x_209);
lean_inc(x_2);
x_211 = l_Lake_Workspace_addPackage(x_2, x_204);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_2);
lean_ctor_set(x_212, 1, x_210);
lean_ctor_set(x_195, 1, x_211);
lean_ctor_set(x_195, 0, x_212);
return x_192;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_213 = lean_ctor_get(x_195, 1);
lean_inc(x_213);
lean_dec(x_195);
x_214 = lean_ctor_get(x_196, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_196, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_216 = x_196;
} else {
 lean_dec_ref(x_196);
 x_216 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_214);
lean_inc(x_2);
x_217 = l_Lake_Workspace_addPackage(x_2, x_213);
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_216;
}
lean_ctor_set(x_218, 0, x_2);
lean_ctor_set(x_218, 1, x_215);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
lean_ctor_set(x_194, 0, x_219);
return x_192;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_220 = lean_ctor_get(x_194, 1);
lean_inc(x_220);
lean_dec(x_194);
x_221 = lean_ctor_get(x_195, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_222 = x_195;
} else {
 lean_dec_ref(x_195);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_196, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_196, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_225 = x_196;
} else {
 lean_dec_ref(x_196);
 x_225 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_223);
lean_inc(x_2);
x_226 = l_Lake_Workspace_addPackage(x_2, x_221);
if (lean_is_scalar(x_225)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_225;
}
lean_ctor_set(x_227, 0, x_2);
lean_ctor_set(x_227, 1, x_224);
if (lean_is_scalar(x_222)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_222;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_220);
lean_ctor_set(x_193, 0, x_229);
return x_192;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_230 = lean_ctor_get(x_193, 1);
lean_inc(x_230);
lean_dec(x_193);
x_231 = lean_ctor_get(x_194, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_232 = x_194;
} else {
 lean_dec_ref(x_194);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_195, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_234 = x_195;
} else {
 lean_dec_ref(x_195);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_196, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_196, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_237 = x_196;
} else {
 lean_dec_ref(x_196);
 x_237 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_235);
lean_inc(x_2);
x_238 = l_Lake_Workspace_addPackage(x_2, x_233);
if (lean_is_scalar(x_237)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_237;
}
lean_ctor_set(x_239, 0, x_2);
lean_ctor_set(x_239, 1, x_236);
if (lean_is_scalar(x_234)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_234;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
if (lean_is_scalar(x_232)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_232;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_231);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_230);
lean_ctor_set(x_192, 0, x_242);
return x_192;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_243 = lean_ctor_get(x_192, 1);
lean_inc(x_243);
lean_dec(x_192);
x_244 = lean_ctor_get(x_193, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_245 = x_193;
} else {
 lean_dec_ref(x_193);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_194, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_247 = x_194;
} else {
 lean_dec_ref(x_194);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_195, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_249 = x_195;
} else {
 lean_dec_ref(x_195);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_196, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_196, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_252 = x_196;
} else {
 lean_dec_ref(x_196);
 x_252 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_250);
lean_inc(x_2);
x_253 = l_Lake_Workspace_addPackage(x_2, x_248);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_252;
}
lean_ctor_set(x_254, 0, x_2);
lean_ctor_set(x_254, 1, x_251);
if (lean_is_scalar(x_249)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_249;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
if (lean_is_scalar(x_247)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_247;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_246);
if (lean_is_scalar(x_245)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_245;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_244);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_243);
return x_258;
}
}
else
{
uint8_t x_259; 
lean_free_object(x_2);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_259 = !lean_is_exclusive(x_192);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_192, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_193);
if (x_261 == 0)
{
return x_192;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_193, 0);
x_263 = lean_ctor_get(x_193, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_193);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_192, 0, x_264);
return x_192;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_265 = lean_ctor_get(x_192, 1);
lean_inc(x_265);
lean_dec(x_192);
x_266 = lean_ctor_get(x_193, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_193, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_268 = x_193;
} else {
 lean_dec_ref(x_193);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_265);
return x_270;
}
}
}
else
{
uint8_t x_271; 
lean_free_object(x_2);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_271 = !lean_is_exclusive(x_192);
if (x_271 == 0)
{
return x_192;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_192, 0);
x_273 = lean_ctor_get(x_192, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_192);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
else
{
size_t x_275; size_t x_276; lean_object* x_277; 
lean_dec(x_2);
x_275 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_276 = 0;
lean_inc(x_16);
x_277 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__6(x_3, x_275, x_276, x_16, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_277, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_283 = x_277;
} else {
 lean_dec_ref(x_277);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_278, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_285 = x_278;
} else {
 lean_dec_ref(x_278);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_279, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_287 = x_279;
} else {
 lean_dec_ref(x_279);
 x_287 = lean_box(0);
}
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
x_290 = lean_ctor_get(x_281, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_281, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_292 = x_281;
} else {
 lean_dec_ref(x_281);
 x_292 = lean_box(0);
}
x_293 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_293, 0, x_10);
lean_ctor_set(x_293, 1, x_11);
lean_ctor_set(x_293, 2, x_12);
lean_ctor_set(x_293, 3, x_13);
lean_ctor_set(x_293, 4, x_14);
lean_ctor_set(x_293, 5, x_15);
lean_ctor_set(x_293, 6, x_290);
lean_ctor_set(x_293, 7, x_16);
lean_ctor_set(x_293, 8, x_17);
lean_ctor_set(x_293, 9, x_18);
lean_ctor_set(x_293, 10, x_19);
lean_ctor_set(x_293, 11, x_20);
lean_ctor_set(x_293, 12, x_21);
lean_ctor_set(x_293, 13, x_22);
lean_ctor_set(x_293, 14, x_23);
lean_ctor_set(x_293, 15, x_24);
lean_ctor_set(x_293, 16, x_25);
lean_ctor_set(x_293, 17, x_26);
lean_inc(x_293);
x_294 = l_Lake_Workspace_addPackage(x_293, x_288);
if (lean_is_scalar(x_292)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_292;
}
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_291);
if (lean_is_scalar(x_289)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_289;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_294);
if (lean_is_scalar(x_287)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_287;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_286);
if (lean_is_scalar(x_285)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_285;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_283;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_282);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_300 = lean_ctor_get(x_277, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_301 = x_277;
} else {
 lean_dec_ref(x_277);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_278, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_278, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_304 = x_278;
} else {
 lean_dec_ref(x_278);
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
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_307 = lean_ctor_get(x_277, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_277, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_309 = x_277;
} else {
 lean_dec_ref(x_277);
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
size_t x_311; size_t x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_311 = 0;
x_312 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_313 = lean_box(0);
lean_inc(x_2);
x_314 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7(x_1, x_2, x_16, x_311, x_312, x_313, x_4, x_5, x_6, x_7, x_8, x_9);
x_315 = !lean_is_exclusive(x_2);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_316 = lean_ctor_get(x_2, 17);
lean_dec(x_316);
x_317 = lean_ctor_get(x_2, 16);
lean_dec(x_317);
x_318 = lean_ctor_get(x_2, 15);
lean_dec(x_318);
x_319 = lean_ctor_get(x_2, 14);
lean_dec(x_319);
x_320 = lean_ctor_get(x_2, 13);
lean_dec(x_320);
x_321 = lean_ctor_get(x_2, 12);
lean_dec(x_321);
x_322 = lean_ctor_get(x_2, 11);
lean_dec(x_322);
x_323 = lean_ctor_get(x_2, 10);
lean_dec(x_323);
x_324 = lean_ctor_get(x_2, 9);
lean_dec(x_324);
x_325 = lean_ctor_get(x_2, 8);
lean_dec(x_325);
x_326 = lean_ctor_get(x_2, 7);
lean_dec(x_326);
x_327 = lean_ctor_get(x_2, 6);
lean_dec(x_327);
x_328 = lean_ctor_get(x_2, 5);
lean_dec(x_328);
x_329 = lean_ctor_get(x_2, 4);
lean_dec(x_329);
x_330 = lean_ctor_get(x_2, 3);
lean_dec(x_330);
x_331 = lean_ctor_get(x_2, 2);
lean_dec(x_331);
x_332 = lean_ctor_get(x_2, 1);
lean_dec(x_332);
x_333 = lean_ctor_get(x_2, 0);
lean_dec(x_333);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_314, 0);
lean_inc(x_334);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_314, 1);
lean_inc(x_338);
lean_dec(x_314);
x_339 = lean_ctor_get(x_334, 1);
lean_inc(x_339);
lean_dec(x_334);
x_340 = lean_ctor_get(x_335, 1);
lean_inc(x_340);
lean_dec(x_335);
x_341 = lean_ctor_get(x_336, 1);
lean_inc(x_341);
lean_dec(x_336);
x_342 = lean_ctor_get(x_337, 1);
lean_inc(x_342);
lean_dec(x_337);
lean_inc(x_16);
x_343 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8(x_3, x_312, x_311, x_16, x_342, x_5, x_341, x_340, x_339, x_338);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = !lean_is_exclusive(x_343);
if (x_348 == 0)
{
lean_object* x_349; uint8_t x_350; 
x_349 = lean_ctor_get(x_343, 0);
lean_dec(x_349);
x_350 = !lean_is_exclusive(x_344);
if (x_350 == 0)
{
lean_object* x_351; uint8_t x_352; 
x_351 = lean_ctor_get(x_344, 0);
lean_dec(x_351);
x_352 = !lean_is_exclusive(x_345);
if (x_352 == 0)
{
lean_object* x_353; uint8_t x_354; 
x_353 = lean_ctor_get(x_345, 0);
lean_dec(x_353);
x_354 = !lean_is_exclusive(x_346);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_355 = lean_ctor_get(x_346, 1);
x_356 = lean_ctor_get(x_346, 0);
lean_dec(x_356);
x_357 = !lean_is_exclusive(x_347);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_347, 0);
lean_ctor_set(x_2, 6, x_358);
lean_inc(x_2);
x_359 = l_Lake_Workspace_addPackage(x_2, x_355);
lean_ctor_set(x_347, 0, x_2);
lean_ctor_set(x_346, 1, x_359);
return x_343;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_360 = lean_ctor_get(x_347, 0);
x_361 = lean_ctor_get(x_347, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_347);
lean_ctor_set(x_2, 6, x_360);
lean_inc(x_2);
x_362 = l_Lake_Workspace_addPackage(x_2, x_355);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_2);
lean_ctor_set(x_363, 1, x_361);
lean_ctor_set(x_346, 1, x_362);
lean_ctor_set(x_346, 0, x_363);
return x_343;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_364 = lean_ctor_get(x_346, 1);
lean_inc(x_364);
lean_dec(x_346);
x_365 = lean_ctor_get(x_347, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_347, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_367 = x_347;
} else {
 lean_dec_ref(x_347);
 x_367 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_365);
lean_inc(x_2);
x_368 = l_Lake_Workspace_addPackage(x_2, x_364);
if (lean_is_scalar(x_367)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_367;
}
lean_ctor_set(x_369, 0, x_2);
lean_ctor_set(x_369, 1, x_366);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_368);
lean_ctor_set(x_345, 0, x_370);
return x_343;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_371 = lean_ctor_get(x_345, 1);
lean_inc(x_371);
lean_dec(x_345);
x_372 = lean_ctor_get(x_346, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_373 = x_346;
} else {
 lean_dec_ref(x_346);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_347, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_347, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_376 = x_347;
} else {
 lean_dec_ref(x_347);
 x_376 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_374);
lean_inc(x_2);
x_377 = l_Lake_Workspace_addPackage(x_2, x_372);
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_2);
lean_ctor_set(x_378, 1, x_375);
if (lean_is_scalar(x_373)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_373;
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_371);
lean_ctor_set(x_344, 0, x_380);
return x_343;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_381 = lean_ctor_get(x_344, 1);
lean_inc(x_381);
lean_dec(x_344);
x_382 = lean_ctor_get(x_345, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_383 = x_345;
} else {
 lean_dec_ref(x_345);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_346, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_385 = x_346;
} else {
 lean_dec_ref(x_346);
 x_385 = lean_box(0);
}
x_386 = lean_ctor_get(x_347, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_347, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_388 = x_347;
} else {
 lean_dec_ref(x_347);
 x_388 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_386);
lean_inc(x_2);
x_389 = l_Lake_Workspace_addPackage(x_2, x_384);
if (lean_is_scalar(x_388)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_388;
}
lean_ctor_set(x_390, 0, x_2);
lean_ctor_set(x_390, 1, x_387);
if (lean_is_scalar(x_385)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_385;
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_389);
if (lean_is_scalar(x_383)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_383;
}
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_382);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_381);
lean_ctor_set(x_343, 0, x_393);
return x_343;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_394 = lean_ctor_get(x_343, 1);
lean_inc(x_394);
lean_dec(x_343);
x_395 = lean_ctor_get(x_344, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_396 = x_344;
} else {
 lean_dec_ref(x_344);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_345, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_398 = x_345;
} else {
 lean_dec_ref(x_345);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_346, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_400 = x_346;
} else {
 lean_dec_ref(x_346);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_347, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_347, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_403 = x_347;
} else {
 lean_dec_ref(x_347);
 x_403 = lean_box(0);
}
lean_ctor_set(x_2, 6, x_401);
lean_inc(x_2);
x_404 = l_Lake_Workspace_addPackage(x_2, x_399);
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_2);
lean_ctor_set(x_405, 1, x_402);
if (lean_is_scalar(x_400)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_400;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_404);
if (lean_is_scalar(x_398)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_398;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_397);
if (lean_is_scalar(x_396)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_396;
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_395);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_394);
return x_409;
}
}
else
{
uint8_t x_410; 
lean_free_object(x_2);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_410 = !lean_is_exclusive(x_343);
if (x_410 == 0)
{
lean_object* x_411; uint8_t x_412; 
x_411 = lean_ctor_get(x_343, 0);
lean_dec(x_411);
x_412 = !lean_is_exclusive(x_344);
if (x_412 == 0)
{
return x_343;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_344, 0);
x_414 = lean_ctor_get(x_344, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_344);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
lean_ctor_set(x_343, 0, x_415);
return x_343;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_416 = lean_ctor_get(x_343, 1);
lean_inc(x_416);
lean_dec(x_343);
x_417 = lean_ctor_get(x_344, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_344, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_419 = x_344;
} else {
 lean_dec_ref(x_344);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_416);
return x_421;
}
}
}
else
{
uint8_t x_422; 
lean_free_object(x_2);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_422 = !lean_is_exclusive(x_343);
if (x_422 == 0)
{
return x_343;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_343, 0);
x_424 = lean_ctor_get(x_343, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_343);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
else
{
uint8_t x_426; 
lean_free_object(x_2);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_426 = !lean_is_exclusive(x_314);
if (x_426 == 0)
{
lean_object* x_427; uint8_t x_428; 
x_427 = lean_ctor_get(x_314, 0);
lean_dec(x_427);
x_428 = !lean_is_exclusive(x_334);
if (x_428 == 0)
{
return x_314;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_334, 0);
x_430 = lean_ctor_get(x_334, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_334);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
lean_ctor_set(x_314, 0, x_431);
return x_314;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_432 = lean_ctor_get(x_314, 1);
lean_inc(x_432);
lean_dec(x_314);
x_433 = lean_ctor_get(x_334, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_334, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_435 = x_334;
} else {
 lean_dec_ref(x_334);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_432);
return x_437;
}
}
}
else
{
uint8_t x_438; 
lean_free_object(x_2);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_438 = !lean_is_exclusive(x_314);
if (x_438 == 0)
{
return x_314;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_314, 0);
x_440 = lean_ctor_get(x_314, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_314);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_442; 
x_442 = lean_ctor_get(x_314, 0);
lean_inc(x_442);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_314, 1);
lean_inc(x_446);
lean_dec(x_314);
x_447 = lean_ctor_get(x_442, 1);
lean_inc(x_447);
lean_dec(x_442);
x_448 = lean_ctor_get(x_443, 1);
lean_inc(x_448);
lean_dec(x_443);
x_449 = lean_ctor_get(x_444, 1);
lean_inc(x_449);
lean_dec(x_444);
x_450 = lean_ctor_get(x_445, 1);
lean_inc(x_450);
lean_dec(x_445);
lean_inc(x_16);
x_451 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8(x_3, x_312, x_311, x_16, x_450, x_5, x_449, x_448, x_447, x_446);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_451, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_457 = x_451;
} else {
 lean_dec_ref(x_451);
 x_457 = lean_box(0);
}
x_458 = lean_ctor_get(x_452, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_459 = x_452;
} else {
 lean_dec_ref(x_452);
 x_459 = lean_box(0);
}
x_460 = lean_ctor_get(x_453, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_461 = x_453;
} else {
 lean_dec_ref(x_453);
 x_461 = lean_box(0);
}
x_462 = lean_ctor_get(x_454, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 lean_ctor_release(x_454, 1);
 x_463 = x_454;
} else {
 lean_dec_ref(x_454);
 x_463 = lean_box(0);
}
x_464 = lean_ctor_get(x_455, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_455, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_466 = x_455;
} else {
 lean_dec_ref(x_455);
 x_466 = lean_box(0);
}
x_467 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_467, 0, x_10);
lean_ctor_set(x_467, 1, x_11);
lean_ctor_set(x_467, 2, x_12);
lean_ctor_set(x_467, 3, x_13);
lean_ctor_set(x_467, 4, x_14);
lean_ctor_set(x_467, 5, x_15);
lean_ctor_set(x_467, 6, x_464);
lean_ctor_set(x_467, 7, x_16);
lean_ctor_set(x_467, 8, x_17);
lean_ctor_set(x_467, 9, x_18);
lean_ctor_set(x_467, 10, x_19);
lean_ctor_set(x_467, 11, x_20);
lean_ctor_set(x_467, 12, x_21);
lean_ctor_set(x_467, 13, x_22);
lean_ctor_set(x_467, 14, x_23);
lean_ctor_set(x_467, 15, x_24);
lean_ctor_set(x_467, 16, x_25);
lean_ctor_set(x_467, 17, x_26);
lean_inc(x_467);
x_468 = l_Lake_Workspace_addPackage(x_467, x_462);
if (lean_is_scalar(x_466)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_466;
}
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_465);
if (lean_is_scalar(x_463)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_463;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_468);
if (lean_is_scalar(x_461)) {
 x_471 = lean_alloc_ctor(0, 2, 0);
} else {
 x_471 = x_461;
}
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_460);
if (lean_is_scalar(x_459)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_459;
}
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_458);
if (lean_is_scalar(x_457)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_457;
}
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_456);
return x_473;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_474 = lean_ctor_get(x_451, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_475 = x_451;
} else {
 lean_dec_ref(x_451);
 x_475 = lean_box(0);
}
x_476 = lean_ctor_get(x_452, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_452, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_478 = x_452;
} else {
 lean_dec_ref(x_452);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_476);
lean_ctor_set(x_479, 1, x_477);
if (lean_is_scalar(x_475)) {
 x_480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_480 = x_475;
}
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_474);
return x_480;
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_481 = lean_ctor_get(x_451, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_451, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_483 = x_451;
} else {
 lean_dec_ref(x_451);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_482);
return x_484;
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_485 = lean_ctor_get(x_314, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_486 = x_314;
} else {
 lean_dec_ref(x_314);
 x_486 = lean_box(0);
}
x_487 = lean_ctor_get(x_442, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_442, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_489 = x_442;
} else {
 lean_dec_ref(x_442);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
if (lean_is_scalar(x_486)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_486;
}
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_485);
return x_491;
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_492 = lean_ctor_get(x_314, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_314, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_494 = x_314;
} else {
 lean_dec_ref(x_314);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_492);
lean_ctor_set(x_495, 1, x_493);
return x_495;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__2(x_1, x_7);
x_9 = l_Lake_depCycleError___rarg___closed__2;
x_10 = l_String_intercalate(x_9, x_8);
x_11 = l_Lake_depCycleError___rarg___closed__3;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = 3;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_array_get_size(x_5);
x_18 = lean_array_push(x_5, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12(x_1, x_3, x_4, x_2, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_10, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_4);
lean_inc(x_12);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12___lambda__1___boxed), 9, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_updateAndMaterialize___spec__4(x_1, x_2, x_13, x_3, x_12, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___closed__1;
lean_inc(x_4);
x_17 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__10(x_10, x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_15);
x_21 = l_List_appendTR___rarg(x_19, x_20);
x_22 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11___rarg(x_21, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_updateAndMaterialize___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterialize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_135; lean_object* x_136; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_box(0);
lean_inc(x_1);
x_185 = l_Lake_reuseManifest(x_1, x_2, x_184, x_4, x_5);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_ctor_get(x_1, 0);
lean_inc(x_191);
x_192 = lean_box(0);
x_193 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12(x_3, x_191, x_184, x_192, x_1, x_190, x_189, x_188);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_193, 1);
lean_inc(x_198);
lean_dec(x_193);
x_199 = !lean_is_exclusive(x_194);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = lean_ctor_get(x_194, 0);
lean_dec(x_200);
x_201 = lean_ctor_get(x_195, 1);
lean_inc(x_201);
lean_dec(x_195);
x_202 = !lean_is_exclusive(x_196);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_ctor_get(x_196, 1);
x_204 = lean_ctor_get(x_196, 0);
lean_dec(x_204);
x_205 = !lean_is_exclusive(x_197);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_197, 1);
lean_dec(x_206);
lean_ctor_set(x_197, 1, x_203);
lean_ctor_set(x_196, 1, x_201);
lean_ctor_set(x_194, 0, x_196);
x_135 = x_194;
x_136 = x_198;
goto block_183;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_197, 0);
lean_inc(x_207);
lean_dec(x_197);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_203);
lean_ctor_set(x_196, 1, x_201);
lean_ctor_set(x_196, 0, x_208);
lean_ctor_set(x_194, 0, x_196);
x_135 = x_194;
x_136 = x_198;
goto block_183;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_196, 1);
lean_inc(x_209);
lean_dec(x_196);
x_210 = lean_ctor_get(x_197, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_211 = x_197;
} else {
 lean_dec_ref(x_197);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_209);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_201);
lean_ctor_set(x_194, 0, x_213);
x_135 = x_194;
x_136 = x_198;
goto block_183;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_214 = lean_ctor_get(x_194, 1);
lean_inc(x_214);
lean_dec(x_194);
x_215 = lean_ctor_get(x_195, 1);
lean_inc(x_215);
lean_dec(x_195);
x_216 = lean_ctor_get(x_196, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_217 = x_196;
} else {
 lean_dec_ref(x_196);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_197, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_219 = x_197;
} else {
 lean_dec_ref(x_197);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_216);
if (lean_is_scalar(x_217)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_217;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_215);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_214);
x_135 = x_222;
x_136 = x_198;
goto block_183;
}
}
else
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_ctor_get(x_193, 1);
lean_inc(x_223);
lean_dec(x_193);
x_224 = !lean_is_exclusive(x_194);
if (x_224 == 0)
{
x_135 = x_194;
x_136 = x_223;
goto block_183;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_194, 0);
x_226 = lean_ctor_get(x_194, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_194);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_135 = x_227;
x_136 = x_223;
goto block_183;
}
}
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_193);
if (x_228 == 0)
{
return x_193;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_193, 0);
x_230 = lean_ctor_get(x_193, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_193);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
else
{
lean_object* x_232; uint8_t x_233; 
lean_dec(x_3);
lean_dec(x_1);
x_232 = lean_ctor_get(x_185, 1);
lean_inc(x_232);
lean_dec(x_185);
x_233 = !lean_is_exclusive(x_186);
if (x_233 == 0)
{
x_6 = x_186;
x_7 = x_232;
goto block_134;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_186, 0);
x_235 = lean_ctor_get(x_186, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_186);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_6 = x_236;
x_7 = x_232;
goto block_134;
}
}
block_134:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_10 = x_6;
} else {
 lean_dec_ref(x_6);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_13 = x_8;
} else {
 lean_dec_ref(x_8);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_lt(x_95, x_15);
x_97 = lean_ctor_get(x_11, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 2);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_99);
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 4);
lean_inc(x_103);
lean_dec(x_97);
x_104 = l_System_FilePath_join(x_102, x_103);
if (x_96 == 0)
{
lean_object* x_121; 
lean_dec(x_12);
x_121 = l_Lake_Workspace_updateAndMaterialize___closed__1;
x_105 = x_121;
goto block_120;
}
else
{
uint8_t x_122; 
x_122 = lean_nat_dec_le(x_15, x_15);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_12);
x_123 = l_Lake_Workspace_updateAndMaterialize___closed__1;
x_105 = x_123;
goto block_120;
}
else
{
size_t x_124; size_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = 0;
x_125 = lean_usize_of_nat(x_15);
x_126 = l_Lake_Workspace_updateAndMaterialize___closed__1;
x_127 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3(x_12, x_14, x_124, x_125, x_126);
lean_dec(x_12);
x_105 = x_127;
goto block_120;
}
}
block_94:
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_15);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
lean_ctor_set(x_16, 0, x_11);
if (lean_is_scalar(x_13)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_13;
}
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_15, x_15);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_ctor_set(x_16, 0, x_11);
if (lean_is_scalar(x_13)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_13;
}
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_16);
lean_dec(x_13);
x_26 = 0;
x_27 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_28 = lean_box(0);
lean_inc(x_11);
x_29 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2(x_14, x_26, x_27, x_28, x_11, x_19, x_17);
lean_dec(x_14);
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
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_11);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_29, 0, x_36);
return x_29;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_39 = x_30;
} else {
 lean_dec_ref(x_30);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_29, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_29, 0, x_47);
return x_29;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_dec(x_29);
x_49 = lean_ctor_get(x_30, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_51 = x_30;
} else {
 lean_dec_ref(x_30);
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
lean_dec(x_11);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_29, 0);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_29);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
lean_dec(x_16);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_lt(x_59, x_15);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_15);
lean_dec(x_14);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_11);
lean_ctor_set(x_61, 1, x_58);
if (lean_is_scalar(x_13)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_13;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_17);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_15, x_15);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_15);
lean_dec(x_14);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_11);
lean_ctor_set(x_64, 1, x_58);
if (lean_is_scalar(x_13)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_13;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_17);
return x_65;
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_13);
x_66 = 0;
x_67 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_68 = lean_box(0);
lean_inc(x_11);
x_69 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2(x_14, x_66, x_67, x_68, x_11, x_58, x_17);
lean_dec(x_14);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
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
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_74 = x_70;
} else {
 lean_dec_ref(x_70);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_11);
lean_ctor_set(x_75, 1, x_73);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_11);
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
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_81 = x_70;
} else {
 lean_dec_ref(x_70);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
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
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_11);
x_84 = lean_ctor_get(x_69, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_69, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_86 = x_69;
} else {
 lean_dec_ref(x_69);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
x_88 = !lean_is_exclusive(x_16);
if (x_88 == 0)
{
lean_object* x_89; 
if (lean_is_scalar(x_13)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_13;
}
lean_ctor_set(x_89, 0, x_16);
lean_ctor_set(x_89, 1, x_17);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_16, 0);
x_91 = lean_ctor_get(x_16, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_16);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
if (lean_is_scalar(x_13)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_13;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_17);
return x_93;
}
}
}
block_120:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = l_Lake_defaultLakeDir;
x_107 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_107, 0, x_100);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_101);
lean_ctor_set(x_107, 3, x_105);
x_108 = l_Lake_Manifest_saveToFile(x_107, x_104, x_7);
lean_dec(x_104);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
if (lean_is_scalar(x_10)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_10;
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_9);
x_16 = x_111;
x_17 = x_110;
goto block_94;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_io_error_to_string(x_112);
x_115 = 3;
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = lean_array_get_size(x_9);
x_118 = lean_array_push(x_9, x_116);
if (lean_is_scalar(x_10)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_10;
 lean_ctor_set_tag(x_119, 1);
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_16 = x_119;
x_17 = x_113;
goto block_94;
}
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_6);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_6);
lean_ctor_set(x_129, 1, x_7);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_6, 0);
x_131 = lean_ctor_get(x_6, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_6);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_7);
return x_133;
}
}
}
block_183:
{
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
x_140 = !lean_is_exclusive(x_135);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_135, 0);
lean_dec(x_141);
x_142 = lean_ctor_get(x_137, 1);
lean_inc(x_142);
lean_dec(x_137);
x_143 = !lean_is_exclusive(x_138);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = lean_ctor_get(x_138, 0);
x_145 = lean_ctor_get(x_138, 1);
lean_dec(x_145);
x_146 = !lean_is_exclusive(x_139);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_139, 0);
lean_dec(x_147);
lean_ctor_set(x_139, 0, x_144);
lean_ctor_set(x_138, 1, x_142);
lean_ctor_set(x_138, 0, x_139);
lean_ctor_set(x_135, 0, x_138);
x_6 = x_135;
x_7 = x_136;
goto block_134;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_139, 1);
x_149 = lean_ctor_get(x_139, 2);
x_150 = lean_ctor_get(x_139, 3);
x_151 = lean_ctor_get(x_139, 4);
x_152 = lean_ctor_get(x_139, 5);
x_153 = lean_ctor_get(x_139, 6);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_139);
x_154 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_154, 0, x_144);
lean_ctor_set(x_154, 1, x_148);
lean_ctor_set(x_154, 2, x_149);
lean_ctor_set(x_154, 3, x_150);
lean_ctor_set(x_154, 4, x_151);
lean_ctor_set(x_154, 5, x_152);
lean_ctor_set(x_154, 6, x_153);
lean_ctor_set(x_138, 1, x_142);
lean_ctor_set(x_138, 0, x_154);
lean_ctor_set(x_135, 0, x_138);
x_6 = x_135;
x_7 = x_136;
goto block_134;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_155 = lean_ctor_get(x_138, 0);
lean_inc(x_155);
lean_dec(x_138);
x_156 = lean_ctor_get(x_139, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_139, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_139, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_139, 4);
lean_inc(x_159);
x_160 = lean_ctor_get(x_139, 5);
lean_inc(x_160);
x_161 = lean_ctor_get(x_139, 6);
lean_inc(x_161);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 lean_ctor_release(x_139, 2);
 lean_ctor_release(x_139, 3);
 lean_ctor_release(x_139, 4);
 lean_ctor_release(x_139, 5);
 lean_ctor_release(x_139, 6);
 x_162 = x_139;
} else {
 lean_dec_ref(x_139);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 7, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_155);
lean_ctor_set(x_163, 1, x_156);
lean_ctor_set(x_163, 2, x_157);
lean_ctor_set(x_163, 3, x_158);
lean_ctor_set(x_163, 4, x_159);
lean_ctor_set(x_163, 5, x_160);
lean_ctor_set(x_163, 6, x_161);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_142);
lean_ctor_set(x_135, 0, x_164);
x_6 = x_135;
x_7 = x_136;
goto block_134;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_165 = lean_ctor_get(x_135, 1);
lean_inc(x_165);
lean_dec(x_135);
x_166 = lean_ctor_get(x_137, 1);
lean_inc(x_166);
lean_dec(x_137);
x_167 = lean_ctor_get(x_138, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_168 = x_138;
} else {
 lean_dec_ref(x_138);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_139, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_139, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_139, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_139, 4);
lean_inc(x_172);
x_173 = lean_ctor_get(x_139, 5);
lean_inc(x_173);
x_174 = lean_ctor_get(x_139, 6);
lean_inc(x_174);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 lean_ctor_release(x_139, 2);
 lean_ctor_release(x_139, 3);
 lean_ctor_release(x_139, 4);
 lean_ctor_release(x_139, 5);
 lean_ctor_release(x_139, 6);
 x_175 = x_139;
} else {
 lean_dec_ref(x_139);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 7, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_167);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set(x_176, 4, x_172);
lean_ctor_set(x_176, 5, x_173);
lean_ctor_set(x_176, 6, x_174);
if (lean_is_scalar(x_168)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_168;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_166);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_165);
x_6 = x_178;
x_7 = x_136;
goto block_134;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_135);
if (x_179 == 0)
{
x_6 = x_135;
x_7 = x_136;
goto block_134;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_135, 0);
x_181 = lean_ctor_get(x_135, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_135);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_6 = x_182;
x_7 = x_136;
goto block_134;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__5(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__6(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__7(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterialize___spec__8(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterialize___spec__10(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterialize___spec__11(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterialize___spec__12___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_updateAndMaterialize(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("manifest out of date: ", 22);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("git revision", 12);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" of dependency '", 16);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__3;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' changed; use `lake update ", 28);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` to update it", 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; 
x_7 = l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(x_1, x_2);
x_8 = l_instDecidableNot___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = 1;
x_13 = l_Lean_Name_toString(x_3, x_12);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__5;
x_15 = lean_string_append(x_14, x_13);
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7;
x_20 = lean_string_append(x_18, x_19);
x_21 = 2;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_push(x_5, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("source kind (git/path)", 22);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("git url", 7);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__1;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__5;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_3, x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_17 = lean_array_uget(x_2, x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_1, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
x_8 = x_21;
x_9 = x_7;
goto block_15;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_22);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_18);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
x_8 = x_26;
x_9 = x_7;
goto block_15;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_27 = 1;
x_28 = l_Lean_Name_toString(x_18, x_27);
x_29 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__3;
x_30 = lean_string_append(x_29, x_28);
x_31 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_append(x_32, x_28);
lean_dec(x_28);
x_34 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7;
x_35 = lean_string_append(x_33, x_34);
x_36 = 2;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_push(x_6, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_8 = x_40;
x_9 = x_7;
goto block_15;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_19, 0);
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_42);
lean_dec(x_22);
x_43 = 1;
x_44 = l_Lean_Name_toString(x_18, x_43);
x_45 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__3;
x_46 = lean_string_append(x_45, x_44);
x_47 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_44);
lean_dec(x_44);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7;
x_51 = lean_string_append(x_49, x_50);
x_52 = 2;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_push(x_6, x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_8 = x_56;
x_9 = x_7;
goto block_15;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_22, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_dec(x_22);
x_59 = lean_ctor_get(x_42, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_42, 2);
lean_inc(x_60);
lean_dec(x_42);
x_61 = lean_string_dec_eq(x_57, x_59);
lean_dec(x_59);
lean_dec(x_57);
x_62 = l_instDecidableNot___rarg(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1(x_58, x_60, x_18, x_63, x_6, x_7);
lean_dec(x_60);
lean_dec(x_58);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_8 = x_65;
x_9 = x_66;
goto block_15;
}
else
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_67 = 1;
lean_inc(x_18);
x_68 = l_Lean_Name_toString(x_18, x_67);
x_69 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__6;
x_70 = lean_string_append(x_69, x_68);
x_71 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_string_append(x_72, x_68);
lean_dec(x_68);
x_74 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7;
x_75 = lean_string_append(x_73, x_74);
x_76 = 2;
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
x_78 = lean_array_push(x_6, x_77);
x_79 = lean_box(0);
x_80 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1(x_58, x_60, x_18, x_79, x_78, x_7);
lean_dec(x_60);
lean_dec(x_58);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_8 = x_81;
x_9 = x_82;
goto block_15;
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_5);
lean_ctor_set(x_83, 1, x_6);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_7);
return x_84;
}
block_15:
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_10;
x_6 = x_11;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
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
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_6, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1(x_2, x_1, x_16, x_17, x_18, x_4, x_5);
return x_19;
}
}
}
}
static lean_object* _init_l_Lake_validateManifest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("missing manifest; use `lake update` to generate one", 51);
return x_1;
}
}
static lean_object* _init_l_Lake_validateManifest___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_validateManifest___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_get_size(x_3);
x_7 = l_Lake_validateManifest___closed__2;
x_8 = lean_array_push(x_3, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lake_validateManifest___lambda__1(x_2, x_1, x_11, x_3, x_4);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lake_validateManifest___lambda__1(x_2, x_1, x_13, x_3, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_validateManifest___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_validateManifest(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = 1;
x_9 = l_Lean_Name_toString(x_1, x_8);
x_10 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = 3;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_get_size(x_6);
x_17 = lean_array_push(x_6, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
x_9 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_8, x_1);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_37; lean_object* x_38; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
lean_dec(x_15);
x_38 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_5, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_box(0);
x_40 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__2(x_37, x_39, x_5, x_6, x_7, x_8, x_9);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_18 = x_41;
x_19 = x_42;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_45, x_5);
lean_dec(x_45);
lean_inc(x_1);
lean_inc(x_6);
x_47 = lean_apply_6(x_1, x_43, x_46, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
x_18 = x_48;
x_19 = x_51;
goto block_36;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_49, 0, x_59);
x_18 = x_48;
x_19 = x_51;
goto block_36;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
lean_dec(x_49);
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
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_48, 0, x_65);
x_18 = x_48;
x_19 = x_51;
goto block_36;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_48, 1);
lean_inc(x_66);
lean_dec(x_48);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_68 = x_49;
} else {
 lean_dec_ref(x_49);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_50, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_50, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_71 = x_50;
} else {
 lean_dec_ref(x_50);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
x_18 = x_74;
x_19 = x_51;
goto block_36;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_47, 1);
lean_inc(x_75);
lean_dec(x_47);
x_76 = !lean_is_exclusive(x_48);
if (x_76 == 0)
{
x_18 = x_48;
x_19 = x_75;
goto block_36;
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
x_18 = x_79;
x_19 = x_75;
goto block_36;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_47);
if (x_80 == 0)
{
return x_47;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_47, 0);
x_82 = lean_ctor_get(x_47, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_47);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
block_36:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
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
x_5 = x_25;
x_7 = x_23;
x_8 = x_22;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_19);
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_37; lean_object* x_38; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
lean_dec(x_15);
x_38 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_5, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_box(0);
x_40 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__2(x_37, x_39, x_5, x_6, x_7, x_8, x_9);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_18 = x_41;
x_19 = x_42;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_45, x_5);
lean_dec(x_45);
lean_inc(x_1);
lean_inc(x_6);
x_47 = lean_apply_6(x_1, x_43, x_46, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
x_18 = x_48;
x_19 = x_51;
goto block_36;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_49, 0, x_59);
x_18 = x_48;
x_19 = x_51;
goto block_36;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
lean_dec(x_49);
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
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_48, 0, x_65);
x_18 = x_48;
x_19 = x_51;
goto block_36;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_48, 1);
lean_inc(x_66);
lean_dec(x_48);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_68 = x_49;
} else {
 lean_dec_ref(x_49);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_50, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_50, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_71 = x_50;
} else {
 lean_dec_ref(x_50);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
x_18 = x_74;
x_19 = x_51;
goto block_36;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_47, 1);
lean_inc(x_75);
lean_dec(x_47);
x_76 = !lean_is_exclusive(x_48);
if (x_76 == 0)
{
x_18 = x_48;
x_19 = x_75;
goto block_36;
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
x_18 = x_79;
x_19 = x_75;
goto block_36;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_47);
if (x_80 == 0)
{
return x_47;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_47, 0);
x_82 = lean_ctor_get(x_47, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_47);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
block_36:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
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
x_5 = x_25;
x_7 = x_23;
x_8 = x_22;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_19);
return x_35;
}
}
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dependency '", 12);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' of '", 6);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' not in manifest; this suggests that the manifest is corrupt; use `lake update` to generate a new, complete file (warning: this will update ALL workspace dependencies)", 168);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' not in manifest; use `lake update ", 36);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` to add it", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_69; lean_object* x_70; lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
x_94 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_2, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_95 = lean_ctor_get(x_3, 2);
lean_inc(x_95);
lean_dec(x_3);
x_96 = lean_ctor_get(x_95, 2);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_ctor_get(x_10, 0);
lean_inc(x_97);
lean_dec(x_10);
x_98 = lean_ctor_get(x_97, 2);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_ctor_get(x_98, 2);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_name_eq(x_96, x_99);
lean_dec(x_99);
if (x_100 == 0)
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_101 = 1;
x_102 = l_Lean_Name_toString(x_93, x_101);
x_103 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__1;
x_104 = lean_string_append(x_103, x_102);
lean_dec(x_102);
x_105 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__2;
x_106 = lean_string_append(x_104, x_105);
x_107 = l_Lean_Name_toString(x_96, x_101);
x_108 = lean_string_append(x_106, x_107);
lean_dec(x_107);
x_109 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__3;
x_110 = lean_string_append(x_108, x_109);
x_111 = 3;
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = lean_array_get_size(x_11);
x_114 = lean_array_push(x_11, x_112);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_69 = x_115;
x_70 = x_12;
goto block_92;
}
else
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_96);
x_116 = 1;
x_117 = l_Lean_Name_toString(x_93, x_116);
x_118 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__1;
x_119 = lean_string_append(x_118, x_117);
x_120 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__4;
x_121 = lean_string_append(x_119, x_120);
x_122 = lean_string_append(x_121, x_117);
lean_dec(x_117);
x_123 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__5;
x_124 = lean_string_append(x_122, x_123);
x_125 = 3;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_array_get_size(x_11);
x_128 = lean_array_push(x_11, x_126);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_69 = x_129;
x_70 = x_12;
goto block_92;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_93);
lean_dec(x_3);
x_130 = lean_ctor_get(x_94, 0);
lean_inc(x_130);
lean_dec(x_94);
x_131 = lean_ctor_get(x_10, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_10, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
x_134 = l_Lake_PackageEntry_materialize(x_130, x_131, x_133, x_4, x_11, x_12);
lean_dec(x_131);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_ctor_get(x_1, 2);
lean_inc(x_139);
lean_dec(x_1);
x_140 = l_Lake_loadDepPackage(x_137, x_139, x_5, x_6, x_10, x_138, x_136);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_69 = x_141;
x_70 = x_142;
goto block_92;
}
else
{
uint8_t x_143; 
lean_dec(x_8);
x_143 = !lean_is_exclusive(x_140);
if (x_143 == 0)
{
return x_140;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_140, 0);
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_140);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; uint8_t x_148; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_147 = lean_ctor_get(x_134, 1);
lean_inc(x_147);
lean_dec(x_134);
x_148 = !lean_is_exclusive(x_135);
if (x_148 == 0)
{
x_69 = x_135;
x_70 = x_147;
goto block_92;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_135, 0);
x_150 = lean_ctor_get(x_135, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_135);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_69 = x_151;
x_70 = x_147;
goto block_92;
}
}
}
block_68:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_23, x_25, x_22);
x_27 = lean_box(0);
lean_ctor_set(x_16, 1, x_26);
lean_ctor_set(x_16, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_14);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_ctor_get(x_29, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_30, x_32, x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_15, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_14);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
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
x_41 = lean_ctor_get(x_38, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_39, x_42, x_38);
x_44 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_13, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_13);
lean_ctor_set(x_47, 1, x_14);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_dec(x_13);
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
x_51 = lean_ctor_get(x_16, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_53 = x_16;
} else {
 lean_dec_ref(x_16);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_51, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 2);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_52, x_55, x_51);
x_57 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_53;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
if (lean_is_scalar(x_50)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_50;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_49);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_48);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_14);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_13);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_13);
lean_ctor_set(x_63, 1, x_14);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_13, 0);
x_65 = lean_ctor_get(x_13, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_13);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_14);
return x_67;
}
}
}
block_92:
{
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 1);
lean_ctor_set(x_72, 1, x_8);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_69, 0, x_75);
x_13 = x_69;
x_14 = x_70;
goto block_68;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_8);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_69, 0, x_79);
x_13 = x_69;
x_14 = x_70;
goto block_68;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_ctor_get(x_69, 0);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_69);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_84 = x_80;
} else {
 lean_dec_ref(x_80);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_8);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
x_13 = x_87;
x_14 = x_70;
goto block_68;
}
}
else
{
uint8_t x_88; 
lean_dec(x_8);
x_88 = !lean_is_exclusive(x_69);
if (x_88 == 0)
{
x_13 = x_69;
x_14 = x_70;
goto block_68;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_69, 0);
x_90 = lean_ctor_get(x_69, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_69);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_13 = x_91;
x_14 = x_70;
goto block_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_name_eq(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = 1;
x_20 = l_Lean_Name_toString(x_14, x_19);
x_21 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_get_size(x_11);
x_28 = lean_array_push(x_11, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_12);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_7, x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_9);
x_16 = lean_array_uget(x_6, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = l_Lean_NameMap_contains___rarg(x_10, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_5);
x_20 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__3(x_16, x_4, x_5, x_3, x_1, x_2, x_19, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = 1;
x_30 = lean_usize_add(x_7, x_29);
x_7 = x_30;
x_9 = x_27;
x_10 = x_28;
x_12 = x_26;
x_13 = x_25;
x_14 = x_24;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_20, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_20;
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
return x_20;
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
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
lean_dec(x_16);
x_48 = 1;
x_49 = lean_usize_add(x_7, x_48);
x_50 = lean_box(0);
x_7 = x_49;
x_9 = x_50;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_9);
lean_ctor_set(x_52, 1, x_10);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_12);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_13);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_14);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_37; lean_object* x_38; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
lean_dec(x_15);
x_38 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_5, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_box(0);
x_40 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__2(x_37, x_39, x_5, x_6, x_7, x_8, x_9);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_18 = x_41;
x_19 = x_42;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_RBNode_erase___at_Lake_Workspace_resolveDeps___spec__3(x_45, x_5);
lean_dec(x_45);
lean_inc(x_1);
lean_inc(x_6);
x_47 = lean_apply_6(x_1, x_43, x_46, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
x_18 = x_48;
x_19 = x_51;
goto block_36;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_49, 0, x_59);
x_18 = x_48;
x_19 = x_51;
goto block_36;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
lean_dec(x_49);
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
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_48, 0, x_65);
x_18 = x_48;
x_19 = x_51;
goto block_36;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_48, 1);
lean_inc(x_66);
lean_dec(x_48);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_68 = x_49;
} else {
 lean_dec_ref(x_49);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_50, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_50, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_71 = x_50;
} else {
 lean_dec_ref(x_50);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
x_18 = x_74;
x_19 = x_51;
goto block_36;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_47, 1);
lean_inc(x_75);
lean_dec(x_47);
x_76 = !lean_is_exclusive(x_48);
if (x_76 == 0)
{
x_18 = x_48;
x_19 = x_75;
goto block_36;
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
x_18 = x_79;
x_19 = x_75;
goto block_36;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_47);
if (x_80 == 0)
{
return x_47;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_47, 0);
x_82 = lean_ctor_get(x_47, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_47);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
block_36:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
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
x_5 = x_25;
x_7 = x_23;
x_8 = x_22;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_19);
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_materializeDeps___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 8);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 10);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 11);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 12);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 13);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 14);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 15);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 16);
lean_inc(x_27);
x_28 = lean_ctor_get(x_5, 17);
lean_inc(x_28);
x_29 = lean_array_get_size(x_18);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_33 = lean_ctor_get(x_5, 17);
lean_dec(x_33);
x_34 = lean_ctor_get(x_5, 16);
lean_dec(x_34);
x_35 = lean_ctor_get(x_5, 15);
lean_dec(x_35);
x_36 = lean_ctor_get(x_5, 14);
lean_dec(x_36);
x_37 = lean_ctor_get(x_5, 13);
lean_dec(x_37);
x_38 = lean_ctor_get(x_5, 12);
lean_dec(x_38);
x_39 = lean_ctor_get(x_5, 11);
lean_dec(x_39);
x_40 = lean_ctor_get(x_5, 10);
lean_dec(x_40);
x_41 = lean_ctor_get(x_5, 9);
lean_dec(x_41);
x_42 = lean_ctor_get(x_5, 8);
lean_dec(x_42);
x_43 = lean_ctor_get(x_5, 7);
lean_dec(x_43);
x_44 = lean_ctor_get(x_5, 6);
lean_dec(x_44);
x_45 = lean_ctor_get(x_5, 5);
lean_dec(x_45);
x_46 = lean_ctor_get(x_5, 4);
lean_dec(x_46);
x_47 = lean_ctor_get(x_5, 3);
lean_dec(x_47);
x_48 = lean_ctor_get(x_5, 2);
lean_dec(x_48);
x_49 = lean_ctor_get(x_5, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_5, 0);
lean_dec(x_50);
x_51 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_52 = 0;
lean_inc(x_18);
x_53 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2(x_6, x_51, x_52, x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_53, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_55);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_55, 1);
x_63 = lean_ctor_get(x_55, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_56);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_56, 0);
lean_ctor_set(x_5, 6, x_65);
lean_inc(x_5);
x_66 = l_Lake_Workspace_addPackage(x_5, x_62);
lean_ctor_set(x_56, 0, x_5);
lean_ctor_set(x_55, 1, x_66);
return x_53;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_56, 0);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_56);
lean_ctor_set(x_5, 6, x_67);
lean_inc(x_5);
x_69 = l_Lake_Workspace_addPackage(x_5, x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_5);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_55, 1, x_69);
lean_ctor_set(x_55, 0, x_70);
return x_53;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_55, 1);
lean_inc(x_71);
lean_dec(x_55);
x_72 = lean_ctor_get(x_56, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_56, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_74 = x_56;
} else {
 lean_dec_ref(x_56);
 x_74 = lean_box(0);
}
lean_ctor_set(x_5, 6, x_72);
lean_inc(x_5);
x_75 = l_Lake_Workspace_addPackage(x_5, x_71);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_5);
lean_ctor_set(x_76, 1, x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_54, 0, x_77);
return x_53;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_54, 1);
lean_inc(x_78);
lean_dec(x_54);
x_79 = lean_ctor_get(x_55, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_80 = x_55;
} else {
 lean_dec_ref(x_55);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_56, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_56, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_83 = x_56;
} else {
 lean_dec_ref(x_56);
 x_83 = lean_box(0);
}
lean_ctor_set(x_5, 6, x_81);
lean_inc(x_5);
x_84 = l_Lake_Workspace_addPackage(x_5, x_79);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_5);
lean_ctor_set(x_85, 1, x_82);
if (lean_is_scalar(x_80)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_80;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_53, 0, x_87);
return x_53;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_88 = lean_ctor_get(x_53, 1);
lean_inc(x_88);
lean_dec(x_53);
x_89 = lean_ctor_get(x_54, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_90 = x_54;
} else {
 lean_dec_ref(x_54);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_55, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_92 = x_55;
} else {
 lean_dec_ref(x_55);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_56, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_56, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_95 = x_56;
} else {
 lean_dec_ref(x_56);
 x_95 = lean_box(0);
}
lean_ctor_set(x_5, 6, x_93);
lean_inc(x_5);
x_96 = l_Lake_Workspace_addPackage(x_5, x_91);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_5);
lean_ctor_set(x_97, 1, x_94);
if (lean_is_scalar(x_92)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_92;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
if (lean_is_scalar(x_90)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_90;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_89);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_88);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_free_object(x_5);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_101 = !lean_is_exclusive(x_53);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_53, 0);
lean_dec(x_102);
x_103 = !lean_is_exclusive(x_54);
if (x_103 == 0)
{
return x_53;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_54, 0);
x_105 = lean_ctor_get(x_54, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_54);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_53, 0, x_106);
return x_53;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_53, 1);
lean_inc(x_107);
lean_dec(x_53);
x_108 = lean_ctor_get(x_54, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_54, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_110 = x_54;
} else {
 lean_dec_ref(x_54);
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
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_5);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_113 = !lean_is_exclusive(x_53);
if (x_113 == 0)
{
return x_53;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_53, 0);
x_115 = lean_ctor_get(x_53, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_53);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; 
lean_dec(x_5);
x_117 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_118 = 0;
lean_inc(x_18);
x_119 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2(x_6, x_117, x_118, x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_126 = x_120;
} else {
 lean_dec_ref(x_120);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_121, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_128 = x_121;
} else {
 lean_dec_ref(x_121);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_122, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_122, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_131 = x_122;
} else {
 lean_dec_ref(x_122);
 x_131 = lean_box(0);
}
x_132 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_132, 0, x_12);
lean_ctor_set(x_132, 1, x_13);
lean_ctor_set(x_132, 2, x_14);
lean_ctor_set(x_132, 3, x_15);
lean_ctor_set(x_132, 4, x_16);
lean_ctor_set(x_132, 5, x_17);
lean_ctor_set(x_132, 6, x_129);
lean_ctor_set(x_132, 7, x_18);
lean_ctor_set(x_132, 8, x_19);
lean_ctor_set(x_132, 9, x_20);
lean_ctor_set(x_132, 10, x_21);
lean_ctor_set(x_132, 11, x_22);
lean_ctor_set(x_132, 12, x_23);
lean_ctor_set(x_132, 13, x_24);
lean_ctor_set(x_132, 14, x_25);
lean_ctor_set(x_132, 15, x_26);
lean_ctor_set(x_132, 16, x_27);
lean_ctor_set(x_132, 17, x_28);
lean_inc(x_132);
x_133 = l_Lake_Workspace_addPackage(x_132, x_127);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_130);
if (lean_is_scalar(x_128)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_128;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
if (lean_is_scalar(x_126)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_126;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_125);
if (lean_is_scalar(x_124)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_124;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_123);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_138 = lean_ctor_get(x_119, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_139 = x_119;
} else {
 lean_dec_ref(x_119);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_120, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_120, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_142 = x_120;
} else {
 lean_dec_ref(x_120);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
if (lean_is_scalar(x_139)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_139;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_138);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_145 = lean_ctor_get(x_119, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_119, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_147 = x_119;
} else {
 lean_dec_ref(x_119);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
else
{
uint8_t x_149; 
x_149 = lean_nat_dec_le(x_29, x_29);
if (x_149 == 0)
{
uint8_t x_150; 
lean_dec(x_3);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_5);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; lean_object* x_171; 
x_151 = lean_ctor_get(x_5, 17);
lean_dec(x_151);
x_152 = lean_ctor_get(x_5, 16);
lean_dec(x_152);
x_153 = lean_ctor_get(x_5, 15);
lean_dec(x_153);
x_154 = lean_ctor_get(x_5, 14);
lean_dec(x_154);
x_155 = lean_ctor_get(x_5, 13);
lean_dec(x_155);
x_156 = lean_ctor_get(x_5, 12);
lean_dec(x_156);
x_157 = lean_ctor_get(x_5, 11);
lean_dec(x_157);
x_158 = lean_ctor_get(x_5, 10);
lean_dec(x_158);
x_159 = lean_ctor_get(x_5, 9);
lean_dec(x_159);
x_160 = lean_ctor_get(x_5, 8);
lean_dec(x_160);
x_161 = lean_ctor_get(x_5, 7);
lean_dec(x_161);
x_162 = lean_ctor_get(x_5, 6);
lean_dec(x_162);
x_163 = lean_ctor_get(x_5, 5);
lean_dec(x_163);
x_164 = lean_ctor_get(x_5, 4);
lean_dec(x_164);
x_165 = lean_ctor_get(x_5, 3);
lean_dec(x_165);
x_166 = lean_ctor_get(x_5, 2);
lean_dec(x_166);
x_167 = lean_ctor_get(x_5, 1);
lean_dec(x_167);
x_168 = lean_ctor_get(x_5, 0);
lean_dec(x_168);
x_169 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_170 = 0;
lean_inc(x_18);
x_171 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3(x_6, x_169, x_170, x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = !lean_is_exclusive(x_171);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_171, 0);
lean_dec(x_176);
x_177 = !lean_is_exclusive(x_172);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_172, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_173);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_173, 1);
x_181 = lean_ctor_get(x_173, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_174);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_174, 0);
lean_ctor_set(x_5, 6, x_183);
lean_inc(x_5);
x_184 = l_Lake_Workspace_addPackage(x_5, x_180);
lean_ctor_set(x_174, 0, x_5);
lean_ctor_set(x_173, 1, x_184);
return x_171;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_174, 0);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_174);
lean_ctor_set(x_5, 6, x_185);
lean_inc(x_5);
x_187 = l_Lake_Workspace_addPackage(x_5, x_180);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_5);
lean_ctor_set(x_188, 1, x_186);
lean_ctor_set(x_173, 1, x_187);
lean_ctor_set(x_173, 0, x_188);
return x_171;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_189 = lean_ctor_get(x_173, 1);
lean_inc(x_189);
lean_dec(x_173);
x_190 = lean_ctor_get(x_174, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_174, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_192 = x_174;
} else {
 lean_dec_ref(x_174);
 x_192 = lean_box(0);
}
lean_ctor_set(x_5, 6, x_190);
lean_inc(x_5);
x_193 = l_Lake_Workspace_addPackage(x_5, x_189);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_5);
lean_ctor_set(x_194, 1, x_191);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
lean_ctor_set(x_172, 0, x_195);
return x_171;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_196 = lean_ctor_get(x_172, 1);
lean_inc(x_196);
lean_dec(x_172);
x_197 = lean_ctor_get(x_173, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_198 = x_173;
} else {
 lean_dec_ref(x_173);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_174, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_174, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_201 = x_174;
} else {
 lean_dec_ref(x_174);
 x_201 = lean_box(0);
}
lean_ctor_set(x_5, 6, x_199);
lean_inc(x_5);
x_202 = l_Lake_Workspace_addPackage(x_5, x_197);
if (lean_is_scalar(x_201)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_201;
}
lean_ctor_set(x_203, 0, x_5);
lean_ctor_set(x_203, 1, x_200);
if (lean_is_scalar(x_198)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_198;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_196);
lean_ctor_set(x_171, 0, x_205);
return x_171;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_206 = lean_ctor_get(x_171, 1);
lean_inc(x_206);
lean_dec(x_171);
x_207 = lean_ctor_get(x_172, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_208 = x_172;
} else {
 lean_dec_ref(x_172);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_173, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_210 = x_173;
} else {
 lean_dec_ref(x_173);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_174, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_174, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_213 = x_174;
} else {
 lean_dec_ref(x_174);
 x_213 = lean_box(0);
}
lean_ctor_set(x_5, 6, x_211);
lean_inc(x_5);
x_214 = l_Lake_Workspace_addPackage(x_5, x_209);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_5);
lean_ctor_set(x_215, 1, x_212);
if (lean_is_scalar(x_210)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_210;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
if (lean_is_scalar(x_208)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_208;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_207);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_206);
return x_218;
}
}
else
{
uint8_t x_219; 
lean_free_object(x_5);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_219 = !lean_is_exclusive(x_171);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_171, 0);
lean_dec(x_220);
x_221 = !lean_is_exclusive(x_172);
if (x_221 == 0)
{
return x_171;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_172, 0);
x_223 = lean_ctor_get(x_172, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_172);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_171, 0, x_224);
return x_171;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_225 = lean_ctor_get(x_171, 1);
lean_inc(x_225);
lean_dec(x_171);
x_226 = lean_ctor_get(x_172, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_172, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_228 = x_172;
} else {
 lean_dec_ref(x_172);
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
lean_free_object(x_5);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_231 = !lean_is_exclusive(x_171);
if (x_231 == 0)
{
return x_171;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_171, 0);
x_233 = lean_ctor_get(x_171, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_171);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
size_t x_235; size_t x_236; lean_object* x_237; 
lean_dec(x_5);
x_235 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_236 = 0;
lean_inc(x_18);
x_237 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3(x_6, x_235, x_236, x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_239, 0);
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
x_243 = lean_ctor_get(x_238, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_244 = x_238;
} else {
 lean_dec_ref(x_238);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_239, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_246 = x_239;
} else {
 lean_dec_ref(x_239);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_240, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_240, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_249 = x_240;
} else {
 lean_dec_ref(x_240);
 x_249 = lean_box(0);
}
x_250 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_250, 0, x_12);
lean_ctor_set(x_250, 1, x_13);
lean_ctor_set(x_250, 2, x_14);
lean_ctor_set(x_250, 3, x_15);
lean_ctor_set(x_250, 4, x_16);
lean_ctor_set(x_250, 5, x_17);
lean_ctor_set(x_250, 6, x_247);
lean_ctor_set(x_250, 7, x_18);
lean_ctor_set(x_250, 8, x_19);
lean_ctor_set(x_250, 9, x_20);
lean_ctor_set(x_250, 10, x_21);
lean_ctor_set(x_250, 11, x_22);
lean_ctor_set(x_250, 12, x_23);
lean_ctor_set(x_250, 13, x_24);
lean_ctor_set(x_250, 14, x_25);
lean_ctor_set(x_250, 15, x_26);
lean_ctor_set(x_250, 16, x_27);
lean_ctor_set(x_250, 17, x_28);
lean_inc(x_250);
x_251 = l_Lake_Workspace_addPackage(x_250, x_245);
if (lean_is_scalar(x_249)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_249;
}
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_248);
if (lean_is_scalar(x_246)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_246;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_251);
if (lean_is_scalar(x_244)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_244;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_243);
if (lean_is_scalar(x_242)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_242;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_241);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_256 = lean_ctor_get(x_237, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_257 = x_237;
} else {
 lean_dec_ref(x_237);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_238, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_238, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_260 = x_238;
} else {
 lean_dec_ref(x_238);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
if (lean_is_scalar(x_257)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_257;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_256);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_263 = lean_ctor_get(x_237, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_237, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_265 = x_237;
} else {
 lean_dec_ref(x_237);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
else
{
size_t x_267; size_t x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_267 = 0;
x_268 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_269 = lean_box(0);
lean_inc(x_5);
x_270 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(x_1, x_2, x_3, x_4, x_5, x_18, x_267, x_268, x_269, x_7, x_8, x_9, x_10, x_11);
x_271 = !lean_is_exclusive(x_5);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_272 = lean_ctor_get(x_5, 17);
lean_dec(x_272);
x_273 = lean_ctor_get(x_5, 16);
lean_dec(x_273);
x_274 = lean_ctor_get(x_5, 15);
lean_dec(x_274);
x_275 = lean_ctor_get(x_5, 14);
lean_dec(x_275);
x_276 = lean_ctor_get(x_5, 13);
lean_dec(x_276);
x_277 = lean_ctor_get(x_5, 12);
lean_dec(x_277);
x_278 = lean_ctor_get(x_5, 11);
lean_dec(x_278);
x_279 = lean_ctor_get(x_5, 10);
lean_dec(x_279);
x_280 = lean_ctor_get(x_5, 9);
lean_dec(x_280);
x_281 = lean_ctor_get(x_5, 8);
lean_dec(x_281);
x_282 = lean_ctor_get(x_5, 7);
lean_dec(x_282);
x_283 = lean_ctor_get(x_5, 6);
lean_dec(x_283);
x_284 = lean_ctor_get(x_5, 5);
lean_dec(x_284);
x_285 = lean_ctor_get(x_5, 4);
lean_dec(x_285);
x_286 = lean_ctor_get(x_5, 3);
lean_dec(x_286);
x_287 = lean_ctor_get(x_5, 2);
lean_dec(x_287);
x_288 = lean_ctor_get(x_5, 1);
lean_dec(x_288);
x_289 = lean_ctor_get(x_5, 0);
lean_dec(x_289);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_270, 0);
lean_inc(x_290);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_270, 1);
lean_inc(x_293);
lean_dec(x_270);
x_294 = lean_ctor_get(x_290, 1);
lean_inc(x_294);
lean_dec(x_290);
x_295 = lean_ctor_get(x_291, 1);
lean_inc(x_295);
lean_dec(x_291);
x_296 = lean_ctor_get(x_292, 1);
lean_inc(x_296);
lean_dec(x_292);
lean_inc(x_18);
x_297 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__5(x_6, x_268, x_267, x_18, x_296, x_8, x_295, x_294, x_293);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = !lean_is_exclusive(x_297);
if (x_301 == 0)
{
lean_object* x_302; uint8_t x_303; 
x_302 = lean_ctor_get(x_297, 0);
lean_dec(x_302);
x_303 = !lean_is_exclusive(x_298);
if (x_303 == 0)
{
lean_object* x_304; uint8_t x_305; 
x_304 = lean_ctor_get(x_298, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_299);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_306 = lean_ctor_get(x_299, 1);
x_307 = lean_ctor_get(x_299, 0);
lean_dec(x_307);
x_308 = !lean_is_exclusive(x_300);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_300, 0);
lean_ctor_set(x_5, 6, x_309);
lean_inc(x_5);
x_310 = l_Lake_Workspace_addPackage(x_5, x_306);
lean_ctor_set(x_300, 0, x_5);
lean_ctor_set(x_299, 1, x_310);
return x_297;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_311 = lean_ctor_get(x_300, 0);
x_312 = lean_ctor_get(x_300, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_300);
lean_ctor_set(x_5, 6, x_311);
lean_inc(x_5);
x_313 = l_Lake_Workspace_addPackage(x_5, x_306);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_5);
lean_ctor_set(x_314, 1, x_312);
lean_ctor_set(x_299, 1, x_313);
lean_ctor_set(x_299, 0, x_314);
return x_297;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_315 = lean_ctor_get(x_299, 1);
lean_inc(x_315);
lean_dec(x_299);
x_316 = lean_ctor_get(x_300, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_300, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_318 = x_300;
} else {
 lean_dec_ref(x_300);
 x_318 = lean_box(0);
}
lean_ctor_set(x_5, 6, x_316);
lean_inc(x_5);
x_319 = l_Lake_Workspace_addPackage(x_5, x_315);
if (lean_is_scalar(x_318)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_318;
}
lean_ctor_set(x_320, 0, x_5);
lean_ctor_set(x_320, 1, x_317);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_319);
lean_ctor_set(x_298, 0, x_321);
return x_297;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_322 = lean_ctor_get(x_298, 1);
lean_inc(x_322);
lean_dec(x_298);
x_323 = lean_ctor_get(x_299, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_324 = x_299;
} else {
 lean_dec_ref(x_299);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get(x_300, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_300, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_327 = x_300;
} else {
 lean_dec_ref(x_300);
 x_327 = lean_box(0);
}
lean_ctor_set(x_5, 6, x_325);
lean_inc(x_5);
x_328 = l_Lake_Workspace_addPackage(x_5, x_323);
if (lean_is_scalar(x_327)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_327;
}
lean_ctor_set(x_329, 0, x_5);
lean_ctor_set(x_329, 1, x_326);
if (lean_is_scalar(x_324)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_324;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_328);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_322);
lean_ctor_set(x_297, 0, x_331);
return x_297;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_332 = lean_ctor_get(x_297, 1);
lean_inc(x_332);
lean_dec(x_297);
x_333 = lean_ctor_get(x_298, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_334 = x_298;
} else {
 lean_dec_ref(x_298);
 x_334 = lean_box(0);
}
x_335 = lean_ctor_get(x_299, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_336 = x_299;
} else {
 lean_dec_ref(x_299);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_300, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_300, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_339 = x_300;
} else {
 lean_dec_ref(x_300);
 x_339 = lean_box(0);
}
lean_ctor_set(x_5, 6, x_337);
lean_inc(x_5);
x_340 = l_Lake_Workspace_addPackage(x_5, x_335);
if (lean_is_scalar(x_339)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_339;
}
lean_ctor_set(x_341, 0, x_5);
lean_ctor_set(x_341, 1, x_338);
if (lean_is_scalar(x_336)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_336;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
if (lean_is_scalar(x_334)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_334;
}
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_333);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_332);
return x_344;
}
}
else
{
uint8_t x_345; 
lean_free_object(x_5);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_345 = !lean_is_exclusive(x_297);
if (x_345 == 0)
{
lean_object* x_346; uint8_t x_347; 
x_346 = lean_ctor_get(x_297, 0);
lean_dec(x_346);
x_347 = !lean_is_exclusive(x_298);
if (x_347 == 0)
{
return x_297;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_298, 0);
x_349 = lean_ctor_get(x_298, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_298);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
lean_ctor_set(x_297, 0, x_350);
return x_297;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_297, 1);
lean_inc(x_351);
lean_dec(x_297);
x_352 = lean_ctor_get(x_298, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_298, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_354 = x_298;
} else {
 lean_dec_ref(x_298);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_351);
return x_356;
}
}
}
else
{
uint8_t x_357; 
lean_free_object(x_5);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_357 = !lean_is_exclusive(x_297);
if (x_357 == 0)
{
return x_297;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_297, 0);
x_359 = lean_ctor_get(x_297, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_297);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
}
}
else
{
uint8_t x_361; 
lean_free_object(x_5);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
x_361 = !lean_is_exclusive(x_270);
if (x_361 == 0)
{
lean_object* x_362; uint8_t x_363; 
x_362 = lean_ctor_get(x_270, 0);
lean_dec(x_362);
x_363 = !lean_is_exclusive(x_290);
if (x_363 == 0)
{
return x_270;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_290, 0);
x_365 = lean_ctor_get(x_290, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_290);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
lean_ctor_set(x_270, 0, x_366);
return x_270;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_367 = lean_ctor_get(x_270, 1);
lean_inc(x_367);
lean_dec(x_270);
x_368 = lean_ctor_get(x_290, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_290, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_370 = x_290;
} else {
 lean_dec_ref(x_290);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_369);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_367);
return x_372;
}
}
}
else
{
uint8_t x_373; 
lean_free_object(x_5);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
x_373 = !lean_is_exclusive(x_270);
if (x_373 == 0)
{
return x_270;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_270, 0);
x_375 = lean_ctor_get(x_270, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_270);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_270, 0);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_270, 1);
lean_inc(x_380);
lean_dec(x_270);
x_381 = lean_ctor_get(x_377, 1);
lean_inc(x_381);
lean_dec(x_377);
x_382 = lean_ctor_get(x_378, 1);
lean_inc(x_382);
lean_dec(x_378);
x_383 = lean_ctor_get(x_379, 1);
lean_inc(x_383);
lean_dec(x_379);
lean_inc(x_18);
x_384 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__5(x_6, x_268, x_267, x_18, x_383, x_8, x_382, x_381, x_380);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_384, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_389 = x_384;
} else {
 lean_dec_ref(x_384);
 x_389 = lean_box(0);
}
x_390 = lean_ctor_get(x_385, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_391 = x_385;
} else {
 lean_dec_ref(x_385);
 x_391 = lean_box(0);
}
x_392 = lean_ctor_get(x_386, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_393 = x_386;
} else {
 lean_dec_ref(x_386);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_387, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_387, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_396 = x_387;
} else {
 lean_dec_ref(x_387);
 x_396 = lean_box(0);
}
x_397 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_397, 0, x_12);
lean_ctor_set(x_397, 1, x_13);
lean_ctor_set(x_397, 2, x_14);
lean_ctor_set(x_397, 3, x_15);
lean_ctor_set(x_397, 4, x_16);
lean_ctor_set(x_397, 5, x_17);
lean_ctor_set(x_397, 6, x_394);
lean_ctor_set(x_397, 7, x_18);
lean_ctor_set(x_397, 8, x_19);
lean_ctor_set(x_397, 9, x_20);
lean_ctor_set(x_397, 10, x_21);
lean_ctor_set(x_397, 11, x_22);
lean_ctor_set(x_397, 12, x_23);
lean_ctor_set(x_397, 13, x_24);
lean_ctor_set(x_397, 14, x_25);
lean_ctor_set(x_397, 15, x_26);
lean_ctor_set(x_397, 16, x_27);
lean_ctor_set(x_397, 17, x_28);
lean_inc(x_397);
x_398 = l_Lake_Workspace_addPackage(x_397, x_392);
if (lean_is_scalar(x_396)) {
 x_399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_399 = x_396;
}
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_395);
if (lean_is_scalar(x_393)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_393;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
if (lean_is_scalar(x_391)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_391;
}
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_390);
if (lean_is_scalar(x_389)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_389;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_388);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_403 = lean_ctor_get(x_384, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_404 = x_384;
} else {
 lean_dec_ref(x_384);
 x_404 = lean_box(0);
}
x_405 = lean_ctor_get(x_385, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_385, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_407 = x_385;
} else {
 lean_dec_ref(x_385);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_406);
if (lean_is_scalar(x_404)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_404;
}
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_403);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_410 = lean_ctor_get(x_384, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_384, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_412 = x_384;
} else {
 lean_dec_ref(x_384);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_411);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
x_414 = lean_ctor_get(x_270, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_415 = x_270;
} else {
 lean_dec_ref(x_270);
 x_415 = lean_box(0);
}
x_416 = lean_ctor_get(x_377, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_377, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_418 = x_377;
} else {
 lean_dec_ref(x_377);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_416);
lean_ctor_set(x_419, 1, x_417);
if (lean_is_scalar(x_415)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_415;
}
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_414);
return x_420;
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
x_421 = lean_ctor_get(x_270, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_270, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_423 = x_270;
} else {
 lean_dec_ref(x_270);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_421);
lean_ctor_set(x_424, 1, x_422);
return x_424;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameResolveTOfMonadOfMonadError___spec__2(x_1, x_6);
x_8 = l_Lake_depCycleError___rarg___closed__2;
x_9 = l_String_intercalate(x_8, x_7);
x_10 = l_Lake_depCycleError___rarg___closed__3;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = 3;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_get_size(x_4);
x_17 = lean_array_push(x_4, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(x_1, x_2, x_3, x_4, x_6, x_7, x_5, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_5, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_12, x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_7);
x_15 = lean_box(x_2);
lean_inc(x_14);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___lambda__1___boxed), 11, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_14);
x_17 = l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_materializeDeps___spec__1(x_1, x_2, x_3, x_4, x_5, x_16, x_6, x_14, x_8, x_9, x_10);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___closed__1;
lean_inc(x_7);
x_20 = l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__7(x_12, x_7, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_18);
x_24 = l_List_appendTR___rarg(x_22, x_23);
x_25 = l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8___rarg(x_24, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_36 = x_32;
} else {
 lean_dec_ref(x_32);
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
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_materializeDeps___spec__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_4, x_7, x_6);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__11(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_1, 2);
lean_inc(x_56);
x_57 = lean_box(0);
x_58 = lean_ctor_get(x_1, 3);
lean_inc(x_58);
lean_dec(x_1);
x_59 = lean_array_get_size(x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_lt(x_60, x_59);
x_62 = lean_ctor_get(x_2, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 7);
lean_inc(x_63);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_62, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
x_64 = x_117;
goto block_115;
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_56, 0);
lean_inc(x_118);
lean_dec(x_56);
x_64 = x_118;
goto block_115;
}
block_55:
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
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
lean_ctor_set(x_11, 0, x_15);
lean_ctor_set(x_8, 0, x_11);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_11, 1);
x_20 = lean_ctor_get(x_11, 2);
x_21 = lean_ctor_get(x_11, 3);
x_22 = lean_ctor_get(x_11, 4);
x_23 = lean_ctor_get(x_11, 5);
x_24 = lean_ctor_get(x_11, 6);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set(x_25, 5, x_23);
lean_ctor_set(x_25, 6, x_24);
lean_ctor_set(x_8, 0, x_25);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_11, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_11, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_11, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 6);
lean_inc(x_32);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 lean_ctor_release(x_11, 6);
 x_33 = x_11;
} else {
 lean_dec_ref(x_11);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 7, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_31);
lean_ctor_set(x_34, 6, x_32);
lean_ctor_set(x_8, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_ctor_get(x_10, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_38 = x_10;
} else {
 lean_dec_ref(x_10);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_11, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_11, 6);
lean_inc(x_44);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 lean_ctor_release(x_11, 6);
 x_45 = x_11;
} else {
 lean_dec_ref(x_11);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 7, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_40);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 4, x_42);
lean_ctor_set(x_46, 5, x_43);
lean_ctor_set(x_46, 6, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_38;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_9);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_8);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_9);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_8, 0);
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_8);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_9);
return x_54;
}
}
}
block_115:
{
lean_object* x_65; 
if (x_61 == 0)
{
lean_dec(x_59);
lean_dec(x_58);
x_65 = x_57;
goto block_110;
}
else
{
uint8_t x_111; 
x_111 = lean_nat_dec_le(x_59, x_59);
if (x_111 == 0)
{
lean_dec(x_59);
lean_dec(x_58);
x_65 = x_57;
goto block_110;
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; 
x_112 = 0;
x_113 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_114 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__10(x_58, x_112, x_113, x_57);
lean_dec(x_58);
x_65 = x_114;
goto block_110;
}
}
block_110:
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lake_validateManifest(x_65, x_63, x_6, x_7);
lean_dec(x_63);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_box(0);
x_71 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(x_3, x_4, x_64, x_65, x_62, x_57, x_70, x_2, x_69, x_68);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_72, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = !lean_is_exclusive(x_74);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_74, 1);
lean_dec(x_80);
lean_ctor_set(x_74, 1, x_78);
lean_ctor_set(x_72, 0, x_74);
x_8 = x_72;
x_9 = x_75;
goto block_55;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_72, 0, x_82);
x_8 = x_72;
x_9 = x_75;
goto block_55;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_72, 1);
lean_inc(x_83);
lean_dec(x_72);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_dec(x_73);
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_86 = x_74;
} else {
 lean_dec_ref(x_74);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_84);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
x_8 = x_88;
x_9 = x_75;
goto block_55;
}
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_71, 1);
lean_inc(x_89);
lean_dec(x_71);
x_90 = !lean_is_exclusive(x_72);
if (x_90 == 0)
{
x_8 = x_72;
x_9 = x_89;
goto block_55;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_72, 0);
x_92 = lean_ctor_get(x_72, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_72);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_8 = x_93;
x_9 = x_89;
goto block_55;
}
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_71);
if (x_94 == 0)
{
return x_71;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_71, 0);
x_96 = lean_ctor_get(x_71, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_71);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_66);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_66, 0);
lean_dec(x_99);
x_100 = !lean_is_exclusive(x_67);
if (x_100 == 0)
{
return x_66;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_67, 0);
x_102 = lean_ctor_get(x_67, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_67);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_66, 0, x_103);
return x_66;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_66, 1);
lean_inc(x_104);
lean_dec(x_66);
x_105 = lean_ctor_get(x_67, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_67, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_107 = x_67;
} else {
 lean_dec_ref(x_67);
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
}
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("manifest out of date: packages directory changed; use `lake update` to rebuild the manifest (warning: this will update ALL workspace dependencies)", 146);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = l_Lake_Workspace_materializeDeps___closed__1;
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
x_15 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__11(x_9, x_14);
lean_dec(x_14);
lean_dec(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lake_Workspace_materializeDeps___closed__2;
x_17 = lean_array_push(x_5, x_16);
x_18 = lean_box(0);
x_19 = l_Lake_Workspace_materializeDeps___lambda__1(x_2, x_1, x_3, x_4, x_18, x_17, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lake_Workspace_materializeDeps___lambda__1(x_2, x_1, x_3, x_4, x_20, x_5, x_6);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lake_Workspace_materializeDeps___lambda__1(x_2, x_1, x_3, x_4, x_22, x_5, x_6);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__3(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_18 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(x_1, x_15, x_3, x_4, x_5, x_6, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lake_Workspace_materializeDeps___spec__5(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_materializeDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lake_Workspace_resolveDeps_go___at_Lake_Workspace_materializeDeps___spec__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__8(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___lambda__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at_Lake_Workspace_materializeDeps___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lake_recFetchAcyclic___at_Lake_Workspace_materializeDeps___spec__6(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lake_Workspace_materializeDeps___lambda__1(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_StoreInsts(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Topological(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Materialize(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Package(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Resolve(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_StoreInsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Topological(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Materialize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_depCycleError___rarg___lambda__1___closed__1 = _init_l_Lake_depCycleError___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lake_depCycleError___rarg___lambda__1___closed__1);
l_Lake_depCycleError___rarg___lambda__1___closed__2 = _init_l_Lake_depCycleError___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lake_depCycleError___rarg___lambda__1___closed__2);
l_Lake_depCycleError___rarg___closed__1 = _init_l_Lake_depCycleError___rarg___closed__1();
lean_mark_persistent(l_Lake_depCycleError___rarg___closed__1);
l_Lake_depCycleError___rarg___closed__2 = _init_l_Lake_depCycleError___rarg___closed__2();
lean_mark_persistent(l_Lake_depCycleError___rarg___closed__2);
l_Lake_depCycleError___rarg___closed__3 = _init_l_Lake_depCycleError___rarg___closed__3();
lean_mark_persistent(l_Lake_depCycleError___rarg___closed__3);
l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___closed__1 = _init_l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___closed__1();
lean_mark_persistent(l_Lake_Workspace_resolveDeps_go___rarg___lambda__6___closed__1);
l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1 = _init_l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1();
lean_mark_persistent(l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__1);
l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2 = _init_l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2();
lean_mark_persistent(l_Lake_Workspace_resolveDeps_go___rarg___lambda__7___closed__2);
l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___closed__1 = _init_l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___closed__1();
lean_mark_persistent(l_Lake_Workspace_resolveDeps_go___rarg___lambda__15___closed__1);
l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___closed__1 = _init_l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lake_recFetch___at_Lake_Workspace_resolveDeps___spec__9___rarg___lambda__2___closed__1);
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
l_Lake_reuseManifest___lambda__1___closed__1 = _init_l_Lake_reuseManifest___lambda__1___closed__1();
lean_mark_persistent(l_Lake_reuseManifest___lambda__1___closed__1);
l_Lake_reuseManifest___lambda__2___closed__1 = _init_l_Lake_reuseManifest___lambda__2___closed__1();
lean_mark_persistent(l_Lake_reuseManifest___lambda__2___closed__1);
l_Lake_reuseManifest___lambda__2___closed__2 = _init_l_Lake_reuseManifest___lambda__2___closed__2();
lean_mark_persistent(l_Lake_reuseManifest___lambda__2___closed__2);
l_Lake_reuseManifest___lambda__2___closed__3 = _init_l_Lake_reuseManifest___lambda__2___closed__3();
lean_mark_persistent(l_Lake_reuseManifest___lambda__2___closed__3);
l_Lake_reuseManifest___lambda__2___closed__4 = _init_l_Lake_reuseManifest___lambda__2___closed__4();
lean_mark_persistent(l_Lake_reuseManifest___lambda__2___closed__4);
l_Lake_reuseManifest___closed__1 = _init_l_Lake_reuseManifest___closed__1();
lean_mark_persistent(l_Lake_reuseManifest___closed__1);
l_Lake_updateDep___lambda__2___closed__1 = _init_l_Lake_updateDep___lambda__2___closed__1();
lean_mark_persistent(l_Lake_updateDep___lambda__2___closed__1);
l_Lake_updateDep___lambda__2___closed__2 = _init_l_Lake_updateDep___lambda__2___closed__2();
lean_mark_persistent(l_Lake_updateDep___lambda__2___closed__2);
l_Lake_updateDep___lambda__3___closed__1 = _init_l_Lake_updateDep___lambda__3___closed__1();
lean_mark_persistent(l_Lake_updateDep___lambda__3___closed__1);
l_Lake_updateDep___lambda__3___closed__2 = _init_l_Lake_updateDep___lambda__3___closed__2();
lean_mark_persistent(l_Lake_updateDep___lambda__3___closed__2);
l_Lake_updateDep___lambda__4___closed__1 = _init_l_Lake_updateDep___lambda__4___closed__1();
lean_mark_persistent(l_Lake_updateDep___lambda__4___closed__1);
l_Lake_updateDep___lambda__4___closed__2 = _init_l_Lake_updateDep___lambda__4___closed__2();
lean_mark_persistent(l_Lake_updateDep___lambda__4___closed__2);
l_Lake_updateDep___closed__1 = _init_l_Lake_updateDep___closed__1();
lean_mark_persistent(l_Lake_updateDep___closed__1);
l_Lake_updateDep___closed__2 = _init_l_Lake_updateDep___closed__2();
lean_mark_persistent(l_Lake_updateDep___closed__2);
l_Lake_updateDep___closed__3 = _init_l_Lake_updateDep___closed__3();
lean_mark_persistent(l_Lake_updateDep___closed__3);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__2___closed__1);
l_Lake_Workspace_updateAndMaterialize___closed__1 = _init_l_Lake_Workspace_updateAndMaterialize___closed__1();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterialize___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__3);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__4);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__5 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__5);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__3);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__4);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__5 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__5);
l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__6 = _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__6();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__6);
l_Lake_validateManifest___closed__1 = _init_l_Lake_validateManifest___closed__1();
lean_mark_persistent(l_Lake_validateManifest___closed__1);
l_Lake_validateManifest___closed__2 = _init_l_Lake_validateManifest___closed__2();
lean_mark_persistent(l_Lake_validateManifest___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__3);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__4);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__5 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___lambda__1___closed__5);
l_Lake_Workspace_materializeDeps___closed__1 = _init_l_Lake_Workspace_materializeDeps___closed__1();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___closed__1);
l_Lake_Workspace_materializeDeps___closed__2 = _init_l_Lake_Workspace_materializeDeps___closed__2();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

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
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2;
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__12;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_recFetch___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__33(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_materializeDeps___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__23(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_toolchainFileName;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__46(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49(lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__50(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadDepPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_runPostUpdateHooks___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__1;
static lean_object* l_Lake_Workspace_updateToolchain___closed__6;
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdMismatchError___boxed(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_decEqOption____x40_Init_Data_Option_Basic___hyg_4____at_Lake_PackageEntry_materialize___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_saveToFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__3;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__20(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__3;
static lean_object* l_Lake_Package_runPostUpdateHooks___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__1;
lean_object* l_Lake_RBNode_dFind___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_UpdateT_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__43(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__7;
static uint8_t l_Lake_Workspace_updateToolchain___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__31(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DepStackT_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__44(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lake_stdMismatchError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__2;
lean_object* l_Array_reverse___rarg(lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_Lake_Workspace_updateToolchain___closed__1;
uint8_t l_List_elem___at_Lean_addAliasEntry___spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_materializeDeps___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__25___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_materializeDeps___spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadDepPackage___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__9___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__6;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__32(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_reuseManifest___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__42(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__21(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__3___boxed(lean_object*, lean_object*);
uint8_t l___private_Lake_Util_Version_0__Lake_decEqToolchainVer____x40_Lake_Util_Version___hyg_1809_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_ToolchainVer_decLe(lean_object*, lean_object*);
lean_object* l_List_partition_loop___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ToolchainVer_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__37___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__41(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__29(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_ToolchainVer_decLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__47(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__6(lean_object*, lean_object*);
static lean_object* l_Lake_depCycleError___rarg___closed__3;
static lean_object* l_Lake_Workspace_materializeDeps___closed__2;
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__9;
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__37___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__48___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Env_noToolchainVars;
LEAN_EXPORT lean_object* l_Lake_ResolveT_run___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__9(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__38(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__5;
LEAN_EXPORT uint32_t l_Lake_restartCode;
static lean_object* l_Lake_stdMismatchError___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_depCycleError___rarg___lambda__1___closed__2;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_lift___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__8;
lean_object* l_StateT_instMonad___rarg(lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1;
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__4;
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__35(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__51(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__45(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__48(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__26(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_writeManifest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__50___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_runPostUpdateHooks___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_UpdateT_run___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DepStackT_run___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24___boxed(lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__8;
static lean_object* l_Lake_Workspace_updateToolchain___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__1;
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10___boxed(lean_object*);
lean_object* l_Lake_instMonadErrorOfMonadLift___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__50___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadDepPackage(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__28(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__12___at_Lake_Workspace_updateAndMaterializeCore___spec__13(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__39(lean_object*, size_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__30(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_writeManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___rarg(lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__11;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_validateManifest___closed__2;
static lean_object* l_Lake_depCycleError___rarg___closed__2;
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__35___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__13;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_materializeDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__2;
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__3;
static lean_object* l_Lake_depCycleError___rarg___closed__1;
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__4;
static lean_object* l_Lake_Workspace_updateToolchain___lambda__1___closed__9;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__4;
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__7___closed__1;
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__2;
static lean_object* l_Lake_validateManifest___closed__1;
static lean_object* l_Lake_depCycleError___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ResolveT_run(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_loadDepPackage___lambda__1(lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__1;
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadDepPackage___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_reuseManifest___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_writeManifest___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__25___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lake_Workspace_writeManifest(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__9(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_stdMismatchError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the 'std' package has been renamed to '", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' and moved to the\n'leanprover-community' organization; downstream packages which wish to\nupdate to the new std should replace\n\n  require std from\n    git \"https://github.com/leanprover/std4\"", 191, 191);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nin their Lake configuration file with\n\n  require ", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" from\n    git \"https://github.com/leanprover-community/", 55, 55);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n", 2, 2);
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
LEAN_EXPORT uint8_t l_Lake_loadDepPackage___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_loadDepPackage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_loadDepPackage___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadDepPackage(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = 0;
x_11 = l_Lake_loadDepPackage___closed__1;
x_12 = l_Lean_Name_toString(x_9, x_10, x_11);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_box(0);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 1;
lean_inc(x_3);
x_22 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_16);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_2);
lean_ctor_set(x_22, 6, x_3);
lean_ctor_set(x_22, 7, x_19);
lean_ctor_set(x_22, 8, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*9, x_4);
lean_ctor_set_uint8(x_22, sizeof(void*)*9 + 1, x_10);
lean_ctor_set_uint8(x_22, sizeof(void*)*9 + 2, x_21);
x_23 = l_Lake_loadPackageCore(x_12, x_22, x_6, x_7);
lean_dec(x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_24, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_25, 1);
lean_dec(x_32);
lean_ctor_set(x_25, 1, x_5);
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
lean_ctor_set(x_24, 0, x_34);
return x_23;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_37 = x_25;
} else {
 lean_dec_ref(x_25);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_23, 0, x_39);
return x_23;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_dec(x_23);
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
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_44 = x_25;
} else {
 lean_dec_ref(x_25);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_5);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_dec(x_23);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_24, 1);
x_51 = lean_ctor_get(x_24, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_25);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_25, 0);
x_54 = lean_ctor_get(x_25, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_26, 0);
lean_inc(x_55);
lean_dec(x_26);
x_56 = l_Lake_Workspace_addFacetsFromEnv(x_55, x_3, x_5);
lean_dec(x_3);
x_57 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_56, x_48);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_ctor_set(x_25, 1, x_59);
lean_ctor_set(x_57, 0, x_24);
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
lean_ctor_set(x_25, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_24);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_free_object(x_25);
lean_dec(x_53);
x_63 = !lean_is_exclusive(x_57);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_57, 0);
x_65 = lean_io_error_to_string(x_64);
x_66 = 3;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_array_get_size(x_50);
x_69 = lean_array_push(x_50, x_67);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_69);
lean_ctor_set(x_24, 0, x_68);
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_24);
return x_57;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_57, 0);
x_71 = lean_ctor_get(x_57, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_57);
x_72 = lean_io_error_to_string(x_70);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_get_size(x_50);
x_76 = lean_array_push(x_50, x_74);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_76);
lean_ctor_set(x_24, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_24);
lean_ctor_set(x_77, 1, x_71);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_25, 0);
lean_inc(x_78);
lean_dec(x_25);
x_79 = lean_ctor_get(x_26, 0);
lean_inc(x_79);
lean_dec(x_26);
x_80 = l_Lake_Workspace_addFacetsFromEnv(x_79, x_3, x_5);
lean_dec(x_3);
x_81 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_80, x_48);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
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
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_82);
lean_ctor_set(x_24, 0, x_85);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_24);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_78);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
 x_89 = lean_box(0);
}
x_90 = lean_io_error_to_string(x_87);
x_91 = 3;
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = lean_array_get_size(x_50);
x_94 = lean_array_push(x_50, x_92);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_94);
lean_ctor_set(x_24, 0, x_93);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_89;
 lean_ctor_set_tag(x_95, 0);
}
lean_ctor_set(x_95, 0, x_24);
lean_ctor_set(x_95, 1, x_88);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_24, 1);
lean_inc(x_96);
lean_dec(x_24);
x_97 = lean_ctor_get(x_25, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_98 = x_25;
} else {
 lean_dec_ref(x_25);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_26, 0);
lean_inc(x_99);
lean_dec(x_26);
x_100 = l_Lake_Workspace_addFacetsFromEnv(x_99, x_3, x_5);
lean_dec(x_3);
x_101 = l_IO_ofExcept___at_Lake_loadDepPackage___spec__1(x_100, x_48);
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
if (lean_is_scalar(x_98)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_98;
}
lean_ctor_set(x_105, 0, x_97);
lean_ctor_set(x_105, 1, x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_96);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_98);
lean_dec(x_97);
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
x_111 = lean_io_error_to_string(x_108);
x_112 = 3;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
x_114 = lean_array_get_size(x_96);
x_115 = lean_array_push(x_96, x_113);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
if (lean_is_scalar(x_110)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_110;
 lean_ctor_set_tag(x_117, 0);
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_109);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_5);
lean_dec(x_3);
x_118 = !lean_is_exclusive(x_23);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_23, 0);
lean_dec(x_119);
x_120 = !lean_is_exclusive(x_24);
if (x_120 == 0)
{
return x_23;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_24, 0);
x_122 = lean_ctor_get(x_24, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_24);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_23, 0, x_123);
return x_23;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_23, 1);
lean_inc(x_124);
lean_dec(x_23);
x_125 = lean_ctor_get(x_24, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_24, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_127 = x_24;
} else {
 lean_dec_ref(x_24);
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
lean_dec(x_5);
lean_dec(x_3);
x_130 = !lean_is_exclusive(x_23);
if (x_130 == 0)
{
return x_23;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_23, 0);
x_132 = lean_ctor_get(x_23, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_23);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadDepPackage___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_loadDepPackage___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lake_DepStackT_run___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DepStackT_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_DepStackT_run___rarg), 2, 0);
return x_3;
}
}
static lean_object* _init_l_Lake_depCycleError___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_depCycleError___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = 1;
x_3 = l_Lake_loadDepPackage___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
x_5 = l_Lake_depCycleError___rarg___lambda__1___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_8 = lean_string_append(x_6, x_7);
return x_8;
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
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_depCycleError___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dependency cycle detected:\n", 27, 27);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = 1;
x_8 = l_Lake_loadDepPackage___closed__1;
x_9 = l_Lean_Name_toString(x_5, x_7, x_8);
x_10 = l_Lake_depCycleError___rarg___lambda__1___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_13 = lean_string_append(x_11, x_12);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_13);
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
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = 1;
x_18 = l_Lake_loadDepPackage___closed__1;
x_19 = l_Lean_Name_toString(x_15, x_17, x_18);
x_20 = l_Lake_depCycleError___rarg___lambda__1___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_1 = x_16;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_box(0);
x_6 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__2(x_3, x_5);
x_7 = l_Lake_depCycleError___rarg___closed__2;
x_8 = l_String_intercalate(x_7, x_6);
x_9 = l_Lake_depCycleError___rarg___closed__3;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_apply_2(x_1, lean_box(0), x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_depCycleError___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__1___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_instMonadCallStackOfCallStackTOfMonad___rarg(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_depCycleError___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, x_3, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_apply_4(x_2, x_3, x_8, x_4, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1() {
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
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Name_instBEq;
lean_inc(x_11);
lean_inc(x_1);
x_14 = l_List_elem___rarg(x_13, x_1, x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_11);
lean_inc(x_15);
lean_ctor_set(x_9, 0, x_15);
x_16 = lean_apply_2(x_2, lean_box(0), x_9);
x_17 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__2), 5, 4);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_4);
lean_closure_set(x_17, 2, x_5);
lean_closure_set(x_17, 3, x_15);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_19, 0, x_1);
x_20 = lean_box(0);
x_21 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1;
x_22 = l_List_partition_loop___rarg(x_19, x_11, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_20);
x_26 = l_List_appendTR___rarg(x_24, x_25);
x_27 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__2;
x_28 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___rarg), 4, 2);
lean_closure_set(x_28, 0, x_27);
lean_closure_set(x_28, 1, x_7);
x_29 = l_Lake_depCycleError___rarg(x_28, x_26);
x_30 = lean_apply_2(x_29, x_8, x_12);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = l_Lean_Name_instBEq;
lean_inc(x_31);
lean_inc(x_1);
x_34 = l_List_elem___rarg(x_33, x_1, x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_7);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_31);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_apply_2(x_2, lean_box(0), x_36);
x_38 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__2), 5, 4);
lean_closure_set(x_38, 0, x_3);
lean_closure_set(x_38, 1, x_4);
lean_closure_set(x_38, 2, x_5);
lean_closure_set(x_38, 3, x_35);
x_39 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_37, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_1);
x_40 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_40, 0, x_1);
x_41 = lean_box(0);
x_42 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1;
x_43 = l_List_partition_loop___rarg(x_40, x_31, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_1);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_41);
x_47 = l_List_appendTR___rarg(x_45, x_46);
x_48 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__2;
x_49 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___rarg), 4, 2);
lean_closure_set(x_49, 0, x_48);
lean_closure_set(x_49, 1, x_7);
x_50 = l_Lake_depCycleError___rarg(x_49, x_47);
x_51 = lean_apply_2(x_50, x_8, x_32);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_inc(x_12);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4), 9, 8);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_6);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_3);
lean_closure_set(x_15, 6, x_4);
lean_closure_set(x_15, 7, x_7);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_StateT_lift___rarg), 4, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___rarg), 4, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
lean_inc(x_7);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__5), 8, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_7);
lean_closure_set(x_10, 3, x_9);
x_11 = l_Lake_recFetch___rarg(x_10, x_5);
x_12 = lean_apply_2(x_11, x_6, x_3);
x_13 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__6), 2, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lake_Workspace_addPackage(x_4, x_5);
x_7 = lean_box(0);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_7);
x_8 = lean_apply_2(x_1, lean_box(0), x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lake_Workspace_addPackage(x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_apply_2(x_1, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_apply_3(x_1, x_2, x_3, x_8);
x_10 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__2), 2, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_3(x_1, x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package requires itself (or a package with the same name)", 59, 59);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__3___boxed), 8, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_name_eq(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
x_17 = lean_apply_2(x_4, lean_box(0), x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_8);
x_19 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = 1;
x_21 = l_Lake_loadDepPackage___closed__1;
x_22 = l_Lean_Name_toString(x_12, x_20, x_21);
x_23 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_apply_2(x_6, lean_box(0), x_26);
x_28 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__5), 3, 2);
lean_closure_set(x_28, 0, x_9);
lean_closure_set(x_28, 1, x_4);
lean_inc(x_5);
x_29 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_27, x_28);
x_30 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_30, 0, x_10);
lean_closure_set(x_30, 1, x_8);
x_31 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_29, x_30);
return x_31;
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___boxed), 9, 6);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
x_12 = lean_ctor_get(x_10, 4);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__7___closed__1;
x_15 = l_Lake_RBNode_dFind___rarg(x_14, lean_box(0), x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_box(0);
lean_ctor_set(x_8, 0, x_16);
x_17 = lean_apply_2(x_4, lean_box(0), x_8);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_18, 0, x_11);
lean_closure_set(x_18, 1, x_7);
x_19 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
x_20 = lean_box(0);
lean_ctor_set(x_8, 0, x_20);
x_21 = lean_apply_2(x_4, lean_box(0), x_8);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___boxed), 9, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
x_25 = lean_ctor_get(x_22, 4);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__7___closed__1;
x_28 = l_Lake_RBNode_dFind___rarg(x_27, lean_box(0), x_25, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
x_31 = lean_apply_2(x_4, lean_box(0), x_30);
x_32 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_32, 0, x_24);
lean_closure_set(x_32, 1, x_7);
x_33 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_31, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_5);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
x_36 = lean_apply_2(x_4, lean_box(0), x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
lean_inc(x_2);
lean_inc(x_3);
x_13 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_12, x_3);
lean_inc(x_2);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_13, x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__7), 8, 7);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_7);
lean_closure_set(x_15, 3, x_1);
lean_closure_set(x_15, 4, x_2);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_9);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_get_size(x_10);
x_12 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__9___boxed), 5, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_nat_dec_lt(x_2, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_box(0);
lean_ctor_set(x_6, 0, x_14);
x_15 = lean_apply_2(x_3, lean_box(0), x_6);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_11, x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_box(0);
lean_ctor_set(x_6, 0, x_17);
x_18 = lean_apply_2(x_3, lean_box(0), x_6);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_6);
lean_dec(x_3);
x_19 = lean_usize_of_nat(x_2);
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = l_Array_foldlMUnsafe_fold___rarg(x_4, x_12, x_10, x_19, x_20, x_21);
x_23 = lean_apply_2(x_22, x_5, x_9);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_ctor_get(x_24, 3);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_get_size(x_26);
x_28 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__9___boxed), 5, 1);
lean_closure_set(x_28, 0, x_1);
x_29 = lean_nat_dec_lt(x_2, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
x_32 = lean_apply_2(x_3, lean_box(0), x_31);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_27, x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_4);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
x_36 = lean_apply_2(x_3, lean_box(0), x_35);
return x_36;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
x_37 = lean_usize_of_nat(x_2);
x_38 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_39 = lean_box(0);
x_40 = l_Array_foldlMUnsafe_fold___rarg(x_4, x_28, x_26, x_37, x_38, x_39);
x_41 = lean_apply_2(x_40, x_5, x_25);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_inc(x_10);
lean_ctor_set(x_8, 0, x_10);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, lean_box(0), x_8);
lean_inc(x_2);
lean_inc(x_3);
x_13 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_12, x_3);
lean_inc(x_2);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_13, x_3);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__10___boxed), 6, 5);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_7);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_1);
x_19 = lean_apply_2(x_1, lean_box(0), x_18);
lean_inc(x_2);
lean_inc(x_3);
x_20 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_19, x_3);
lean_inc(x_2);
x_21 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_20, x_3);
x_22 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__10___boxed), 6, 5);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_6);
lean_closure_set(x_22, 4, x_7);
x_23 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_1, 7);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__8___boxed), 10, 6);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
lean_closure_set(x_18, 4, x_1);
lean_closure_set(x_18, 5, x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__11), 8, 7);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_3);
lean_closure_set(x_19, 2, x_4);
lean_closure_set(x_19, 3, x_7);
lean_closure_set(x_19, 4, x_15);
lean_closure_set(x_19, 5, x_8);
lean_closure_set(x_19, 6, x_9);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
x_22 = lean_box(0);
lean_ctor_set(x_10, 0, x_22);
x_23 = lean_apply_2(x_2, lean_box(0), x_10);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_23, x_19);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_10);
lean_dec(x_2);
x_25 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_26 = 0;
x_27 = lean_box(0);
x_28 = l_Array_foldrMUnsafe_fold___rarg(x_8, x_18, x_16, x_25, x_26, x_27);
x_29 = lean_apply_2(x_28, x_9, x_13);
x_30 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_29, x_19);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_ctor_get(x_31, 3);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_array_get_size(x_33);
lean_dec(x_33);
x_35 = lean_ctor_get(x_1, 7);
lean_inc(x_35);
x_36 = lean_array_get_size(x_35);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_37 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__8___boxed), 10, 6);
lean_closure_set(x_37, 0, x_2);
lean_closure_set(x_37, 1, x_3);
lean_closure_set(x_37, 2, x_4);
lean_closure_set(x_37, 3, x_5);
lean_closure_set(x_37, 4, x_1);
lean_closure_set(x_37, 5, x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
x_38 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__11), 8, 7);
lean_closure_set(x_38, 0, x_2);
lean_closure_set(x_38, 1, x_3);
lean_closure_set(x_38, 2, x_4);
lean_closure_set(x_38, 3, x_7);
lean_closure_set(x_38, 4, x_34);
lean_closure_set(x_38, 5, x_8);
lean_closure_set(x_38, 6, x_9);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_lt(x_39, x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_32);
x_43 = lean_apply_2(x_2, lean_box(0), x_42);
x_44 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_43, x_38);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
x_45 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_46 = 0;
x_47 = lean_box(0);
x_48 = l_Array_foldrMUnsafe_fold___rarg(x_8, x_37, x_35, x_45, x_46, x_47);
x_49 = lean_apply_2(x_48, x_9, x_32);
x_50 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_49, x_38);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_1);
x_8 = l_StateT_instMonad___rarg(x_1);
x_9 = l_ReaderT_instMonad___rarg(x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_7);
lean_inc(x_12);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
lean_inc(x_12);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__1), 2, 1);
lean_closure_set(x_15, 0, x_12);
lean_inc(x_10);
lean_inc(x_15);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_15);
lean_inc(x_10);
lean_inc(x_15);
x_17 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_16, x_15);
lean_inc(x_10);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__12), 10, 9);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_12);
lean_closure_set(x_18, 2, x_10);
lean_closure_set(x_18, 3, x_15);
lean_closure_set(x_18, 4, x_3);
lean_closure_set(x_18, 5, x_2);
lean_closure_set(x_18, 6, x_5);
lean_closure_set(x_18, 7, x_9);
lean_closure_set(x_18, 8, x_6);
x_19 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_1, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg(x_2, x_3, x_4, x_5, x_12, x_6, x_9, x_7, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_5, x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_11 = lean_array_uget(x_4, x_5);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_3);
x_13 = lean_apply_3(x_2, x_11, x_3, x_9);
x_14 = lean_box_usize(x_5);
x_15 = lean_box_usize(x_6);
x_16 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_15);
lean_closure_set(x_16, 6, x_8);
x_17 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_9);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__3___boxed), 8, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_name_eq(x_6, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
x_16 = lean_apply_2(x_4, lean_box(0), x_15);
x_17 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_9);
x_18 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = 1;
x_20 = l_Lake_loadDepPackage___closed__1;
x_21 = l_Lean_Name_toString(x_6, x_19, x_20);
x_22 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_apply_2(x_7, lean_box(0), x_25);
x_27 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__5), 3, 2);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_4);
lean_inc(x_5);
x_28 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_26, x_27);
x_29 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_29, 0, x_11);
lean_closure_set(x_29, 1, x_9);
x_30 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_28, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__1___boxed), 10, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_7);
x_13 = lean_ctor_get(x_11, 4);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_box(0);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_apply_2(x_4, lean_box(0), x_9);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_8);
x_19 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
x_20 = lean_box(0);
lean_ctor_set(x_9, 0, x_20);
x_21 = lean_apply_2(x_4, lean_box(0), x_9);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__1___boxed), 10, 7);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
lean_closure_set(x_24, 6, x_7);
x_25 = lean_ctor_get(x_22, 4);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
x_30 = lean_apply_2(x_4, lean_box(0), x_29);
x_31 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__4), 3, 2);
lean_closure_set(x_31, 0, x_24);
lean_closure_set(x_31, 1, x_8);
x_32 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_30, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_5);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
x_35 = lean_apply_2(x_4, lean_box(0), x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, size_t x_11, size_t x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15, x_13, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, size_t x_11, size_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_11, x_12);
if (x_16 == 0)
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_13);
x_17 = 1;
x_18 = lean_usize_sub(x_11, x_17);
x_19 = lean_array_uget(x_10, x_18);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_15);
lean_inc(x_7);
x_22 = lean_apply_2(x_7, lean_box(0), x_21);
lean_inc(x_4);
lean_inc(x_8);
x_23 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_22, x_8);
lean_inc(x_4);
lean_inc(x_9);
x_24 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_23, x_9);
lean_inc(x_14);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_25 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__2), 9, 8);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_19);
lean_closure_set(x_25, 3, x_7);
lean_closure_set(x_25, 4, x_4);
lean_closure_set(x_25, 5, x_6);
lean_closure_set(x_25, 6, x_2);
lean_closure_set(x_25, 7, x_14);
lean_inc(x_4);
x_26 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_24, x_25);
x_27 = lean_box_usize(x_18);
x_28 = lean_box_usize(x_12);
x_29 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__3___boxed), 14, 13);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_5);
lean_closure_set(x_29, 5, x_6);
lean_closure_set(x_29, 6, x_7);
lean_closure_set(x_29, 7, x_8);
lean_closure_set(x_29, 8, x_9);
lean_closure_set(x_29, 9, x_10);
lean_closure_set(x_29, 10, x_27);
lean_closure_set(x_29, 11, x_28);
lean_closure_set(x_29, 12, x_14);
x_30 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_26, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_15);
x_34 = lean_apply_2(x_32, lean_box(0), x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___boxed), 15, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14, x_12, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__1), 2, 1);
lean_closure_set(x_15, 0, x_4);
x_16 = lean_usize_dec_eq(x_10, x_11);
if (x_16 == 0)
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
x_17 = 1;
x_18 = lean_usize_sub(x_10, x_17);
x_19 = lean_array_uget(x_9, x_18);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_14);
lean_inc(x_4);
x_22 = lean_apply_2(x_4, lean_box(0), x_21);
lean_inc(x_2);
lean_inc(x_15);
x_23 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_22, x_15);
lean_inc(x_2);
x_24 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_23, x_15);
lean_inc(x_13);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__2), 9, 8);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_7);
lean_closure_set(x_25, 2, x_19);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_2);
lean_closure_set(x_25, 5, x_8);
lean_closure_set(x_25, 6, x_6);
lean_closure_set(x_25, 7, x_13);
lean_inc(x_2);
x_26 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_24, x_25);
x_27 = lean_box_usize(x_18);
x_28 = lean_box_usize(x_11);
x_29 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg___lambda__1___boxed), 13, 12);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_5);
lean_closure_set(x_29, 5, x_6);
lean_closure_set(x_29, 6, x_7);
lean_closure_set(x_29, 7, x_8);
lean_closure_set(x_29, 8, x_9);
lean_closure_set(x_29, 9, x_27);
lean_closure_set(x_29, 10, x_28);
lean_closure_set(x_29, 11, x_13);
x_30 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_26, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_14);
x_34 = lean_apply_2(x_32, lean_box(0), x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg___boxed), 14, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, size_t x_11, size_t x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15, x_13, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, size_t x_11, size_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_11, x_12);
if (x_16 == 0)
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_13);
x_17 = 1;
x_18 = lean_usize_sub(x_11, x_17);
x_19 = lean_array_uget(x_10, x_18);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_15);
lean_inc(x_7);
x_22 = lean_apply_2(x_7, lean_box(0), x_21);
lean_inc(x_4);
lean_inc(x_8);
x_23 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_22, x_8);
lean_inc(x_4);
lean_inc(x_9);
x_24 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_23, x_9);
lean_inc(x_14);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_25 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__2), 9, 8);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_19);
lean_closure_set(x_25, 3, x_7);
lean_closure_set(x_25, 4, x_4);
lean_closure_set(x_25, 5, x_6);
lean_closure_set(x_25, 6, x_2);
lean_closure_set(x_25, 7, x_14);
lean_inc(x_4);
x_26 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_24, x_25);
x_27 = lean_box_usize(x_18);
x_28 = lean_box_usize(x_12);
x_29 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg___lambda__1___boxed), 14, 13);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_5);
lean_closure_set(x_29, 5, x_6);
lean_closure_set(x_29, 6, x_7);
lean_closure_set(x_29, 7, x_8);
lean_closure_set(x_29, 8, x_9);
lean_closure_set(x_29, 9, x_10);
lean_closure_set(x_29, 10, x_27);
lean_closure_set(x_29, 11, x_28);
lean_closure_set(x_29, 12, x_14);
x_30 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_26, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_15);
x_34 = lean_apply_2(x_32, lean_box(0), x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg___boxed), 15, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14, x_12, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__1), 2, 1);
lean_closure_set(x_15, 0, x_4);
x_16 = lean_usize_dec_eq(x_10, x_11);
if (x_16 == 0)
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
x_17 = 1;
x_18 = lean_usize_sub(x_10, x_17);
x_19 = lean_array_uget(x_9, x_18);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_14);
lean_inc(x_4);
x_22 = lean_apply_2(x_4, lean_box(0), x_21);
lean_inc(x_2);
lean_inc(x_15);
x_23 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_22, x_15);
lean_inc(x_2);
x_24 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_23, x_15);
lean_inc(x_13);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__2), 9, 8);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_7);
lean_closure_set(x_25, 2, x_19);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_2);
lean_closure_set(x_25, 5, x_8);
lean_closure_set(x_25, 6, x_6);
lean_closure_set(x_25, 7, x_13);
lean_inc(x_2);
x_26 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_24, x_25);
x_27 = lean_box_usize(x_18);
x_28 = lean_box_usize(x_11);
x_29 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg___lambda__1___boxed), 13, 12);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_5);
lean_closure_set(x_29, 5, x_6);
lean_closure_set(x_29, 6, x_7);
lean_closure_set(x_29, 7, x_8);
lean_closure_set(x_29, 8, x_9);
lean_closure_set(x_29, 9, x_27);
lean_closure_set(x_29, 10, x_28);
lean_closure_set(x_29, 11, x_13);
x_30 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_26, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_14);
x_34 = lean_apply_2(x_32, lean_box(0), x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg___boxed), 14, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__2(x_4, x_7);
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
x_17 = lean_alloc_closure((void*)(l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg___lambda__1), 3, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_6);
x_18 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_1, x_15);
x_17 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16, x_10, x_13, x_11, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_9, x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_15 = lean_array_uget(x_8, x_9);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_13);
x_18 = lean_box_usize(x_9);
x_19 = lean_box_usize(x_10);
x_20 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg___lambda__1___boxed), 12, 11);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_8);
lean_closure_set(x_20, 9, x_19);
lean_closure_set(x_20, 10, x_12);
x_21 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_17, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_13);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg___boxed), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_14);
x_16 = lean_nat_dec_lt(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
lean_ctor_set(x_10, 0, x_17);
x_18 = lean_apply_2(x_2, lean_box(0), x_10);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_box(0);
lean_ctor_set(x_10, 0, x_20);
x_21 = lean_apply_2(x_2, lean_box(0), x_10);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_10);
lean_dec(x_2);
x_22 = lean_usize_of_nat(x_1);
x_23 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_24 = lean_box(0);
lean_inc(x_3);
x_25 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg(x_3, x_4, x_5, x_6, x_7, x_3, x_8, x_14, x_22, x_23, x_24, x_9, x_13);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_ctor_get(x_26, 3);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_get_size(x_28);
x_30 = lean_nat_dec_lt(x_1, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_33 = lean_apply_2(x_2, lean_box(0), x_32);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_29, x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
x_37 = lean_apply_2(x_2, lean_box(0), x_36);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_38 = lean_usize_of_nat(x_1);
x_39 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_40 = lean_box(0);
lean_inc(x_3);
x_41 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg(x_3, x_4, x_5, x_6, x_7, x_3, x_8, x_28, x_38, x_39, x_40, x_9, x_27);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
lean_inc(x_13);
lean_ctor_set(x_11, 0, x_13);
lean_inc(x_1);
x_15 = lean_apply_2(x_1, lean_box(0), x_11);
lean_inc(x_2);
lean_inc(x_3);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_15, x_3);
lean_inc(x_2);
x_17 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_16, x_3);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__1___boxed), 10, 9);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_5);
lean_closure_set(x_18, 3, x_6);
lean_closure_set(x_18, 4, x_7);
lean_closure_set(x_18, 5, x_8);
lean_closure_set(x_18, 6, x_2);
lean_closure_set(x_18, 7, x_9);
lean_closure_set(x_18, 8, x_10);
x_19 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_1);
x_22 = lean_apply_2(x_1, lean_box(0), x_21);
lean_inc(x_2);
lean_inc(x_3);
x_23 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_22, x_3);
lean_inc(x_2);
x_24 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_23, x_3);
lean_inc(x_2);
x_25 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__1___boxed), 10, 9);
lean_closure_set(x_25, 0, x_4);
lean_closure_set(x_25, 1, x_1);
lean_closure_set(x_25, 2, x_5);
lean_closure_set(x_25, 3, x_6);
lean_closure_set(x_25, 4, x_7);
lean_closure_set(x_25, 5, x_8);
lean_closure_set(x_25, 6, x_2);
lean_closure_set(x_25, 7, x_9);
lean_closure_set(x_25, 8, x_10);
x_26 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 7);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_le(x_19, x_19);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__2), 11, 10);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_4);
lean_closure_set(x_21, 3, x_17);
lean_closure_set(x_21, 4, x_5);
lean_closure_set(x_21, 5, x_6);
lean_closure_set(x_21, 6, x_7);
lean_closure_set(x_21, 7, x_8);
lean_closure_set(x_21, 8, x_9);
lean_closure_set(x_21, 9, x_10);
if (x_20 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_apply_2(x_2, lean_box(0), x_12);
x_26 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_25, x_21);
return x_26;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_12);
x_27 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_28 = 0;
x_29 = lean_box(0);
lean_inc(x_2);
x_30 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg(x_7, x_8, x_2, x_2, x_5, x_6, x_1, x_11, x_18, x_27, x_28, x_29, x_10, x_15);
x_31 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_30, x_21);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_19);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_34 = lean_box(0);
lean_ctor_set(x_12, 0, x_34);
x_35 = lean_apply_2(x_2, lean_box(0), x_12);
x_36 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_35, x_21);
return x_36;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_12);
x_37 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_38 = 0;
x_39 = lean_box(0);
lean_inc(x_2);
x_40 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg(x_7, x_8, x_2, x_2, x_5, x_6, x_1, x_11, x_18, x_37, x_38, x_39, x_10, x_15);
x_41 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_40, x_21);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_12, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_12);
x_44 = lean_ctor_get(x_42, 3);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
lean_dec(x_44);
x_46 = lean_ctor_get(x_1, 7);
lean_inc(x_46);
x_47 = lean_array_get_size(x_46);
x_48 = lean_nat_dec_le(x_47, x_47);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_49 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__2), 11, 10);
lean_closure_set(x_49, 0, x_2);
lean_closure_set(x_49, 1, x_3);
lean_closure_set(x_49, 2, x_4);
lean_closure_set(x_49, 3, x_45);
lean_closure_set(x_49, 4, x_5);
lean_closure_set(x_49, 5, x_6);
lean_closure_set(x_49, 6, x_7);
lean_closure_set(x_49, 7, x_8);
lean_closure_set(x_49, 8, x_9);
lean_closure_set(x_49, 9, x_10);
if (x_48 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_lt(x_50, x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
x_54 = lean_apply_2(x_2, lean_box(0), x_53);
x_55 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_54, x_49);
return x_55;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_57 = 0;
x_58 = lean_box(0);
lean_inc(x_2);
x_59 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg(x_7, x_8, x_2, x_2, x_5, x_6, x_1, x_11, x_46, x_56, x_57, x_58, x_10, x_43);
x_60 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_59, x_49);
return x_60;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_lt(x_61, x_47);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_43);
x_65 = lean_apply_2(x_2, lean_box(0), x_64);
x_66 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_65, x_49);
return x_66;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_68 = 0;
x_69 = lean_box(0);
lean_inc(x_2);
x_70 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg(x_7, x_8, x_2, x_2, x_5, x_6, x_1, x_11, x_46, x_67, x_68, x_69, x_10, x_43);
x_71 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_70, x_49);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_ctor_set(x_10, 0, x_13);
lean_inc(x_1);
x_14 = lean_apply_2(x_1, lean_box(0), x_10);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__1), 2, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_2);
lean_inc(x_15);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_14, x_15);
lean_inc(x_2);
lean_inc(x_15);
x_17 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_16, x_15);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__3), 12, 11);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_15);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_5);
lean_closure_set(x_18, 6, x_6);
lean_closure_set(x_18, 7, x_7);
lean_closure_set(x_18, 8, x_12);
lean_closure_set(x_18, 9, x_8);
lean_closure_set(x_18, 10, x_9);
x_19 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_1);
x_23 = lean_apply_2(x_1, lean_box(0), x_22);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__1), 2, 1);
lean_closure_set(x_24, 0, x_1);
lean_inc(x_2);
lean_inc(x_24);
x_25 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_23, x_24);
lean_inc(x_2);
lean_inc(x_24);
x_26 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_25, x_24);
lean_inc(x_2);
x_27 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__3), 12, 11);
lean_closure_set(x_27, 0, x_3);
lean_closure_set(x_27, 1, x_1);
lean_closure_set(x_27, 2, x_2);
lean_closure_set(x_27, 3, x_24);
lean_closure_set(x_27, 4, x_4);
lean_closure_set(x_27, 5, x_5);
lean_closure_set(x_27, 6, x_6);
lean_closure_set(x_27, 7, x_7);
lean_closure_set(x_27, 8, x_20);
lean_closure_set(x_27, 9, x_8);
lean_closure_set(x_27, 10, x_9);
x_28 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_26, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_1, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_12);
lean_inc(x_15);
lean_ctor_set(x_10, 0, x_15);
lean_inc(x_2);
x_16 = lean_apply_2(x_2, lean_box(0), x_10);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__4), 10, 9);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_6);
lean_closure_set(x_17, 5, x_7);
lean_closure_set(x_17, 6, x_8);
lean_closure_set(x_17, 7, x_15);
lean_closure_set(x_17, 8, x_1);
x_18 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1;
x_21 = l_List_partition_loop___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__7(x_1, x_12, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_19);
x_25 = l_List_appendTR___rarg(x_23, x_24);
x_26 = l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg(x_5, x_6, x_4, x_25, x_9, x_13);
lean_dec(x_4);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_1, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_1);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_27);
lean_inc(x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
lean_inc(x_2);
x_32 = lean_apply_2(x_2, lean_box(0), x_31);
lean_inc(x_3);
x_33 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__4), 10, 9);
lean_closure_set(x_33, 0, x_2);
lean_closure_set(x_33, 1, x_3);
lean_closure_set(x_33, 2, x_4);
lean_closure_set(x_33, 3, x_5);
lean_closure_set(x_33, 4, x_6);
lean_closure_set(x_33, 5, x_7);
lean_closure_set(x_33, 6, x_8);
lean_closure_set(x_33, 7, x_30);
lean_closure_set(x_33, 8, x_1);
x_34 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_32, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1;
x_37 = l_List_partition_loop___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__7(x_1, x_27, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_1);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_35);
x_41 = l_List_appendTR___rarg(x_39, x_40);
x_42 = l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg(x_5, x_6, x_4, x_41, x_9, x_28);
lean_dec(x_4);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_inc(x_12);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
lean_inc(x_5);
x_15 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__5___boxed), 10, 9);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_1);
lean_closure_set(x_15, 5, x_2);
lean_closure_set(x_15, 6, x_3);
lean_closure_set(x_15, 7, x_4);
lean_closure_set(x_15, 8, x_7);
x_16 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc_n(x_7, 2);
lean_inc(x_1);
x_8 = l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg(x_1, x_2, x_3, x_7, x_7, x_5, x_6, x_4);
x_9 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__6), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__1___rarg(x_1, x_2, x_4, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg___lambda__1(x_9, x_2, x_3, x_4, x_5, x_10, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___rarg(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_16 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_17 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15, x_16, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_17 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_18 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16, x_17, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_15 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_16 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14, x_15, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_16 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_17 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__3___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15, x_16, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_16 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_17 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15, x_16, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_17 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_18 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16, x_17, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_15 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_16 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14, x_15, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_16 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_17 = l_Array_foldrMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__5___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15, x_16, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg___lambda__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_15 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_16 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__2___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__10___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14, x_15, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_recFetch___at___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___spec__9___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_reuseManifest___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_5);
x_10 = lean_array_uget(x_2, x_3);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*5);
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
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ignoring previous manifest because it failed to load: ", 56, 56);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_8 = lean_string_append(x_7, x_1);
x_9 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1___closed__1;
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
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not rename workspace packages directory: ", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("workspace packages directory changed; renaming '", 48, 48);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to '", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_78 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__2;
x_79 = lean_string_append(x_78, x_65);
x_80 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__3;
x_81 = lean_string_append(x_79, x_80);
x_82 = l_System_FilePath_join(x_64, x_71);
lean_dec(x_71);
x_83 = lean_string_append(x_81, x_82);
x_84 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4;
x_85 = lean_string_append(x_83, x_84);
x_86 = 1;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_array_push(x_6, x_87);
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
x_140 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__2;
x_141 = lean_string_append(x_140, x_65);
x_142 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__3;
x_143 = lean_string_append(x_141, x_142);
x_144 = l_System_FilePath_join(x_64, x_132);
lean_dec(x_132);
x_145 = lean_string_append(x_143, x_144);
x_146 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4;
x_147 = lean_string_append(x_145, x_146);
x_148 = 1;
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_148);
x_150 = lean_array_push(x_6, x_149);
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
x_190 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__2;
x_191 = lean_string_append(x_190, x_176);
x_192 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__3;
x_193 = lean_string_append(x_191, x_192);
x_194 = l_System_FilePath_join(x_175, x_182);
lean_dec(x_182);
x_195 = lean_string_append(x_193, x_194);
x_196 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4;
x_197 = lean_string_append(x_195, x_196);
x_198 = 1;
x_199 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_198);
x_200 = lean_array_push(x_6, x_199);
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
x_17 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__1;
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
x_29 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__1;
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
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": no previous manifest, creating one from scratch", 49, 49);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = 0;
x_10 = l_Lake_loadDepPackage___closed__1;
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_106 = lean_ctor_get(x_6, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_6, 4);
lean_inc(x_107);
x_108 = l_System_FilePath_join(x_106, x_107);
lean_dec(x_107);
x_109 = l_Lake_Manifest_load(x_108, x_5);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_109, 1, x_3);
lean_ctor_set(x_109, 0, x_113);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_4);
x_12 = x_114;
x_13 = x_112;
goto block_105;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_109, 0);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_109);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_3);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_4);
x_12 = x_119;
x_13 = x_116;
goto block_105;
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_109);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_109, 0);
x_122 = lean_ctor_get(x_109, 1);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set_tag(x_109, 0);
lean_ctor_set(x_109, 1, x_3);
lean_ctor_set(x_109, 0, x_123);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_4);
x_12 = x_124;
x_13 = x_122;
goto block_105;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_125);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_3);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_4);
x_12 = x_129;
x_13 = x_126;
goto block_105;
}
}
block_105:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 11)
{
uint8_t x_17; 
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_23 = lean_string_append(x_22, x_11);
lean_dec(x_11);
x_24 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_push(x_18, x_27);
x_29 = lean_box(0);
lean_ctor_set(x_14, 0, x_29);
lean_ctor_set(x_12, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_13);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_33 = lean_string_append(x_32, x_11);
lean_dec(x_11);
x_34 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = 1;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_push(x_18, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_12, 1, x_38);
lean_ctor_set(x_12, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_12);
lean_ctor_set(x_41, 1, x_13);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_dec(x_12);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_44 = x_14;
} else {
 lean_dec_ref(x_14);
 x_44 = lean_box(0);
}
x_45 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_46 = lean_string_append(x_45, x_11);
lean_dec(x_11);
x_47 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_push(x_42, x_50);
x_52 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_44;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_13);
return x_55;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_dec(x_12);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_dec(x_14);
x_58 = lean_box(0);
x_59 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1(x_11, x_16, x_58, x_57, x_56, x_13);
lean_dec(x_11);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_14);
lean_dec(x_11);
x_60 = !lean_is_exclusive(x_12);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_12, 1);
x_62 = lean_ctor_get(x_12, 0);
lean_dec(x_62);
x_63 = lean_io_error_to_string(x_16);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_61);
x_67 = lean_array_push(x_61, x_65);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_67);
lean_ctor_set(x_12, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_12);
lean_ctor_set(x_68, 1, x_13);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_12, 1);
lean_inc(x_69);
lean_dec(x_12);
x_70 = lean_io_error_to_string(x_16);
x_71 = 3;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_array_get_size(x_69);
x_74 = lean_array_push(x_69, x_72);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_13);
return x_76;
}
}
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_12, 1);
lean_inc(x_77);
lean_dec(x_12);
x_78 = lean_ctor_get(x_14, 1);
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_ctor_get(x_15, 0);
lean_inc(x_79);
lean_dec(x_15);
x_80 = lean_box(0);
x_81 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2(x_79, x_6, x_7, x_80, x_78, x_77, x_13);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_82 = lean_ctor_get(x_12, 1);
lean_inc(x_82);
lean_dec(x_12);
x_83 = lean_ctor_get(x_14, 1);
lean_inc(x_83);
lean_dec(x_14);
x_84 = lean_ctor_get(x_15, 0);
lean_inc(x_84);
lean_dec(x_15);
x_85 = lean_ctor_get(x_84, 3);
lean_inc(x_85);
x_86 = lean_array_get_size(x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_dec_lt(x_87, x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_86);
lean_dec(x_85);
x_89 = lean_box(0);
x_90 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2(x_84, x_6, x_7, x_89, x_83, x_82, x_13);
return x_90;
}
else
{
uint8_t x_91; 
x_91 = lean_nat_dec_le(x_86, x_86);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_86);
lean_dec(x_85);
x_92 = lean_box(0);
x_93 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2(x_84, x_6, x_7, x_92, x_83, x_82, x_13);
return x_93;
}
else
{
size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_94 = 0;
x_95 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_96 = lean_box(0);
x_97 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_reuseManifest___spec__1(x_2, x_85, x_94, x_95, x_96, x_83, x_82, x_13);
lean_dec(x_85);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2(x_84, x_6, x_7, x_102, x_103, x_101, x_100);
lean_dec(x_102);
return x_104;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_reuseManifest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_reuseManifest___spec__1(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_5);
x_10 = lean_array_uget(x_2, x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = l_Lean_NameMap_contains___rarg(x_6, x_12);
if (x_17 == 0)
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = l_System_FilePath_join(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_21);
x_22 = 1;
lean_inc(x_12);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_22);
x_23 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_6, x_12, x_10);
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
x_26 = lean_box(0);
x_3 = x_25;
x_5 = x_26;
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = l_System_FilePath_join(x_29, x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = 1;
lean_inc(x_12);
lean_ctor_set(x_10, 4, x_31);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_32);
x_33 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_6, x_12, x_10);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_36 = lean_box(0);
x_3 = x_35;
x_5 = x_36;
x_6 = x_33;
goto _start;
}
}
else
{
uint8_t x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_38 = 1;
lean_inc(x_12);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_38);
x_39 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_6, x_12, x_10);
x_40 = 1;
x_41 = lean_usize_add(x_3, x_40);
x_42 = lean_box(0);
x_3 = x_41;
x_5 = x_42;
x_6 = x_39;
goto _start;
}
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
lean_free_object(x_10);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_44 = 1;
x_45 = lean_usize_add(x_3, x_44);
x_46 = lean_box(0);
x_3 = x_45;
x_5 = x_46;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
x_50 = lean_ctor_get(x_10, 2);
x_51 = lean_ctor_get(x_10, 3);
x_52 = lean_ctor_get(x_10, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_53 = l_Lean_NameMap_contains___rarg(x_6, x_48);
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
lean_dec(x_54);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
x_59 = 1;
lean_inc(x_48);
x_60 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_60, 0, x_48);
lean_ctor_set(x_60, 1, x_49);
lean_ctor_set(x_60, 2, x_50);
lean_ctor_set(x_60, 3, x_51);
lean_ctor_set(x_60, 4, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*5, x_59);
x_61 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_6, x_48, x_60);
x_62 = 1;
x_63 = lean_usize_add(x_3, x_62);
x_64 = lean_box(0);
x_3 = x_63;
x_5 = x_64;
x_6 = x_61;
goto _start;
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; lean_object* x_71; 
x_66 = 1;
lean_inc(x_48);
x_67 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_67, 0, x_48);
lean_ctor_set(x_67, 1, x_49);
lean_ctor_set(x_67, 2, x_50);
lean_ctor_set(x_67, 3, x_51);
lean_ctor_set(x_67, 4, x_52);
lean_ctor_set_uint8(x_67, sizeof(void*)*5, x_66);
x_68 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_6, x_48, x_67);
x_69 = 1;
x_70 = lean_usize_add(x_3, x_69);
x_71 = lean_box(0);
x_3 = x_70;
x_5 = x_71;
x_6 = x_68;
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
lean_dec(x_48);
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
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_5);
lean_ctor_set(x_77, 1, x_6);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_7);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_8);
return x_79;
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ignoring manifest because it failed to load: ", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ignoring missing manifest '", 29, 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_198; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
x_7 = l_System_FilePath_join(x_5, x_6);
lean_dec(x_6);
x_198 = l_Lake_Manifest_load(x_7, x_4);
if (lean_obj_tag(x_198) == 0)
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_198, 0);
x_201 = lean_ctor_get(x_198, 1);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_198, 1, x_2);
lean_ctor_set(x_198, 0, x_202);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_3);
x_8 = x_203;
x_9 = x_201;
goto block_197;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_198, 0);
x_205 = lean_ctor_get(x_198, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_198);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_204);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_2);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_3);
x_8 = x_208;
x_9 = x_205;
goto block_197;
}
}
else
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_198);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_198, 0);
x_211 = lean_ctor_get(x_198, 1);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set_tag(x_198, 0);
lean_ctor_set(x_198, 1, x_2);
lean_ctor_set(x_198, 0, x_212);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_198);
lean_ctor_set(x_213, 1, x_3);
x_8 = x_213;
x_9 = x_211;
goto block_197;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_214 = lean_ctor_get(x_198, 0);
x_215 = lean_ctor_get(x_198, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_198);
x_216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_216, 0, x_214);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_2);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_3);
x_8 = x_218;
x_9 = x_215;
goto block_197;
}
}
block_197:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 11)
{
uint8_t x_13; 
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_8, 1);
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = l_Lake_loadDepPackage___closed__1;
x_22 = l_Lean_Name_toString(x_19, x_20, x_21);
x_23 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_7);
lean_dec(x_7);
x_28 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4;
x_29 = lean_string_append(x_27, x_28);
x_30 = 2;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_push(x_14, x_31);
x_33 = lean_box(0);
lean_ctor_set(x_10, 0, x_33);
lean_ctor_set(x_8, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 1;
x_39 = l_Lake_loadDepPackage___closed__1;
x_40 = l_Lean_Name_toString(x_37, x_38, x_39);
x_41 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_44, x_7);
lean_dec(x_7);
x_46 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4;
x_47 = lean_string_append(x_45, x_46);
x_48 = 2;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_array_push(x_14, x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_35);
lean_ctor_set(x_8, 1, x_50);
lean_ctor_set(x_8, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_9);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_dec(x_8);
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
x_57 = lean_ctor_get(x_1, 2);
lean_inc(x_57);
lean_dec(x_1);
x_58 = lean_ctor_get(x_57, 2);
lean_inc(x_58);
lean_dec(x_57);
x_59 = 1;
x_60 = l_Lake_loadDepPackage___closed__1;
x_61 = l_Lean_Name_toString(x_58, x_59, x_60);
x_62 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_64 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__2;
x_65 = lean_string_append(x_63, x_64);
x_66 = lean_string_append(x_65, x_7);
lean_dec(x_7);
x_67 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4;
x_68 = lean_string_append(x_66, x_67);
x_69 = 2;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_array_push(x_54, x_70);
x_72 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_56;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_55);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_7);
x_76 = !lean_is_exclusive(x_8);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_8, 1);
x_78 = lean_ctor_get(x_8, 0);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_10);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_80 = lean_ctor_get(x_10, 0);
lean_dec(x_80);
x_81 = lean_ctor_get(x_1, 2);
lean_inc(x_81);
lean_dec(x_1);
x_82 = lean_ctor_get(x_81, 2);
lean_inc(x_82);
lean_dec(x_81);
x_83 = 1;
x_84 = l_Lake_loadDepPackage___closed__1;
x_85 = l_Lean_Name_toString(x_82, x_83, x_84);
x_86 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_io_error_to_string(x_12);
x_91 = lean_string_append(x_89, x_90);
lean_dec(x_90);
x_92 = lean_string_append(x_91, x_86);
x_93 = 2;
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_93);
x_95 = lean_array_push(x_77, x_94);
x_96 = lean_box(0);
lean_ctor_set(x_10, 0, x_96);
lean_ctor_set(x_8, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_8);
lean_ctor_set(x_97, 1, x_9);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_98 = lean_ctor_get(x_10, 1);
lean_inc(x_98);
lean_dec(x_10);
x_99 = lean_ctor_get(x_1, 2);
lean_inc(x_99);
lean_dec(x_1);
x_100 = lean_ctor_get(x_99, 2);
lean_inc(x_100);
lean_dec(x_99);
x_101 = 1;
x_102 = l_Lake_loadDepPackage___closed__1;
x_103 = l_Lean_Name_toString(x_100, x_101, x_102);
x_104 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_105 = lean_string_append(x_104, x_103);
lean_dec(x_103);
x_106 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1;
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_io_error_to_string(x_12);
x_109 = lean_string_append(x_107, x_108);
lean_dec(x_108);
x_110 = lean_string_append(x_109, x_104);
x_111 = 2;
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = lean_array_push(x_77, x_112);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_98);
lean_ctor_set(x_8, 1, x_113);
lean_ctor_set(x_8, 0, x_115);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_8);
lean_ctor_set(x_116, 1, x_9);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_117 = lean_ctor_get(x_8, 1);
lean_inc(x_117);
lean_dec(x_8);
x_118 = lean_ctor_get(x_10, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_119 = x_10;
} else {
 lean_dec_ref(x_10);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_1, 2);
lean_inc(x_120);
lean_dec(x_1);
x_121 = lean_ctor_get(x_120, 2);
lean_inc(x_121);
lean_dec(x_120);
x_122 = 1;
x_123 = l_Lake_loadDepPackage___closed__1;
x_124 = l_Lean_Name_toString(x_121, x_122, x_123);
x_125 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_126 = lean_string_append(x_125, x_124);
lean_dec(x_124);
x_127 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_io_error_to_string(x_12);
x_130 = lean_string_append(x_128, x_129);
lean_dec(x_129);
x_131 = lean_string_append(x_130, x_125);
x_132 = 2;
x_133 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_132);
x_134 = lean_array_push(x_117, x_133);
x_135 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_119;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_118);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_9);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_7);
x_139 = !lean_is_exclusive(x_8);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = lean_ctor_get(x_8, 1);
x_141 = lean_ctor_get(x_8, 0);
lean_dec(x_141);
x_142 = !lean_is_exclusive(x_10);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_143 = lean_ctor_get(x_10, 1);
x_144 = lean_ctor_get(x_10, 0);
lean_dec(x_144);
x_145 = lean_ctor_get(x_11, 0);
lean_inc(x_145);
lean_dec(x_11);
x_146 = lean_ctor_get(x_145, 3);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_array_get_size(x_146);
x_148 = lean_unsigned_to_nat(0u);
x_149 = lean_nat_dec_lt(x_148, x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_1);
x_150 = lean_box(0);
lean_ctor_set(x_10, 0, x_150);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_8);
lean_ctor_set(x_151, 1, x_9);
return x_151;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_147, x_147);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_1);
x_153 = lean_box(0);
lean_ctor_set(x_10, 0, x_153);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_8);
lean_ctor_set(x_154, 1, x_9);
return x_154;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; lean_object* x_158; 
lean_free_object(x_10);
lean_free_object(x_8);
x_155 = 0;
x_156 = lean_usize_of_nat(x_147);
lean_dec(x_147);
x_157 = lean_box(0);
x_158 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___spec__1(x_1, x_146, x_155, x_156, x_157, x_143, x_140, x_9);
lean_dec(x_146);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_159 = lean_ctor_get(x_10, 1);
lean_inc(x_159);
lean_dec(x_10);
x_160 = lean_ctor_get(x_11, 0);
lean_inc(x_160);
lean_dec(x_11);
x_161 = lean_ctor_get(x_160, 3);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_array_get_size(x_161);
x_163 = lean_unsigned_to_nat(0u);
x_164 = lean_nat_dec_lt(x_163, x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_1);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_159);
lean_ctor_set(x_8, 0, x_166);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_8);
lean_ctor_set(x_167, 1, x_9);
return x_167;
}
else
{
uint8_t x_168; 
x_168 = lean_nat_dec_le(x_162, x_162);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_1);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_159);
lean_ctor_set(x_8, 0, x_170);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_8);
lean_ctor_set(x_171, 1, x_9);
return x_171;
}
else
{
size_t x_172; size_t x_173; lean_object* x_174; lean_object* x_175; 
lean_free_object(x_8);
x_172 = 0;
x_173 = lean_usize_of_nat(x_162);
lean_dec(x_162);
x_174 = lean_box(0);
x_175 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___spec__1(x_1, x_161, x_172, x_173, x_174, x_159, x_140, x_9);
lean_dec(x_161);
return x_175;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_176 = lean_ctor_get(x_8, 1);
lean_inc(x_176);
lean_dec(x_8);
x_177 = lean_ctor_get(x_10, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_178 = x_10;
} else {
 lean_dec_ref(x_10);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_11, 0);
lean_inc(x_179);
lean_dec(x_11);
x_180 = lean_ctor_get(x_179, 3);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_array_get_size(x_180);
x_182 = lean_unsigned_to_nat(0u);
x_183 = lean_nat_dec_lt(x_182, x_181);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_1);
x_184 = lean_box(0);
if (lean_is_scalar(x_178)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_178;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_177);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_9);
return x_187;
}
else
{
uint8_t x_188; 
x_188 = lean_nat_dec_le(x_181, x_181);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_1);
x_189 = lean_box(0);
if (lean_is_scalar(x_178)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_178;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_177);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_176);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_9);
return x_192;
}
else
{
size_t x_193; size_t x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_178);
x_193 = 0;
x_194 = lean_usize_of_nat(x_181);
lean_dec(x_181);
x_195 = lean_box(0);
x_196 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___spec__1(x_1, x_180, x_193, x_194, x_195, x_177, x_176, x_9);
lean_dec(x_180);
return x_196;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___spec__1(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_4, x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; 
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
x_46 = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__1;
x_47 = lean_string_dec_eq(x_45, x_46);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
x_53 = lean_name_eq(x_49, x_52);
lean_dec(x_52);
lean_dec(x_49);
x_54 = l_instDecidableNot___rarg(x_53);
if (x_47 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l_System_FilePath_join(x_45, x_46);
x_59 = l_Lake_Dependency_materialize(x_3, x_54, x_55, x_56, x_57, x_58, x_5, x_6);
lean_dec(x_55);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_59, 1);
x_63 = lean_ctor_get(x_59, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_60, 0);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 0, x_65);
lean_ctor_set(x_60, 0, x_59);
x_7 = x_60;
x_8 = x_62;
goto block_42;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_67);
x_7 = x_68;
x_8 = x_62;
goto block_42;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_dec(x_59);
x_70 = lean_ctor_get(x_60, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_72 = x_60;
} else {
 lean_dec_ref(x_60);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_4);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_7 = x_74;
x_8 = x_69;
goto block_42;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
lean_dec(x_4);
x_75 = lean_ctor_get(x_59, 1);
lean_inc(x_75);
lean_dec(x_59);
x_76 = !lean_is_exclusive(x_60);
if (x_76 == 0)
{
x_7 = x_60;
x_8 = x_75;
goto block_42;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_60, 0);
x_78 = lean_ctor_get(x_60, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_60);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_7 = x_79;
x_8 = x_75;
goto block_42;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_1, 1);
lean_inc(x_80);
lean_dec(x_1);
x_81 = lean_ctor_get(x_50, 0);
lean_inc(x_81);
lean_dec(x_50);
x_82 = lean_ctor_get(x_51, 0);
lean_inc(x_82);
lean_dec(x_51);
x_83 = l_Lake_Dependency_materialize(x_3, x_54, x_80, x_81, x_82, x_45, x_5, x_6);
lean_dec(x_80);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_83, 1);
x_87 = lean_ctor_get(x_83, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_84, 0);
lean_ctor_set(x_83, 1, x_4);
lean_ctor_set(x_83, 0, x_89);
lean_ctor_set(x_84, 0, x_83);
x_7 = x_84;
x_8 = x_86;
goto block_42;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
lean_ctor_set(x_83, 1, x_4);
lean_ctor_set(x_83, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_91);
x_7 = x_92;
x_8 = x_86;
goto block_42;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_83, 1);
lean_inc(x_93);
lean_dec(x_83);
x_94 = lean_ctor_get(x_84, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_84, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_96 = x_84;
} else {
 lean_dec_ref(x_84);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_4);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
x_7 = x_98;
x_8 = x_93;
goto block_42;
}
}
else
{
lean_object* x_99; uint8_t x_100; 
lean_dec(x_4);
x_99 = lean_ctor_get(x_83, 1);
lean_inc(x_99);
lean_dec(x_83);
x_100 = !lean_is_exclusive(x_84);
if (x_100 == 0)
{
x_7 = x_84;
x_8 = x_99;
goto block_42;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_84, 0);
x_102 = lean_ctor_get(x_84, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_84);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_7 = x_103;
x_8 = x_99;
goto block_42;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_ctor_get(x_44, 0);
lean_inc(x_104);
lean_dec(x_44);
x_105 = lean_ctor_get(x_1, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
lean_dec(x_1);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 2);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l_Lake_PackageEntry_materialize(x_104, x_105, x_107, x_109, x_5, x_6);
lean_dec(x_105);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_110);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_110, 0);
lean_dec(x_113);
x_114 = !lean_is_exclusive(x_111);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_111, 0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_4);
lean_ctor_set(x_111, 0, x_116);
return x_110;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_111, 0);
x_118 = lean_ctor_get(x_111, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_111);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_4);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_110, 0, x_120);
return x_110;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_ctor_get(x_110, 1);
lean_inc(x_121);
lean_dec(x_110);
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_111, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_124 = x_111;
} else {
 lean_dec_ref(x_111);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_4);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_121);
return x_127;
}
}
else
{
uint8_t x_128; 
lean_dec(x_4);
x_128 = !lean_is_exclusive(x_110);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_110, 0);
lean_dec(x_129);
x_130 = !lean_is_exclusive(x_111);
if (x_130 == 0)
{
return x_110;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_111, 0);
x_132 = lean_ctor_get(x_111, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_111);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_110, 0, x_133);
return x_110;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_110, 1);
lean_inc(x_134);
lean_dec(x_110);
x_135 = lean_ctor_get(x_111, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_111, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_137 = x_111;
} else {
 lean_dec_ref(x_111);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
return x_139;
}
}
}
block_42:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_13, x_15, x_14);
lean_ctor_set(x_10, 1, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_19, x_21, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_7, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_29 = x_25;
} else {
 lean_dec_ref(x_25);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_27, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_28, x_31, x_30);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_8);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_7);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_8);
return x_41;
}
}
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package '", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' was required as '", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 1;
x_10 = l_Lake_loadDepPackage___closed__1;
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_Name_toString(x_2, x_9, x_10);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_Name_toString(x_3, x_9, x_10);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4;
x_23 = lean_string_append(x_21, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_array_get_size(x_5);
x_27 = lean_array_push(x_5, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' was downloaded incorrectly; you will need to manually delete '", 64, 64);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': ", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_9, 4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1(x_1, x_2, x_3, x_11, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = l_IO_FS_removeDirAll(x_13, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1(x_1, x_2, x_3, x_16, x_7, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = 1;
x_21 = l_Lake_loadDepPackage___closed__1;
lean_inc(x_3);
x_22 = l_Lean_Name_toString(x_3, x_20, x_21);
x_23 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_13);
x_28 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_io_error_to_string(x_18);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_push(x_7, x_35);
x_37 = lean_box(0);
x_38 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1(x_1, x_2, x_3, x_37, x_36, x_19);
return x_38;
}
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("std", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" @ ", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_name_eq(x_8, x_9);
x_11 = l_instDecidableNot___rarg(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2;
x_16 = lean_name_eq(x_9, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2(x_1, x_8, x_9, x_3, x_4, x_17, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = l_Lake_loadDepPackage___closed__1;
lean_inc(x_8);
x_23 = l_Lean_Name_toString(x_8, x_21, x_22);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
x_24 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_25 = l_Lake_stdMismatchError(x_23, x_24);
lean_dec(x_23);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_push(x_5, x_27);
x_29 = lean_box(0);
x_30 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2(x_1, x_8, x_9, x_3, x_4, x_29, x_28, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_20, 2);
lean_inc(x_31);
lean_dec(x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_33 = l_Lake_stdMismatchError(x_23, x_32);
lean_dec(x_23);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_push(x_5, x_35);
x_37 = lean_box(0);
x_38 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2(x_1, x_8, x_9, x_3, x_4, x_37, x_36, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = l_String_quote(x_40);
lean_dec(x_40);
lean_ctor_set_tag(x_31, 3);
lean_ctor_set(x_31, 0, x_41);
x_42 = l_Std_Format_defWidth;
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_format_pretty(x_31, x_42, x_43, x_43);
x_45 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = l_Lake_stdMismatchError(x_23, x_48);
lean_dec(x_48);
lean_dec(x_23);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_push(x_5, x_51);
x_53 = lean_box(0);
x_54 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2(x_1, x_8, x_9, x_3, x_4, x_53, x_52, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_31, 0);
lean_inc(x_55);
lean_dec(x_31);
x_56 = l_String_quote(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Std_Format_defWidth;
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_format_pretty(x_57, x_58, x_59, x_59);
x_61 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3;
x_62 = lean_string_append(x_61, x_60);
lean_dec(x_60);
x_63 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_64 = lean_string_append(x_62, x_63);
x_65 = l_Lake_stdMismatchError(x_23, x_64);
lean_dec(x_64);
lean_dec(x_23);
x_66 = 3;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_array_push(x_5, x_67);
x_69 = lean_box(0);
x_70 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2(x_1, x_8, x_9, x_3, x_4, x_69, x_68, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_70;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
static uint32_t _init_l_Lake_restartCode() {
_start:
{
uint32_t x_1; 
x_1 = 4;
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n  ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    from ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_12 = lean_string_append(x_11, x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lake_ToolchainVer_toString(x_10);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = 1;
x_20 = l_Lake_loadDepPackage___closed__1;
x_21 = l_Lean_Name_toString(x_9, x_19, x_20);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_11);
x_2 = x_8;
x_4 = x_23;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_uget(x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_inc(x_1);
x_11 = l_System_FilePath_join(x_1, x_10);
lean_dec(x_10);
x_12 = l_Lake_toolchainFileName;
x_13 = l_System_FilePath_join(x_11, x_12);
x_14 = l_Lake_ToolchainVer_ofFile_x3f(x_13, x_7);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_5, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_9, 2);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_5, 0, x_29);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
x_7 = x_26;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_15);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_34);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
x_7 = x_26;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
lean_dec(x_5);
x_39 = lean_ctor_get(x_9, 2);
lean_inc(x_39);
lean_dec(x_9);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_dec(x_14);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_42 = x_20;
} else {
 lean_dec_ref(x_20);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_15);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_3, x_46);
x_3 = x_47;
x_5 = x_45;
x_7 = x_40;
goto _start;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_14, 1);
x_51 = lean_ctor_get(x_14, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_15, 0);
lean_inc(x_52);
lean_dec(x_15);
x_53 = !lean_is_exclusive(x_5);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_5, 0);
x_55 = lean_ctor_get(x_5, 1);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_20);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_20, 1);
x_58 = lean_ctor_get(x_20, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_21);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_21, 0);
lean_inc(x_60);
lean_inc(x_52);
x_61 = l_Lake_ToolchainVer_decLe(x_52, x_60);
if (x_61 == 0)
{
uint8_t x_62; 
lean_inc(x_52);
lean_inc(x_60);
x_62 = l_Lake_ToolchainVer_decLt(x_60, x_52);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; 
x_63 = lean_ctor_get(x_9, 2);
lean_inc(x_63);
lean_dec(x_9);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
lean_ctor_set(x_20, 1, x_52);
lean_ctor_set(x_20, 0, x_64);
x_65 = lean_array_push(x_57, x_20);
lean_ctor_set(x_5, 1, x_65);
lean_ctor_set(x_5, 0, x_21);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_54);
x_66 = 1;
x_67 = lean_usize_add(x_3, x_66);
x_3 = x_67;
x_5 = x_14;
x_7 = x_50;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; 
lean_dec(x_60);
lean_dec(x_54);
lean_free_object(x_14);
x_69 = lean_ctor_get(x_9, 2);
lean_inc(x_69);
lean_dec(x_9);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
lean_ctor_set(x_21, 0, x_52);
lean_ctor_set(x_5, 0, x_70);
x_71 = 1;
x_72 = lean_usize_add(x_3, x_71);
x_3 = x_72;
x_7 = x_50;
goto _start;
}
}
else
{
size_t x_74; size_t x_75; 
lean_dec(x_52);
lean_free_object(x_14);
lean_dec(x_9);
x_74 = 1;
x_75 = lean_usize_add(x_3, x_74);
x_3 = x_75;
x_7 = x_50;
goto _start;
}
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_21, 0);
lean_inc(x_77);
lean_dec(x_21);
lean_inc(x_77);
lean_inc(x_52);
x_78 = l_Lake_ToolchainVer_decLe(x_52, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
lean_inc(x_52);
lean_inc(x_77);
x_79 = l_Lake_ToolchainVer_decLt(x_77, x_52);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_77);
x_81 = lean_ctor_get(x_9, 2);
lean_inc(x_81);
lean_dec(x_9);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
lean_ctor_set(x_20, 1, x_52);
lean_ctor_set(x_20, 0, x_82);
x_83 = lean_array_push(x_57, x_20);
lean_ctor_set(x_5, 1, x_83);
lean_ctor_set(x_5, 0, x_80);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_54);
x_84 = 1;
x_85 = lean_usize_add(x_3, x_84);
x_3 = x_85;
x_5 = x_14;
x_7 = x_50;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; 
lean_dec(x_77);
lean_dec(x_54);
lean_free_object(x_14);
x_87 = lean_ctor_get(x_9, 2);
lean_inc(x_87);
lean_dec(x_9);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_52);
lean_ctor_set(x_20, 0, x_89);
lean_ctor_set(x_5, 0, x_88);
x_90 = 1;
x_91 = lean_usize_add(x_3, x_90);
x_3 = x_91;
x_7 = x_50;
goto _start;
}
}
else
{
lean_object* x_93; size_t x_94; size_t x_95; 
lean_dec(x_52);
lean_free_object(x_14);
lean_dec(x_9);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_77);
lean_ctor_set(x_20, 0, x_93);
x_94 = 1;
x_95 = lean_usize_add(x_3, x_94);
x_3 = x_95;
x_7 = x_50;
goto _start;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_20, 1);
lean_inc(x_97);
lean_dec(x_20);
x_98 = lean_ctor_get(x_21, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_99 = x_21;
} else {
 lean_dec_ref(x_21);
 x_99 = lean_box(0);
}
lean_inc(x_98);
lean_inc(x_52);
x_100 = l_Lake_ToolchainVer_decLe(x_52, x_98);
if (x_100 == 0)
{
uint8_t x_101; 
lean_inc(x_52);
lean_inc(x_98);
x_101 = l_Lake_ToolchainVer_decLt(x_98, x_52);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; size_t x_108; 
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_98);
x_103 = lean_ctor_get(x_9, 2);
lean_inc(x_103);
lean_dec(x_9);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_52);
x_106 = lean_array_push(x_97, x_105);
lean_ctor_set(x_5, 1, x_106);
lean_ctor_set(x_5, 0, x_102);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_54);
x_107 = 1;
x_108 = lean_usize_add(x_3, x_107);
x_3 = x_108;
x_5 = x_14;
x_7 = x_50;
goto _start;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; 
lean_dec(x_98);
lean_dec(x_54);
lean_free_object(x_14);
x_110 = lean_ctor_get(x_9, 2);
lean_inc(x_110);
lean_dec(x_9);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
if (lean_is_scalar(x_99)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_99;
}
lean_ctor_set(x_112, 0, x_52);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_97);
lean_ctor_set(x_5, 1, x_113);
lean_ctor_set(x_5, 0, x_111);
x_114 = 1;
x_115 = lean_usize_add(x_3, x_114);
x_3 = x_115;
x_7 = x_50;
goto _start;
}
}
else
{
lean_object* x_117; lean_object* x_118; size_t x_119; size_t x_120; 
lean_dec(x_52);
lean_free_object(x_14);
lean_dec(x_9);
if (lean_is_scalar(x_99)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_99;
}
lean_ctor_set(x_117, 0, x_98);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_97);
lean_ctor_set(x_5, 1, x_118);
x_119 = 1;
x_120 = lean_usize_add(x_3, x_119);
x_3 = x_120;
x_7 = x_50;
goto _start;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_5, 0);
lean_inc(x_122);
lean_dec(x_5);
x_123 = lean_ctor_get(x_20, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_124 = x_20;
} else {
 lean_dec_ref(x_20);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_21, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_126 = x_21;
} else {
 lean_dec_ref(x_21);
 x_126 = lean_box(0);
}
lean_inc(x_125);
lean_inc(x_52);
x_127 = l_Lake_ToolchainVer_decLe(x_52, x_125);
if (x_127 == 0)
{
uint8_t x_128; 
lean_inc(x_52);
lean_inc(x_125);
x_128 = l_Lake_ToolchainVer_decLt(x_125, x_52);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; size_t x_135; size_t x_136; 
if (lean_is_scalar(x_126)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_126;
}
lean_ctor_set(x_129, 0, x_125);
x_130 = lean_ctor_get(x_9, 2);
lean_inc(x_130);
lean_dec(x_9);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec(x_130);
if (lean_is_scalar(x_124)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_124;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_52);
x_133 = lean_array_push(x_123, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_14, 1, x_134);
lean_ctor_set(x_14, 0, x_122);
x_135 = 1;
x_136 = lean_usize_add(x_3, x_135);
x_3 = x_136;
x_5 = x_14;
x_7 = x_50;
goto _start;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; size_t x_143; size_t x_144; 
lean_dec(x_125);
lean_dec(x_122);
lean_free_object(x_14);
x_138 = lean_ctor_get(x_9, 2);
lean_inc(x_138);
lean_dec(x_9);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
if (lean_is_scalar(x_126)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_126;
}
lean_ctor_set(x_140, 0, x_52);
if (lean_is_scalar(x_124)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_124;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_123);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = 1;
x_144 = lean_usize_add(x_3, x_143);
x_3 = x_144;
x_5 = x_142;
x_7 = x_50;
goto _start;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; size_t x_149; size_t x_150; 
lean_dec(x_52);
lean_free_object(x_14);
lean_dec(x_9);
if (lean_is_scalar(x_126)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_126;
}
lean_ctor_set(x_146, 0, x_125);
if (lean_is_scalar(x_124)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_124;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_123);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_122);
lean_ctor_set(x_148, 1, x_147);
x_149 = 1;
x_150 = lean_usize_add(x_3, x_149);
x_3 = x_150;
x_5 = x_148;
x_7 = x_50;
goto _start;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_152 = lean_ctor_get(x_14, 1);
lean_inc(x_152);
lean_dec(x_14);
x_153 = lean_ctor_get(x_15, 0);
lean_inc(x_153);
lean_dec(x_15);
x_154 = lean_ctor_get(x_5, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_155 = x_5;
} else {
 lean_dec_ref(x_5);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_20, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_157 = x_20;
} else {
 lean_dec_ref(x_20);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_21, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_159 = x_21;
} else {
 lean_dec_ref(x_21);
 x_159 = lean_box(0);
}
lean_inc(x_158);
lean_inc(x_153);
x_160 = l_Lake_ToolchainVer_decLe(x_153, x_158);
if (x_160 == 0)
{
uint8_t x_161; 
lean_inc(x_153);
lean_inc(x_158);
x_161 = l_Lake_ToolchainVer_decLt(x_158, x_153);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; 
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_158);
x_163 = lean_ctor_get(x_9, 2);
lean_inc(x_163);
lean_dec(x_9);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec(x_163);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_153);
x_166 = lean_array_push(x_156, x_165);
if (lean_is_scalar(x_155)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_155;
}
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_154);
lean_ctor_set(x_168, 1, x_167);
x_169 = 1;
x_170 = lean_usize_add(x_3, x_169);
x_3 = x_170;
x_5 = x_168;
x_7 = x_152;
goto _start;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; size_t x_177; size_t x_178; 
lean_dec(x_158);
lean_dec(x_154);
x_172 = lean_ctor_get(x_9, 2);
lean_inc(x_172);
lean_dec(x_9);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec(x_172);
if (lean_is_scalar(x_159)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_159;
}
lean_ctor_set(x_174, 0, x_153);
if (lean_is_scalar(x_157)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_157;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_156);
if (lean_is_scalar(x_155)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_155;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
x_177 = 1;
x_178 = lean_usize_add(x_3, x_177);
x_3 = x_178;
x_5 = x_176;
x_7 = x_152;
goto _start;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; size_t x_183; size_t x_184; 
lean_dec(x_153);
lean_dec(x_9);
if (lean_is_scalar(x_159)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_159;
}
lean_ctor_set(x_180, 0, x_158);
if (lean_is_scalar(x_157)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_157;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_156);
if (lean_is_scalar(x_155)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_155;
}
lean_ctor_set(x_182, 0, x_154);
lean_ctor_set(x_182, 1, x_181);
x_183 = 1;
x_184 = lean_usize_add(x_3, x_183);
x_3 = x_184;
x_5 = x_182;
x_7 = x_152;
goto _start;
}
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_186 = lean_ctor_get(x_14, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_14, 1);
lean_inc(x_187);
lean_dec(x_14);
x_188 = lean_io_error_to_string(x_186);
x_189 = 3;
x_190 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set_uint8(x_190, sizeof(void*)*1, x_189);
x_191 = lean_apply_2(x_6, x_190, x_187);
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_191, 0);
lean_dec(x_193);
x_194 = lean_box(0);
lean_ctor_set_tag(x_191, 1);
lean_ctor_set(x_191, 0, x_194);
return x_191;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_dec(x_191);
x_196 = lean_box(0);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
else
{
lean_object* x_198; 
lean_dec(x_6);
lean_dec(x_1);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_5);
lean_ctor_set(x_198, 1, x_7);
return x_198;
}
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("updating toolchain to '", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot auto-restart; you will need to manually restart Lake", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_Workspace_updateToolchain___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static uint8_t _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__4() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = l_Lake_restartCode;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no Elan detected; you will need to manually restart Lake", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_Workspace_updateToolchain___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("restarting Lake via Elan", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_Workspace_updateToolchain___lambda__1___closed__7;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__9() {
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
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Workspace_updateToolchain___lambda__1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--install", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("run", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lake_ToolchainVer_toString(x_1);
x_8 = l_Lake_Workspace_updateToolchain___lambda__1___closed__1;
x_9 = lean_string_append(x_8, x_7);
x_10 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4;
x_11 = lean_string_append(x_9, x_10);
x_12 = 1;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
lean_inc(x_5);
x_14 = lean_apply_2(x_5, x_13, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_IO_FS_writeFile(x_2, x_7, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_3, 2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_free_object(x_14);
lean_dec(x_7);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lake_Workspace_updateToolchain___lambda__1___closed__3;
lean_inc(x_5);
x_22 = lean_apply_2(x_5, x_21, x_20);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lake_Workspace_updateToolchain___lambda__1___closed__4;
x_25 = lean_io_exit(x_24, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_io_error_to_string(x_30);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_apply_2(x_5, x_34, x_31);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_3, 1);
x_43 = lean_ctor_get(x_42, 2);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
lean_free_object(x_14);
lean_dec(x_7);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_dec(x_18);
x_45 = l_Lake_Workspace_updateToolchain___lambda__1___closed__6;
lean_inc(x_5);
x_46 = lean_apply_2(x_5, x_45, x_44);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lake_Workspace_updateToolchain___lambda__1___closed__4;
x_49 = lean_io_exit(x_48, x_47);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_io_error_to_string(x_54);
x_57 = 3;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = lean_apply_2(x_5, x_58, x_55);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_18, 1);
x_68 = lean_ctor_get(x_18, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_19, 0);
x_70 = lean_ctor_get(x_43, 0);
x_71 = l_Lake_Workspace_updateToolchain___lambda__1___closed__8;
lean_inc(x_5);
x_72 = lean_apply_2(x_5, x_71, x_67);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_72, 1);
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_70, 1);
x_77 = l_Lake_Workspace_updateToolchain___lambda__1___closed__11;
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_77);
lean_ctor_set(x_72, 0, x_7);
x_78 = l_Lake_Workspace_updateToolchain___lambda__1___closed__12;
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 1, x_72);
lean_ctor_set(x_18, 0, x_78);
x_79 = l_Lake_Workspace_updateToolchain___lambda__1___closed__13;
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_79);
x_80 = lean_array_mk(x_14);
x_81 = l_Array_append___rarg(x_80, x_69);
x_82 = lean_box(0);
x_83 = l_Lake_Workspace_updateToolchain___lambda__1___closed__9;
x_84 = l_Lake_Env_noToolchainVars;
x_85 = 0;
lean_inc(x_76);
x_86 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_76);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set(x_86, 4, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*5, x_85);
x_87 = lean_io_process_spawn(x_86, x_74);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_io_process_child_wait(x_83, x_88, x_89);
lean_dec(x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; uint32_t x_93; uint8_t x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unbox_uint32(x_91);
lean_dec(x_91);
x_94 = lean_uint32_to_uint8(x_93);
x_95 = lean_io_exit(x_94, x_92);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
lean_dec(x_5);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
return x_95;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_dec(x_95);
x_102 = lean_io_error_to_string(x_100);
x_103 = 3;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_apply_2(x_5, x_104, x_101);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
lean_dec(x_107);
x_108 = lean_box(0);
lean_ctor_set_tag(x_105, 1);
lean_ctor_set(x_105, 0, x_108);
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_112 = lean_ctor_get(x_90, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_90, 1);
lean_inc(x_113);
lean_dec(x_90);
x_114 = lean_io_error_to_string(x_112);
x_115 = 3;
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = lean_apply_2(x_5, x_116, x_113);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
x_120 = lean_box(0);
lean_ctor_set_tag(x_117, 1);
lean_ctor_set(x_117, 0, x_120);
return x_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec(x_117);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_124 = lean_ctor_get(x_87, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_87, 1);
lean_inc(x_125);
lean_dec(x_87);
x_126 = lean_io_error_to_string(x_124);
x_127 = 3;
x_128 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_127);
x_129 = lean_apply_2(x_5, x_128, x_125);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 0);
lean_dec(x_131);
x_132 = lean_box(0);
lean_ctor_set_tag(x_129, 1);
lean_ctor_set(x_129, 0, x_132);
return x_129;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_dec(x_129);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_136 = lean_ctor_get(x_72, 1);
lean_inc(x_136);
lean_dec(x_72);
x_137 = lean_ctor_get(x_70, 1);
x_138 = l_Lake_Workspace_updateToolchain___lambda__1___closed__11;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_7);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lake_Workspace_updateToolchain___lambda__1___closed__12;
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 1, x_139);
lean_ctor_set(x_18, 0, x_140);
x_141 = l_Lake_Workspace_updateToolchain___lambda__1___closed__13;
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_141);
x_142 = lean_array_mk(x_14);
x_143 = l_Array_append___rarg(x_142, x_69);
x_144 = lean_box(0);
x_145 = l_Lake_Workspace_updateToolchain___lambda__1___closed__9;
x_146 = l_Lake_Env_noToolchainVars;
x_147 = 0;
lean_inc(x_137);
x_148 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_137);
lean_ctor_set(x_148, 2, x_143);
lean_ctor_set(x_148, 3, x_144);
lean_ctor_set(x_148, 4, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*5, x_147);
x_149 = lean_io_process_spawn(x_148, x_136);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_io_process_child_wait(x_145, x_150, x_151);
lean_dec(x_150);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; uint32_t x_155; uint8_t x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_unbox_uint32(x_153);
lean_dec(x_153);
x_156 = lean_uint32_to_uint8(x_155);
x_157 = lean_io_exit(x_156, x_154);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_5);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_162 = lean_ctor_get(x_157, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_dec(x_157);
x_164 = lean_io_error_to_string(x_162);
x_165 = 3;
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_165);
x_167 = lean_apply_2(x_5, x_166, x_163);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_box(0);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_169;
 lean_ctor_set_tag(x_171, 1);
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_168);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_172 = lean_ctor_get(x_152, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_152, 1);
lean_inc(x_173);
lean_dec(x_152);
x_174 = lean_io_error_to_string(x_172);
x_175 = 3;
x_176 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_175);
x_177 = lean_apply_2(x_5, x_176, x_173);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_179;
 lean_ctor_set_tag(x_181, 1);
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_182 = lean_ctor_get(x_149, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_149, 1);
lean_inc(x_183);
lean_dec(x_149);
x_184 = lean_io_error_to_string(x_182);
x_185 = 3;
x_186 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_185);
x_187 = lean_apply_2(x_5, x_186, x_183);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
x_190 = lean_box(0);
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_189;
 lean_ctor_set_tag(x_191, 1);
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_188);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; 
x_192 = lean_ctor_get(x_18, 1);
lean_inc(x_192);
lean_dec(x_18);
x_193 = lean_ctor_get(x_19, 0);
x_194 = lean_ctor_get(x_43, 0);
x_195 = l_Lake_Workspace_updateToolchain___lambda__1___closed__8;
lean_inc(x_5);
x_196 = lean_apply_2(x_5, x_195, x_192);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_194, 1);
x_200 = l_Lake_Workspace_updateToolchain___lambda__1___closed__11;
if (lean_is_scalar(x_198)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_198;
 lean_ctor_set_tag(x_201, 1);
}
lean_ctor_set(x_201, 0, x_7);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lake_Workspace_updateToolchain___lambda__1___closed__12;
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = l_Lake_Workspace_updateToolchain___lambda__1___closed__13;
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_203);
lean_ctor_set(x_14, 0, x_204);
x_205 = lean_array_mk(x_14);
x_206 = l_Array_append___rarg(x_205, x_193);
x_207 = lean_box(0);
x_208 = l_Lake_Workspace_updateToolchain___lambda__1___closed__9;
x_209 = l_Lake_Env_noToolchainVars;
x_210 = 0;
lean_inc(x_199);
x_211 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_199);
lean_ctor_set(x_211, 2, x_206);
lean_ctor_set(x_211, 3, x_207);
lean_ctor_set(x_211, 4, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*5, x_210);
x_212 = lean_io_process_spawn(x_211, x_197);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_io_process_child_wait(x_208, x_213, x_214);
lean_dec(x_213);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; uint32_t x_218; uint8_t x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_unbox_uint32(x_216);
lean_dec(x_216);
x_219 = lean_uint32_to_uint8(x_218);
x_220 = lean_io_exit(x_219, x_217);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_5);
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
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_225 = lean_ctor_get(x_220, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 1);
lean_inc(x_226);
lean_dec(x_220);
x_227 = lean_io_error_to_string(x_225);
x_228 = 3;
x_229 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*1, x_228);
x_230 = lean_apply_2(x_5, x_229, x_226);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_232 = x_230;
} else {
 lean_dec_ref(x_230);
 x_232 = lean_box(0);
}
x_233 = lean_box(0);
if (lean_is_scalar(x_232)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_232;
 lean_ctor_set_tag(x_234, 1);
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_231);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_235 = lean_ctor_get(x_215, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_215, 1);
lean_inc(x_236);
lean_dec(x_215);
x_237 = lean_io_error_to_string(x_235);
x_238 = 3;
x_239 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set_uint8(x_239, sizeof(void*)*1, x_238);
x_240 = lean_apply_2(x_5, x_239, x_236);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_242 = x_240;
} else {
 lean_dec_ref(x_240);
 x_242 = lean_box(0);
}
x_243 = lean_box(0);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_242;
 lean_ctor_set_tag(x_244, 1);
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_245 = lean_ctor_get(x_212, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_212, 1);
lean_inc(x_246);
lean_dec(x_212);
x_247 = lean_io_error_to_string(x_245);
x_248 = 3;
x_249 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*1, x_248);
x_250 = lean_apply_2(x_5, x_249, x_246);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
x_253 = lean_box(0);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_252;
 lean_ctor_set_tag(x_254, 1);
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
return x_254;
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
lean_free_object(x_14);
lean_dec(x_7);
x_255 = lean_ctor_get(x_18, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_18, 1);
lean_inc(x_256);
lean_dec(x_18);
x_257 = lean_io_error_to_string(x_255);
x_258 = 3;
x_259 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set_uint8(x_259, sizeof(void*)*1, x_258);
x_260 = lean_apply_2(x_5, x_259, x_256);
x_261 = !lean_is_exclusive(x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_260, 0);
lean_dec(x_262);
x_263 = lean_box(0);
lean_ctor_set_tag(x_260, 1);
lean_ctor_set(x_260, 0, x_263);
return x_260;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_260, 1);
lean_inc(x_264);
lean_dec(x_260);
x_265 = lean_box(0);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_ctor_get(x_14, 1);
lean_inc(x_267);
lean_dec(x_14);
x_268 = l_IO_FS_writeFile(x_2, x_7, x_267);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_3, 2);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; 
lean_dec(x_7);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = l_Lake_Workspace_updateToolchain___lambda__1___closed__3;
lean_inc(x_5);
x_272 = lean_apply_2(x_5, x_271, x_270);
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
lean_dec(x_272);
x_274 = l_Lake_Workspace_updateToolchain___lambda__1___closed__4;
x_275 = lean_io_exit(x_274, x_273);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_5);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_280 = lean_ctor_get(x_275, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_275, 1);
lean_inc(x_281);
lean_dec(x_275);
x_282 = lean_io_error_to_string(x_280);
x_283 = 3;
x_284 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_283);
x_285 = lean_apply_2(x_5, x_284, x_281);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
x_288 = lean_box(0);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_287;
 lean_ctor_set_tag(x_289, 1);
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_286);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_3, 1);
x_291 = lean_ctor_get(x_290, 2);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; 
lean_dec(x_7);
x_292 = lean_ctor_get(x_268, 1);
lean_inc(x_292);
lean_dec(x_268);
x_293 = l_Lake_Workspace_updateToolchain___lambda__1___closed__6;
lean_inc(x_5);
x_294 = lean_apply_2(x_5, x_293, x_292);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = l_Lake_Workspace_updateToolchain___lambda__1___closed__4;
x_297 = lean_io_exit(x_296, x_295);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_5);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
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
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_302 = lean_ctor_get(x_297, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_297, 1);
lean_inc(x_303);
lean_dec(x_297);
x_304 = lean_io_error_to_string(x_302);
x_305 = 3;
x_306 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set_uint8(x_306, sizeof(void*)*1, x_305);
x_307 = lean_apply_2(x_5, x_306, x_303);
x_308 = lean_ctor_get(x_307, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_309 = x_307;
} else {
 lean_dec_ref(x_307);
 x_309 = lean_box(0);
}
x_310 = lean_box(0);
if (lean_is_scalar(x_309)) {
 x_311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_311 = x_309;
 lean_ctor_set_tag(x_311, 1);
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_308);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; 
x_312 = lean_ctor_get(x_268, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_313 = x_268;
} else {
 lean_dec_ref(x_268);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_269, 0);
x_315 = lean_ctor_get(x_291, 0);
x_316 = l_Lake_Workspace_updateToolchain___lambda__1___closed__8;
lean_inc(x_5);
x_317 = lean_apply_2(x_5, x_316, x_312);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_319 = x_317;
} else {
 lean_dec_ref(x_317);
 x_319 = lean_box(0);
}
x_320 = lean_ctor_get(x_315, 1);
x_321 = l_Lake_Workspace_updateToolchain___lambda__1___closed__11;
if (lean_is_scalar(x_319)) {
 x_322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_322 = x_319;
 lean_ctor_set_tag(x_322, 1);
}
lean_ctor_set(x_322, 0, x_7);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_Lake_Workspace_updateToolchain___lambda__1___closed__12;
if (lean_is_scalar(x_313)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_313;
 lean_ctor_set_tag(x_324, 1);
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
x_325 = l_Lake_Workspace_updateToolchain___lambda__1___closed__13;
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
x_327 = lean_array_mk(x_326);
x_328 = l_Array_append___rarg(x_327, x_314);
x_329 = lean_box(0);
x_330 = l_Lake_Workspace_updateToolchain___lambda__1___closed__9;
x_331 = l_Lake_Env_noToolchainVars;
x_332 = 0;
lean_inc(x_320);
x_333 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_320);
lean_ctor_set(x_333, 2, x_328);
lean_ctor_set(x_333, 3, x_329);
lean_ctor_set(x_333, 4, x_331);
lean_ctor_set_uint8(x_333, sizeof(void*)*5, x_332);
x_334 = lean_io_process_spawn(x_333, x_318);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = lean_io_process_child_wait(x_330, x_335, x_336);
lean_dec(x_335);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; uint32_t x_340; uint8_t x_341; lean_object* x_342; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_unbox_uint32(x_338);
lean_dec(x_338);
x_341 = lean_uint32_to_uint8(x_340);
x_342 = lean_io_exit(x_341, x_339);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_5);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_345 = x_342;
} else {
 lean_dec_ref(x_342);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_347 = lean_ctor_get(x_342, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_342, 1);
lean_inc(x_348);
lean_dec(x_342);
x_349 = lean_io_error_to_string(x_347);
x_350 = 3;
x_351 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set_uint8(x_351, sizeof(void*)*1, x_350);
x_352 = lean_apply_2(x_5, x_351, x_348);
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_354 = x_352;
} else {
 lean_dec_ref(x_352);
 x_354 = lean_box(0);
}
x_355 = lean_box(0);
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_354;
 lean_ctor_set_tag(x_356, 1);
}
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_353);
return x_356;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_357 = lean_ctor_get(x_337, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_337, 1);
lean_inc(x_358);
lean_dec(x_337);
x_359 = lean_io_error_to_string(x_357);
x_360 = 3;
x_361 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*1, x_360);
x_362 = lean_apply_2(x_5, x_361, x_358);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_364 = x_362;
} else {
 lean_dec_ref(x_362);
 x_364 = lean_box(0);
}
x_365 = lean_box(0);
if (lean_is_scalar(x_364)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_364;
 lean_ctor_set_tag(x_366, 1);
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_363);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_367 = lean_ctor_get(x_334, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_334, 1);
lean_inc(x_368);
lean_dec(x_334);
x_369 = lean_io_error_to_string(x_367);
x_370 = 3;
x_371 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set_uint8(x_371, sizeof(void*)*1, x_370);
x_372 = lean_apply_2(x_5, x_371, x_368);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
x_375 = lean_box(0);
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_374;
 lean_ctor_set_tag(x_376, 1);
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_373);
return x_376;
}
}
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_7);
x_377 = lean_ctor_get(x_268, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_268, 1);
lean_inc(x_378);
lean_dec(x_268);
x_379 = lean_io_error_to_string(x_377);
x_380 = 3;
x_381 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set_uint8(x_381, sizeof(void*)*1, x_380);
x_382 = lean_apply_2(x_5, x_381, x_378);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
x_385 = lean_box(0);
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_384;
 lean_ctor_set_tag(x_386, 1);
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_383);
return x_386;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toolchain not updated; no toolchain information found", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_Workspace_updateToolchain___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toolchain not updated; already up-to-date", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_Workspace_updateToolchain___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toolchain not updated; multiple toolchain candidates:", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = l_Lake_Workspace_updateToolchain___closed__5;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_2 = l_Lake_Workspace_updateToolchain___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_updateToolchain___closed__7;
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = l_Lake_toolchainFileName;
lean_inc(x_6);
x_8 = l_System_FilePath_join(x_6, x_7);
x_9 = l_Lake_ToolchainVer_ofFile_x3f(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_93 = lean_ctor_get(x_5, 2);
lean_inc(x_93);
lean_dec(x_5);
x_94 = lean_ctor_get(x_93, 2);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_11);
lean_ctor_set(x_9, 1, x_95);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_9);
x_97 = lean_array_get_size(x_2);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_nat_dec_lt(x_98, x_97);
if (x_99 == 0)
{
lean_dec(x_97);
lean_dec(x_6);
x_13 = x_96;
x_14 = x_12;
goto block_92;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_le(x_97, x_97);
if (x_100 == 0)
{
lean_dec(x_97);
lean_dec(x_6);
x_13 = x_96;
x_14 = x_12;
goto block_92;
}
else
{
size_t x_101; size_t x_102; lean_object* x_103; 
x_101 = 0;
x_102 = lean_usize_of_nat(x_97);
lean_dec(x_97);
lean_inc(x_3);
x_103 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__2(x_6, x_2, x_101, x_102, x_96, x_3, x_12);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_13 = x_104;
x_14 = x_105;
goto block_92;
}
else
{
uint8_t x_106; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 0);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_103);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
block_92:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_array_get_size(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_1);
x_22 = l_Lake_Workspace_updateToolchain___closed__2;
x_23 = lean_apply_2(x_3, x_22, x_14);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_box(0);
x_30 = l_Lake_Workspace_updateToolchain___lambda__1(x_28, x_8, x_1, x_29, x_3, x_14);
lean_dec(x_1);
lean_dec(x_8);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_32);
lean_dec(x_11);
x_33 = l___private_Lake_Util_Version_0__Lake_decEqToolchainVer____x40_Lake_Util_Version___hyg_1809_(x_32, x_31);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Lake_Workspace_updateToolchain___lambda__1(x_31, x_8, x_1, x_34, x_3, x_14);
lean_dec(x_1);
lean_dec(x_8);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_1);
x_36 = l_Lake_Workspace_updateToolchain___closed__4;
x_37 = lean_apply_2(x_3, x_36, x_14);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_1);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_44; 
lean_dec(x_16);
x_44 = lean_nat_dec_le(x_19, x_19);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_18);
x_45 = l_Lake_Workspace_updateToolchain___closed__6;
x_46 = lean_apply_2(x_3, x_45, x_14);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_53 = l_Lake_Workspace_updateToolchain___closed__5;
x_54 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1(x_18, x_51, x_52, x_53);
lean_dec(x_18);
x_55 = 2;
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = lean_apply_2(x_3, x_56, x_14);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_62 = lean_ctor_get(x_17, 0);
lean_inc(x_62);
lean_dec(x_17);
x_63 = l_Lake_ToolchainVer_toString(x_62);
x_64 = l_Lake_Workspace_updateToolchain___closed__8;
x_65 = lean_string_append(x_64, x_63);
lean_dec(x_63);
x_66 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__2;
x_67 = lean_string_append(x_65, x_66);
x_68 = 1;
x_69 = l_Lake_loadDepPackage___closed__1;
x_70 = l_Lean_Name_toString(x_16, x_68, x_69);
x_71 = lean_string_append(x_67, x_70);
lean_dec(x_70);
x_72 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_nat_dec_le(x_19, x_19);
if (x_74 == 0)
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_19);
lean_dec(x_18);
x_75 = 2;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_apply_2(x_3, x_76, x_14);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_84 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1(x_18, x_82, x_83, x_73);
lean_dec(x_18);
x_85 = 2;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_apply_2(x_3, x_86, x_14);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
return x_87;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_110 = lean_ctor_get(x_9, 0);
x_111 = lean_ctor_get(x_9, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_9);
x_190 = lean_ctor_get(x_5, 2);
lean_inc(x_190);
lean_dec(x_5);
x_191 = lean_ctor_get(x_190, 2);
lean_inc(x_191);
lean_dec(x_190);
x_192 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_110);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_110);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_array_get_size(x_2);
x_196 = lean_unsigned_to_nat(0u);
x_197 = lean_nat_dec_lt(x_196, x_195);
if (x_197 == 0)
{
lean_dec(x_195);
lean_dec(x_6);
x_112 = x_194;
x_113 = x_111;
goto block_189;
}
else
{
uint8_t x_198; 
x_198 = lean_nat_dec_le(x_195, x_195);
if (x_198 == 0)
{
lean_dec(x_195);
lean_dec(x_6);
x_112 = x_194;
x_113 = x_111;
goto block_189;
}
else
{
size_t x_199; size_t x_200; lean_object* x_201; 
x_199 = 0;
x_200 = lean_usize_of_nat(x_195);
lean_dec(x_195);
lean_inc(x_3);
x_201 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__2(x_6, x_2, x_199, x_200, x_194, x_3, x_111);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_112 = x_202;
x_113 = x_203;
goto block_189;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_110);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_206 = x_201;
} else {
 lean_dec_ref(x_201);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
block_189:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_array_get_size(x_117);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_nat_dec_lt(x_119, x_118);
if (x_120 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_110);
lean_dec(x_8);
lean_dec(x_1);
x_121 = l_Lake_Workspace_updateToolchain___closed__2;
x_122 = lean_apply_2(x_3, x_121, x_113);
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
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
else
{
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_116, 0);
lean_inc(x_127);
lean_dec(x_116);
x_128 = lean_box(0);
x_129 = l_Lake_Workspace_updateToolchain___lambda__1(x_127, x_8, x_1, x_128, x_3, x_113);
lean_dec(x_1);
lean_dec(x_8);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_116, 0);
lean_inc(x_130);
lean_dec(x_116);
x_131 = lean_ctor_get(x_110, 0);
lean_inc(x_131);
lean_dec(x_110);
x_132 = l___private_Lake_Util_Version_0__Lake_decEqToolchainVer____x40_Lake_Util_Version___hyg_1809_(x_131, x_130);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_box(0);
x_134 = l_Lake_Workspace_updateToolchain___lambda__1(x_130, x_8, x_1, x_133, x_3, x_113);
lean_dec(x_1);
lean_dec(x_8);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_130);
lean_dec(x_8);
lean_dec(x_1);
x_135 = l_Lake_Workspace_updateToolchain___closed__4;
x_136 = lean_apply_2(x_3, x_135, x_113);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_box(0);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
}
}
}
else
{
lean_dec(x_110);
lean_dec(x_8);
lean_dec(x_1);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_141; 
lean_dec(x_115);
x_141 = lean_nat_dec_le(x_118, x_118);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_118);
lean_dec(x_117);
x_142 = l_Lake_Workspace_updateToolchain___closed__6;
x_143 = lean_apply_2(x_3, x_142, x_113);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
else
{
size_t x_148; size_t x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_148 = 0;
x_149 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_150 = l_Lake_Workspace_updateToolchain___closed__5;
x_151 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1(x_117, x_148, x_149, x_150);
lean_dec(x_117);
x_152 = 2;
x_153 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_152);
x_154 = lean_apply_2(x_3, x_153, x_113);
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
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
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
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_159 = lean_ctor_get(x_116, 0);
lean_inc(x_159);
lean_dec(x_116);
x_160 = l_Lake_ToolchainVer_toString(x_159);
x_161 = l_Lake_Workspace_updateToolchain___closed__8;
x_162 = lean_string_append(x_161, x_160);
lean_dec(x_160);
x_163 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__2;
x_164 = lean_string_append(x_162, x_163);
x_165 = 1;
x_166 = l_Lake_loadDepPackage___closed__1;
x_167 = l_Lean_Name_toString(x_115, x_165, x_166);
x_168 = lean_string_append(x_164, x_167);
lean_dec(x_167);
x_169 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_170 = lean_string_append(x_168, x_169);
x_171 = lean_nat_dec_le(x_118, x_118);
if (x_171 == 0)
{
uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_118);
lean_dec(x_117);
x_172 = 2;
x_173 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_172);
x_174 = lean_apply_2(x_3, x_173, x_113);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
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
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
else
{
size_t x_179; size_t x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_179 = 0;
x_180 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_181 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1(x_117, x_179, x_180, x_170);
lean_dec(x_117);
x_182 = 2;
x_183 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set_uint8(x_183, sizeof(void*)*1, x_182);
x_184 = lean_apply_2(x_3, x_183, x_113);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_208 = lean_ctor_get(x_9, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_9, 1);
lean_inc(x_209);
lean_dec(x_9);
x_210 = lean_io_error_to_string(x_208);
x_211 = 3;
x_212 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*1, x_211);
x_213 = lean_apply_2(x_3, x_212, x_209);
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_213, 0);
lean_dec(x_215);
x_216 = lean_box(0);
lean_ctor_set_tag(x_213, 1);
lean_ctor_set(x_213, 0, x_216);
return x_213;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_213, 1);
lean_inc(x_217);
lean_dec(x_213);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Workspace_updateToolchain___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_updateToolchain(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_182; uint8_t x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_3, 4);
lean_inc(x_182);
x_183 = 1;
lean_inc(x_4);
x_184 = l_Lake_loadDepPackage(x_4, x_182, x_1, x_183, x_5, x_7, x_8);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
lean_dec(x_184);
x_188 = !lean_is_exclusive(x_185);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_185, 0);
lean_dec(x_189);
x_190 = !lean_is_exclusive(x_186);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_186);
lean_ctor_set(x_191, 1, x_6);
lean_ctor_set(x_185, 0, x_191);
x_9 = x_185;
x_10 = x_187;
goto block_181;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_186, 0);
x_193 = lean_ctor_get(x_186, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_186);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_6);
lean_ctor_set(x_185, 0, x_195);
x_9 = x_185;
x_10 = x_187;
goto block_181;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_196 = lean_ctor_get(x_185, 1);
lean_inc(x_196);
lean_dec(x_185);
x_197 = lean_ctor_get(x_186, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_186, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_199 = x_186;
} else {
 lean_dec_ref(x_186);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_6);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_196);
x_9 = x_202;
x_10 = x_187;
goto block_181;
}
}
else
{
lean_object* x_203; uint8_t x_204; 
lean_dec(x_6);
x_203 = lean_ctor_get(x_184, 1);
lean_inc(x_203);
lean_dec(x_184);
x_204 = !lean_is_exclusive(x_185);
if (x_204 == 0)
{
x_9 = x_185;
x_10 = x_203;
goto block_181;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_185, 0);
x_206 = lean_ctor_get(x_185, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_185);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_9 = x_207;
x_10 = x_203;
goto block_181;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_208 = !lean_is_exclusive(x_184);
if (x_208 == 0)
{
return x_184;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_184, 0);
x_210 = lean_ctor_get(x_184, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_184);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
block_181:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_75; lean_object* x_76; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
x_75 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_2, x_3, x_4, x_18, x_13, x_10);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_76, 0);
lean_ctor_set(x_12, 0, x_79);
lean_ctor_set(x_76, 0, x_11);
x_20 = x_76;
x_21 = x_77;
goto block_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 0);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_76);
lean_ctor_set(x_12, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_81);
x_20 = x_82;
x_21 = x_77;
goto block_74;
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_free_object(x_12);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_15);
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
lean_dec(x_75);
x_84 = !lean_is_exclusive(x_76);
if (x_84 == 0)
{
x_20 = x_76;
x_21 = x_83;
goto block_74;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_76, 0);
x_86 = lean_ctor_get(x_76, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_76);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_20 = x_87;
x_21 = x_83;
goto block_74;
}
}
block_74:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_23, 1);
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
lean_inc(x_18);
x_29 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_18, x_25, x_24, x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_31, 1);
x_38 = lean_ctor_get(x_31, 0);
lean_dec(x_38);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_23, 1, x_37);
lean_ctor_set(x_23, 0, x_31);
lean_ctor_set(x_30, 0, x_23);
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_18);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_23, 1, x_39);
lean_ctor_set(x_23, 0, x_40);
lean_ctor_set(x_30, 0, x_23);
return x_29;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_43 = x_31;
} else {
 lean_dec_ref(x_31);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_18);
lean_ctor_set(x_44, 1, x_27);
lean_ctor_set(x_23, 1, x_42);
lean_ctor_set(x_23, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_29, 0, x_45);
return x_29;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_48 = x_30;
} else {
 lean_dec_ref(x_30);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_50 = x_31;
} else {
 lean_dec_ref(x_31);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_18);
lean_ctor_set(x_51, 1, x_27);
lean_ctor_set(x_23, 1, x_49);
lean_ctor_set(x_23, 0, x_51);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_23, 1);
lean_inc(x_54);
lean_dec(x_23);
lean_inc(x_18);
x_55 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_18, x_25, x_24, x_21);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_61 = x_56;
} else {
 lean_dec_ref(x_56);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_18);
lean_ctor_set(x_64, 1, x_54);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
if (lean_is_scalar(x_59)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_59;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_58);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_18);
x_68 = !lean_is_exclusive(x_20);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_20);
lean_ctor_set(x_69, 1, x_21);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_20, 0);
x_71 = lean_ctor_get(x_20, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_20);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_21);
return x_73;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_117; lean_object* x_118; 
x_88 = lean_ctor_get(x_12, 0);
x_89 = lean_ctor_get(x_12, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_12);
lean_inc(x_88);
x_117 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_2, x_3, x_4, x_88, x_13, x_10);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_89);
lean_ctor_set(x_11, 0, x_123);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_11);
lean_ctor_set(x_124, 1, x_121);
x_90 = x_124;
x_91 = x_119;
goto block_116;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_89);
lean_free_object(x_11);
lean_dec(x_15);
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
lean_dec(x_117);
x_126 = lean_ctor_get(x_118, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_118, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_128 = x_118;
} else {
 lean_dec_ref(x_118);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
x_90 = x_129;
x_91 = x_125;
goto block_116;
}
block_116:
{
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_97 = x_93;
} else {
 lean_dec_ref(x_93);
 x_97 = lean_box(0);
}
lean_inc(x_88);
x_98 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_88, x_95, x_94, x_91);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
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
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_106 = x_100;
} else {
 lean_dec_ref(x_100);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_88);
lean_ctor_set(x_107, 1, x_96);
if (lean_is_scalar(x_97)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_97;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
if (lean_is_scalar(x_104)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_104;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_103);
if (lean_is_scalar(x_102)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_102;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_101);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_88);
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
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_91);
return x_115;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_161; lean_object* x_162; 
x_130 = lean_ctor_get(x_11, 1);
lean_inc(x_130);
lean_dec(x_11);
x_131 = lean_ctor_get(x_12, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_12, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_133 = x_12;
} else {
 lean_dec_ref(x_12);
 x_133 = lean_box(0);
}
lean_inc(x_131);
x_161 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_2, x_3, x_4, x_131, x_13, x_10);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_166 = x_162;
} else {
 lean_dec_ref(x_162);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_133;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_132);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_130);
if (lean_is_scalar(x_166)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_166;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_165);
x_134 = x_169;
x_135 = x_163;
goto block_160;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_130);
x_170 = lean_ctor_get(x_161, 1);
lean_inc(x_170);
lean_dec(x_161);
x_171 = lean_ctor_get(x_162, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_162, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_173 = x_162;
} else {
 lean_dec_ref(x_162);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
x_134 = x_174;
x_135 = x_170;
goto block_160;
}
block_160:
{
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_141 = x_137;
} else {
 lean_dec_ref(x_137);
 x_141 = lean_box(0);
}
lean_inc(x_131);
x_142 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_131, x_139, x_138, x_135);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_146 = x_142;
} else {
 lean_dec_ref(x_142);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_148 = x_143;
} else {
 lean_dec_ref(x_143);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_144, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_150 = x_144;
} else {
 lean_dec_ref(x_144);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_131);
lean_ctor_set(x_151, 1, x_140);
if (lean_is_scalar(x_141)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_141;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
if (lean_is_scalar(x_148)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_148;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_147);
if (lean_is_scalar(x_146)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_146;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_145);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_131);
x_155 = lean_ctor_get(x_134, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_134, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_157 = x_134;
} else {
 lean_dec_ref(x_134);
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
lean_ctor_set(x_159, 1, x_135);
return x_159;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_9);
if (x_175 == 0)
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_9);
lean_ctor_set(x_176, 1, x_10);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_9, 0);
x_178 = lean_ctor_get(x_9, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_9);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_10);
return x_180;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_27; lean_object* x_28; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_4);
x_363 = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(x_4, x_2, x_3, x_5, x_362, x_7);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_ctor_get(x_364, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
lean_dec(x_364);
x_368 = lean_array_get_size(x_367);
x_369 = lean_unsigned_to_nat(0u);
x_370 = lean_nat_dec_lt(x_369, x_368);
if (x_370 == 0)
{
lean_dec(x_368);
lean_dec(x_367);
x_27 = x_366;
x_28 = x_365;
goto block_361;
}
else
{
uint8_t x_371; 
x_371 = lean_nat_dec_le(x_368, x_368);
if (x_371 == 0)
{
lean_dec(x_368);
lean_dec(x_367);
x_27 = x_366;
x_28 = x_365;
goto block_361;
}
else
{
size_t x_372; size_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_372 = 0;
x_373 = lean_usize_of_nat(x_368);
lean_dec(x_368);
x_374 = lean_box(0);
lean_inc(x_6);
x_375 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_367, x_372, x_373, x_374, x_6, x_365);
lean_dec(x_367);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
x_27 = x_366;
x_28 = x_376;
goto block_361;
}
}
}
else
{
uint8_t x_377; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_377 = !lean_is_exclusive(x_363);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_378 = lean_ctor_get(x_363, 1);
x_379 = lean_ctor_get(x_363, 0);
lean_dec(x_379);
x_380 = lean_ctor_get(x_364, 1);
lean_inc(x_380);
lean_dec(x_364);
x_381 = lean_array_get_size(x_380);
x_382 = lean_unsigned_to_nat(0u);
x_383 = lean_nat_dec_lt(x_382, x_381);
if (x_383 == 0)
{
lean_object* x_384; 
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_6);
x_384 = lean_box(0);
lean_ctor_set_tag(x_363, 1);
lean_ctor_set(x_363, 0, x_384);
return x_363;
}
else
{
uint8_t x_385; 
x_385 = lean_nat_dec_le(x_381, x_381);
if (x_385 == 0)
{
lean_object* x_386; 
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_6);
x_386 = lean_box(0);
lean_ctor_set_tag(x_363, 1);
lean_ctor_set(x_363, 0, x_386);
return x_363;
}
else
{
size_t x_387; size_t x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
lean_free_object(x_363);
x_387 = 0;
x_388 = lean_usize_of_nat(x_381);
lean_dec(x_381);
x_389 = lean_box(0);
x_390 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_380, x_387, x_388, x_389, x_6, x_378);
lean_dec(x_380);
x_391 = !lean_is_exclusive(x_390);
if (x_391 == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_390, 0);
lean_dec(x_392);
lean_ctor_set_tag(x_390, 1);
lean_ctor_set(x_390, 0, x_389);
return x_390;
}
else
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_390, 1);
lean_inc(x_393);
lean_dec(x_390);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_389);
lean_ctor_set(x_394, 1, x_393);
return x_394;
}
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_395 = lean_ctor_get(x_363, 1);
lean_inc(x_395);
lean_dec(x_363);
x_396 = lean_ctor_get(x_364, 1);
lean_inc(x_396);
lean_dec(x_364);
x_397 = lean_array_get_size(x_396);
x_398 = lean_unsigned_to_nat(0u);
x_399 = lean_nat_dec_lt(x_398, x_397);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_6);
x_400 = lean_box(0);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_395);
return x_401;
}
else
{
uint8_t x_402; 
x_402 = lean_nat_dec_le(x_397, x_397);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; 
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_6);
x_403 = lean_box(0);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_395);
return x_404;
}
else
{
size_t x_405; size_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_405 = 0;
x_406 = lean_usize_of_nat(x_397);
lean_dec(x_397);
x_407 = lean_box(0);
x_408 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_396, x_405, x_406, x_407, x_6, x_395);
lean_dec(x_396);
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_410;
 lean_ctor_set_tag(x_411, 1);
}
lean_ctor_set(x_411, 0, x_407);
lean_ctor_set(x_411, 1, x_409);
return x_411;
}
}
}
}
block_26:
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
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_8, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
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
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
}
block_361:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_79; lean_object* x_80; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
x_231 = lean_ctor_get(x_3, 4);
lean_inc(x_231);
x_232 = 1;
x_233 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_30);
x_234 = l_Lake_loadDepPackage(x_30, x_231, x_1, x_232, x_4, x_233, x_28);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = !lean_is_exclusive(x_235);
if (x_238 == 0)
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_ctor_get(x_235, 0);
lean_dec(x_239);
x_240 = !lean_is_exclusive(x_236);
if (x_240 == 0)
{
lean_ctor_set(x_27, 0, x_236);
lean_ctor_set(x_235, 0, x_27);
x_79 = x_235;
x_80 = x_237;
goto block_230;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_236, 0);
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_236);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
lean_ctor_set(x_27, 0, x_243);
lean_ctor_set(x_235, 0, x_27);
x_79 = x_235;
x_80 = x_237;
goto block_230;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_244 = lean_ctor_get(x_235, 1);
lean_inc(x_244);
lean_dec(x_235);
x_245 = lean_ctor_get(x_236, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_236, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_247 = x_236;
} else {
 lean_dec_ref(x_236);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
lean_ctor_set(x_27, 0, x_248);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_27);
lean_ctor_set(x_249, 1, x_244);
x_79 = x_249;
x_80 = x_237;
goto block_230;
}
}
else
{
lean_object* x_250; uint8_t x_251; 
lean_free_object(x_27);
lean_dec(x_31);
x_250 = lean_ctor_get(x_234, 1);
lean_inc(x_250);
lean_dec(x_234);
x_251 = !lean_is_exclusive(x_235);
if (x_251 == 0)
{
x_79 = x_235;
x_80 = x_250;
goto block_230;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_235, 0);
x_253 = lean_ctor_get(x_235, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_235);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_79 = x_254;
x_80 = x_250;
goto block_230;
}
}
block_78:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_array_get_size(x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_36);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_6);
x_8 = x_34;
x_9 = x_33;
goto block_26;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_36, x_36);
if (x_39 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_6);
x_8 = x_34;
x_9 = x_33;
goto block_26;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_42 = lean_box(0);
x_43 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_35, x_40, x_41, x_42, x_6, x_33);
lean_dec(x_35);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_8 = x_34;
x_9 = x_44;
goto block_26;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_32, 1);
x_47 = lean_ctor_get(x_32, 0);
lean_dec(x_47);
x_48 = lean_array_get_size(x_46);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_lt(x_49, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_6);
x_51 = lean_box(0);
lean_ctor_set(x_32, 1, x_33);
lean_ctor_set(x_32, 0, x_51);
return x_32;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_48, x_48);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_6);
x_53 = lean_box(0);
lean_ctor_set(x_32, 1, x_33);
lean_ctor_set(x_32, 0, x_53);
return x_32;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_free_object(x_32);
x_54 = 0;
x_55 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_56 = lean_box(0);
x_57 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_46, x_54, x_55, x_56, x_6, x_33);
lean_dec(x_46);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_32, 1);
lean_inc(x_62);
lean_dec(x_32);
x_63 = lean_array_get_size(x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_lt(x_64, x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_6);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_33);
return x_67;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_63, x_63);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_6);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_33);
return x_70;
}
else
{
size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = 0;
x_72 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_73 = lean_box(0);
x_74 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_62, x_71, x_72, x_73, x_6, x_33);
lean_dec(x_62);
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
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
 lean_ctor_set_tag(x_77, 1);
}
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
}
block_230:
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_81, 1);
x_86 = lean_ctor_get(x_81, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_132; lean_object* x_133; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
x_132 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_2, x_3, x_30, x_88, x_83, x_80);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = !lean_is_exclusive(x_133);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_133, 0);
lean_ctor_set(x_82, 0, x_136);
lean_ctor_set(x_133, 0, x_81);
x_90 = x_133;
x_91 = x_134;
goto block_131;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_133, 0);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_133);
lean_ctor_set(x_82, 0, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_81);
lean_ctor_set(x_139, 1, x_138);
x_90 = x_139;
x_91 = x_134;
goto block_131;
}
}
else
{
lean_object* x_140; uint8_t x_141; 
lean_free_object(x_82);
lean_dec(x_89);
lean_free_object(x_81);
lean_dec(x_85);
x_140 = lean_ctor_get(x_132, 1);
lean_inc(x_140);
lean_dec(x_132);
x_141 = !lean_is_exclusive(x_133);
if (x_141 == 0)
{
x_90 = x_133;
x_91 = x_140;
goto block_131;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_133, 0);
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_133);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_90 = x_144;
x_91 = x_140;
goto block_131;
}
}
block_131:
{
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_97 = lean_ctor_get(x_93, 1);
x_98 = lean_ctor_get(x_93, 0);
lean_dec(x_98);
lean_inc(x_88);
x_99 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_88, x_95, x_94, x_91);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = !lean_is_exclusive(x_100);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_100, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_101);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_101, 1);
x_107 = lean_ctor_get(x_101, 0);
lean_dec(x_107);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set(x_101, 0, x_88);
lean_ctor_set(x_93, 1, x_106);
lean_ctor_set(x_93, 0, x_101);
lean_ctor_set(x_100, 0, x_93);
x_32 = x_100;
x_33 = x_102;
goto block_78;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
lean_dec(x_101);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_88);
lean_ctor_set(x_109, 1, x_97);
lean_ctor_set(x_93, 1, x_108);
lean_ctor_set(x_93, 0, x_109);
lean_ctor_set(x_100, 0, x_93);
x_32 = x_100;
x_33 = x_102;
goto block_78;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_100, 1);
lean_inc(x_110);
lean_dec(x_100);
x_111 = lean_ctor_get(x_101, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_112 = x_101;
} else {
 lean_dec_ref(x_101);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_88);
lean_ctor_set(x_113, 1, x_97);
lean_ctor_set(x_93, 1, x_111);
lean_ctor_set(x_93, 0, x_113);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_93);
lean_ctor_set(x_114, 1, x_110);
x_32 = x_114;
x_33 = x_102;
goto block_78;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_115 = lean_ctor_get(x_93, 1);
lean_inc(x_115);
lean_dec(x_93);
lean_inc(x_88);
x_116 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_88, x_95, x_94, x_91);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
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
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_88);
lean_ctor_set(x_124, 1, x_115);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
if (lean_is_scalar(x_121)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_121;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_120);
x_32 = x_126;
x_33 = x_119;
goto block_78;
}
}
else
{
uint8_t x_127; 
lean_dec(x_88);
x_127 = !lean_is_exclusive(x_90);
if (x_127 == 0)
{
x_32 = x_90;
x_33 = x_91;
goto block_78;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_90, 0);
x_129 = lean_ctor_get(x_90, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_90);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_32 = x_130;
x_33 = x_91;
goto block_78;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_171; lean_object* x_172; 
x_145 = lean_ctor_get(x_82, 0);
x_146 = lean_ctor_get(x_82, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_82);
lean_inc(x_145);
x_171 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_2, x_3, x_30, x_145, x_83, x_80);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_176 = x_172;
} else {
 lean_dec_ref(x_172);
 x_176 = lean_box(0);
}
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_146);
lean_ctor_set(x_81, 0, x_177);
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_81);
lean_ctor_set(x_178, 1, x_175);
x_147 = x_178;
x_148 = x_173;
goto block_170;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_146);
lean_free_object(x_81);
lean_dec(x_85);
x_179 = lean_ctor_get(x_171, 1);
lean_inc(x_179);
lean_dec(x_171);
x_180 = lean_ctor_get(x_172, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_172, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_182 = x_172;
} else {
 lean_dec_ref(x_172);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
x_147 = x_183;
x_148 = x_179;
goto block_170;
}
block_170:
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_154 = x_150;
} else {
 lean_dec_ref(x_150);
 x_154 = lean_box(0);
}
lean_inc(x_145);
x_155 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_145, x_152, x_151, x_148);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_160 = x_156;
} else {
 lean_dec_ref(x_156);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_162 = x_157;
} else {
 lean_dec_ref(x_157);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_145);
lean_ctor_set(x_163, 1, x_153);
if (lean_is_scalar(x_154)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_154;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
if (lean_is_scalar(x_160)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_160;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_159);
x_32 = x_165;
x_33 = x_158;
goto block_78;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_145);
x_166 = lean_ctor_get(x_147, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_147, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_168 = x_147;
} else {
 lean_dec_ref(x_147);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
x_32 = x_169;
x_33 = x_148;
goto block_78;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_212; lean_object* x_213; 
x_184 = lean_ctor_get(x_81, 1);
lean_inc(x_184);
lean_dec(x_81);
x_185 = lean_ctor_get(x_82, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_82, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_187 = x_82;
} else {
 lean_dec_ref(x_82);
 x_187 = lean_box(0);
}
lean_inc(x_185);
x_212 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_2, x_3, x_30, x_185, x_83, x_80);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_213, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_217 = x_213;
} else {
 lean_dec_ref(x_213);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_187;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_186);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_184);
if (lean_is_scalar(x_217)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_217;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_216);
x_188 = x_220;
x_189 = x_214;
goto block_211;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_184);
x_221 = lean_ctor_get(x_212, 1);
lean_inc(x_221);
lean_dec(x_212);
x_222 = lean_ctor_get(x_213, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_213, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_224 = x_213;
} else {
 lean_dec_ref(x_213);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
x_188 = x_225;
x_189 = x_221;
goto block_211;
}
block_211:
{
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
lean_dec(x_188);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
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
lean_inc(x_185);
x_196 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_185, x_193, x_192, x_189);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_201 = x_197;
} else {
 lean_dec_ref(x_197);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_198, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_203 = x_198;
} else {
 lean_dec_ref(x_198);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_185);
lean_ctor_set(x_204, 1, x_194);
if (lean_is_scalar(x_195)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_195;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
if (lean_is_scalar(x_201)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_201;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_200);
x_32 = x_206;
x_33 = x_199;
goto block_78;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_185);
x_207 = lean_ctor_get(x_188, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_188, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_209 = x_188;
} else {
 lean_dec_ref(x_188);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
x_32 = x_210;
x_33 = x_189;
goto block_78;
}
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
x_226 = !lean_is_exclusive(x_79);
if (x_226 == 0)
{
x_32 = x_79;
x_33 = x_80;
goto block_78;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_79, 0);
x_228 = lean_ctor_get(x_79, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_79);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_32 = x_229;
x_33 = x_80;
goto block_78;
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_288; lean_object* x_289; lean_object* x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_255 = lean_ctor_get(x_27, 0);
x_256 = lean_ctor_get(x_27, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_27);
x_341 = lean_ctor_get(x_3, 4);
lean_inc(x_341);
x_342 = 1;
x_343 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_255);
x_344 = l_Lake_loadDepPackage(x_255, x_341, x_1, x_342, x_4, x_343, x_28);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_347);
lean_dec(x_344);
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_349 = x_345;
} else {
 lean_dec_ref(x_345);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_346, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_346, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_352 = x_346;
} else {
 lean_dec_ref(x_346);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_256);
if (lean_is_scalar(x_349)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_349;
}
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_348);
x_288 = x_355;
x_289 = x_347;
goto block_340;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_256);
x_356 = lean_ctor_get(x_344, 1);
lean_inc(x_356);
lean_dec(x_344);
x_357 = lean_ctor_get(x_345, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_345, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_359 = x_345;
} else {
 lean_dec_ref(x_345);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
x_288 = x_360;
x_289 = x_356;
goto block_340;
}
block_287:
{
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
lean_dec(x_257);
x_261 = lean_array_get_size(x_260);
x_262 = lean_unsigned_to_nat(0u);
x_263 = lean_nat_dec_lt(x_262, x_261);
if (x_263 == 0)
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_6);
x_8 = x_259;
x_9 = x_258;
goto block_26;
}
else
{
uint8_t x_264; 
x_264 = lean_nat_dec_le(x_261, x_261);
if (x_264 == 0)
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_6);
x_8 = x_259;
x_9 = x_258;
goto block_26;
}
else
{
size_t x_265; size_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = 0;
x_266 = lean_usize_of_nat(x_261);
lean_dec(x_261);
x_267 = lean_box(0);
x_268 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_260, x_265, x_266, x_267, x_6, x_258);
lean_dec(x_260);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_8 = x_259;
x_9 = x_269;
goto block_26;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_270 = lean_ctor_get(x_257, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_271 = x_257;
} else {
 lean_dec_ref(x_257);
 x_271 = lean_box(0);
}
x_272 = lean_array_get_size(x_270);
x_273 = lean_unsigned_to_nat(0u);
x_274 = lean_nat_dec_lt(x_273, x_272);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_272);
lean_dec(x_270);
lean_dec(x_6);
x_275 = lean_box(0);
if (lean_is_scalar(x_271)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_271;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_258);
return x_276;
}
else
{
uint8_t x_277; 
x_277 = lean_nat_dec_le(x_272, x_272);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_272);
lean_dec(x_270);
lean_dec(x_6);
x_278 = lean_box(0);
if (lean_is_scalar(x_271)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_271;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_258);
return x_279;
}
else
{
size_t x_280; size_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_271);
x_280 = 0;
x_281 = lean_usize_of_nat(x_272);
lean_dec(x_272);
x_282 = lean_box(0);
x_283 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_270, x_280, x_281, x_282, x_6, x_258);
lean_dec(x_270);
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_285 = x_283;
} else {
 lean_dec_ref(x_283);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
 lean_ctor_set_tag(x_286, 1);
}
lean_ctor_set(x_286, 0, x_282);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
}
}
block_340:
{
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_322; lean_object* x_323; 
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_288, 1);
lean_inc(x_292);
lean_dec(x_288);
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
x_295 = lean_ctor_get(x_291, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_291, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_297 = x_291;
} else {
 lean_dec_ref(x_291);
 x_297 = lean_box(0);
}
lean_inc(x_295);
x_322 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_2, x_3, x_255, x_295, x_292, x_289);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get(x_323, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_327 = x_323;
} else {
 lean_dec_ref(x_323);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_297;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_296);
if (lean_is_scalar(x_294)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_294;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_293);
if (lean_is_scalar(x_327)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_327;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_326);
x_298 = x_330;
x_299 = x_324;
goto block_321;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_294);
lean_dec(x_293);
x_331 = lean_ctor_get(x_322, 1);
lean_inc(x_331);
lean_dec(x_322);
x_332 = lean_ctor_get(x_323, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_323, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_334 = x_323;
} else {
 lean_dec_ref(x_323);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 2, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_333);
x_298 = x_335;
x_299 = x_331;
goto block_321;
}
block_321:
{
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_300 = lean_ctor_get(x_298, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_298, 1);
lean_inc(x_302);
lean_dec(x_298);
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_304 = lean_ctor_get(x_301, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_305 = x_301;
} else {
 lean_dec_ref(x_301);
 x_305 = lean_box(0);
}
lean_inc(x_295);
x_306 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_295, x_303, x_302, x_299);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_dec(x_306);
x_310 = lean_ctor_get(x_307, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_311 = x_307;
} else {
 lean_dec_ref(x_307);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_308, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_313 = x_308;
} else {
 lean_dec_ref(x_308);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_295);
lean_ctor_set(x_314, 1, x_304);
if (lean_is_scalar(x_305)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_305;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_312);
if (lean_is_scalar(x_311)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_311;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_310);
x_257 = x_316;
x_258 = x_309;
goto block_287;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_295);
x_317 = lean_ctor_get(x_298, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_298, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_319 = x_298;
} else {
 lean_dec_ref(x_298);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
x_257 = x_320;
x_258 = x_299;
goto block_287;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_255);
lean_dec(x_3);
lean_dec(x_2);
x_336 = lean_ctor_get(x_288, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_288, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_338 = x_288;
} else {
 lean_dec_ref(x_288);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_337);
x_257 = x_339;
x_258 = x_289;
goto block_287;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_37; lean_object* x_38; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_6);
x_373 = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(x_6, x_1, x_2, x_7, x_372, x_9);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; 
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_ctor_get(x_374, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_374, 1);
lean_inc(x_377);
lean_dec(x_374);
x_378 = lean_array_get_size(x_377);
x_379 = lean_unsigned_to_nat(0u);
x_380 = lean_nat_dec_lt(x_379, x_378);
if (x_380 == 0)
{
lean_dec(x_378);
lean_dec(x_377);
x_37 = x_376;
x_38 = x_375;
goto block_371;
}
else
{
uint8_t x_381; 
x_381 = lean_nat_dec_le(x_378, x_378);
if (x_381 == 0)
{
lean_dec(x_378);
lean_dec(x_377);
x_37 = x_376;
x_38 = x_375;
goto block_371;
}
else
{
size_t x_382; size_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_382 = 0;
x_383 = lean_usize_of_nat(x_378);
lean_dec(x_378);
x_384 = lean_box(0);
lean_inc(x_8);
x_385 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_377, x_382, x_383, x_384, x_8, x_375);
lean_dec(x_377);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
lean_dec(x_385);
x_37 = x_376;
x_38 = x_386;
goto block_371;
}
}
}
else
{
uint8_t x_387; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_387 = !lean_is_exclusive(x_373);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_388 = lean_ctor_get(x_373, 1);
x_389 = lean_ctor_get(x_373, 0);
lean_dec(x_389);
x_390 = lean_ctor_get(x_374, 1);
lean_inc(x_390);
lean_dec(x_374);
x_391 = lean_array_get_size(x_390);
x_392 = lean_unsigned_to_nat(0u);
x_393 = lean_nat_dec_lt(x_392, x_391);
if (x_393 == 0)
{
lean_object* x_394; 
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_8);
x_394 = lean_box(0);
lean_ctor_set_tag(x_373, 1);
lean_ctor_set(x_373, 0, x_394);
return x_373;
}
else
{
uint8_t x_395; 
x_395 = lean_nat_dec_le(x_391, x_391);
if (x_395 == 0)
{
lean_object* x_396; 
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_8);
x_396 = lean_box(0);
lean_ctor_set_tag(x_373, 1);
lean_ctor_set(x_373, 0, x_396);
return x_373;
}
else
{
size_t x_397; size_t x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
lean_free_object(x_373);
x_397 = 0;
x_398 = lean_usize_of_nat(x_391);
lean_dec(x_391);
x_399 = lean_box(0);
x_400 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_390, x_397, x_398, x_399, x_8, x_388);
lean_dec(x_390);
x_401 = !lean_is_exclusive(x_400);
if (x_401 == 0)
{
lean_object* x_402; 
x_402 = lean_ctor_get(x_400, 0);
lean_dec(x_402);
lean_ctor_set_tag(x_400, 1);
lean_ctor_set(x_400, 0, x_399);
return x_400;
}
else
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_ctor_get(x_400, 1);
lean_inc(x_403);
lean_dec(x_400);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_399);
lean_ctor_set(x_404, 1, x_403);
return x_404;
}
}
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_405 = lean_ctor_get(x_373, 1);
lean_inc(x_405);
lean_dec(x_373);
x_406 = lean_ctor_get(x_374, 1);
lean_inc(x_406);
lean_dec(x_374);
x_407 = lean_array_get_size(x_406);
x_408 = lean_unsigned_to_nat(0u);
x_409 = lean_nat_dec_lt(x_408, x_407);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
x_410 = lean_box(0);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_405);
return x_411;
}
else
{
uint8_t x_412; 
x_412 = lean_nat_dec_le(x_407, x_407);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
x_413 = lean_box(0);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_405);
return x_414;
}
else
{
size_t x_415; size_t x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_415 = 0;
x_416 = lean_usize_of_nat(x_407);
lean_dec(x_407);
x_417 = lean_box(0);
x_418 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_406, x_415, x_416, x_417, x_8, x_405);
lean_dec(x_406);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_420 = x_418;
} else {
 lean_dec_ref(x_418);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
 lean_ctor_set_tag(x_421, 1);
}
lean_ctor_set(x_421, 0, x_417);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
}
}
block_36:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lake_Workspace_addPackage(x_15, x_16);
x_18 = lean_box(0);
lean_ctor_set(x_13, 1, x_17);
lean_ctor_set(x_13, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lake_Workspace_addPackage(x_20, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_10, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
x_31 = l_Lake_Workspace_addPackage(x_28, x_29);
x_32 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
block_371:
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_89; lean_object* x_90; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 1);
x_241 = lean_ctor_get(x_2, 4);
lean_inc(x_241);
x_242 = 1;
x_243 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_40);
x_244 = l_Lake_loadDepPackage(x_40, x_241, x_3, x_242, x_6, x_243, x_38);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
lean_dec(x_244);
x_248 = !lean_is_exclusive(x_245);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; 
x_249 = lean_ctor_get(x_245, 0);
lean_dec(x_249);
x_250 = !lean_is_exclusive(x_246);
if (x_250 == 0)
{
lean_ctor_set(x_37, 0, x_246);
lean_ctor_set(x_245, 0, x_37);
x_89 = x_245;
x_90 = x_247;
goto block_240;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_246, 0);
x_252 = lean_ctor_get(x_246, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_246);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set(x_37, 0, x_253);
lean_ctor_set(x_245, 0, x_37);
x_89 = x_245;
x_90 = x_247;
goto block_240;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_245, 1);
lean_inc(x_254);
lean_dec(x_245);
x_255 = lean_ctor_get(x_246, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_246, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_257 = x_246;
} else {
 lean_dec_ref(x_246);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
lean_ctor_set(x_37, 0, x_258);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_37);
lean_ctor_set(x_259, 1, x_254);
x_89 = x_259;
x_90 = x_247;
goto block_240;
}
}
else
{
lean_object* x_260; uint8_t x_261; 
lean_free_object(x_37);
lean_dec(x_41);
x_260 = lean_ctor_get(x_244, 1);
lean_inc(x_260);
lean_dec(x_244);
x_261 = !lean_is_exclusive(x_245);
if (x_261 == 0)
{
x_89 = x_245;
x_90 = x_260;
goto block_240;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_245, 0);
x_263 = lean_ctor_get(x_245, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_245);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_89 = x_264;
x_90 = x_260;
goto block_240;
}
}
block_88:
{
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_array_get_size(x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_lt(x_47, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_8);
x_10 = x_44;
x_11 = x_43;
goto block_36;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_46, x_46);
if (x_49 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_8);
x_10 = x_44;
x_11 = x_43;
goto block_36;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_52 = lean_box(0);
x_53 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_45, x_50, x_51, x_52, x_8, x_43);
lean_dec(x_45);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_10 = x_44;
x_11 = x_54;
goto block_36;
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_42, 1);
x_57 = lean_ctor_get(x_42, 0);
lean_dec(x_57);
x_58 = lean_array_get_size(x_56);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_lt(x_59, x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_8);
x_61 = lean_box(0);
lean_ctor_set(x_42, 1, x_43);
lean_ctor_set(x_42, 0, x_61);
return x_42;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_58, x_58);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_8);
x_63 = lean_box(0);
lean_ctor_set(x_42, 1, x_43);
lean_ctor_set(x_42, 0, x_63);
return x_42;
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_free_object(x_42);
x_64 = 0;
x_65 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_66 = lean_box(0);
x_67 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_56, x_64, x_65, x_66, x_8, x_43);
lean_dec(x_56);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_42, 1);
lean_inc(x_72);
lean_dec(x_42);
x_73 = lean_array_get_size(x_72);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_lt(x_74, x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_8);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_43);
return x_77;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_73, x_73);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_8);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_43);
return x_80;
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_83 = lean_box(0);
x_84 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_72, x_81, x_82, x_83, x_8, x_43);
lean_dec(x_72);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
 lean_ctor_set_tag(x_87, 1);
}
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
}
block_240:
{
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_dec(x_89);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_91, 1);
x_96 = lean_ctor_get(x_91, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_92);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_142; lean_object* x_143; 
x_98 = lean_ctor_get(x_92, 0);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
x_142 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_1, x_2, x_40, x_98, x_93, x_90);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_143, 0);
lean_ctor_set(x_92, 0, x_146);
lean_ctor_set(x_143, 0, x_91);
x_100 = x_143;
x_101 = x_144;
goto block_141;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_143, 0);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_143);
lean_ctor_set(x_92, 0, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_91);
lean_ctor_set(x_149, 1, x_148);
x_100 = x_149;
x_101 = x_144;
goto block_141;
}
}
else
{
lean_object* x_150; uint8_t x_151; 
lean_free_object(x_92);
lean_dec(x_99);
lean_free_object(x_91);
lean_dec(x_95);
x_150 = lean_ctor_get(x_142, 1);
lean_inc(x_150);
lean_dec(x_142);
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
x_100 = x_143;
x_101 = x_150;
goto block_141;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_143, 0);
x_153 = lean_ctor_get(x_143, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_143);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_100 = x_154;
x_101 = x_150;
goto block_141;
}
}
block_141:
{
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_dec(x_100);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_107 = lean_ctor_get(x_103, 1);
x_108 = lean_ctor_get(x_103, 0);
lean_dec(x_108);
lean_inc(x_98);
x_109 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_98, x_105, x_104, x_101);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_111);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_111, 1);
x_117 = lean_ctor_get(x_111, 0);
lean_dec(x_117);
lean_ctor_set(x_111, 1, x_107);
lean_ctor_set(x_111, 0, x_98);
lean_ctor_set(x_103, 1, x_116);
lean_ctor_set(x_103, 0, x_111);
lean_ctor_set(x_110, 0, x_103);
x_42 = x_110;
x_43 = x_112;
goto block_88;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_111, 1);
lean_inc(x_118);
lean_dec(x_111);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_98);
lean_ctor_set(x_119, 1, x_107);
lean_ctor_set(x_103, 1, x_118);
lean_ctor_set(x_103, 0, x_119);
lean_ctor_set(x_110, 0, x_103);
x_42 = x_110;
x_43 = x_112;
goto block_88;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_110, 1);
lean_inc(x_120);
lean_dec(x_110);
x_121 = lean_ctor_get(x_111, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_122 = x_111;
} else {
 lean_dec_ref(x_111);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_98);
lean_ctor_set(x_123, 1, x_107);
lean_ctor_set(x_103, 1, x_121);
lean_ctor_set(x_103, 0, x_123);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_103);
lean_ctor_set(x_124, 1, x_120);
x_42 = x_124;
x_43 = x_112;
goto block_88;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_125 = lean_ctor_get(x_103, 1);
lean_inc(x_125);
lean_dec(x_103);
lean_inc(x_98);
x_126 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_98, x_105, x_104, x_101);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
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
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_98);
lean_ctor_set(x_134, 1, x_125);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
if (lean_is_scalar(x_131)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_131;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_130);
x_42 = x_136;
x_43 = x_129;
goto block_88;
}
}
else
{
uint8_t x_137; 
lean_dec(x_98);
x_137 = !lean_is_exclusive(x_100);
if (x_137 == 0)
{
x_42 = x_100;
x_43 = x_101;
goto block_88;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_100, 0);
x_139 = lean_ctor_get(x_100, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_100);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_42 = x_140;
x_43 = x_101;
goto block_88;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_181; lean_object* x_182; 
x_155 = lean_ctor_get(x_92, 0);
x_156 = lean_ctor_get(x_92, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_92);
lean_inc(x_155);
x_181 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_1, x_2, x_40, x_155, x_93, x_90);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_186 = x_182;
} else {
 lean_dec_ref(x_182);
 x_186 = lean_box(0);
}
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_156);
lean_ctor_set(x_91, 0, x_187);
if (lean_is_scalar(x_186)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_186;
}
lean_ctor_set(x_188, 0, x_91);
lean_ctor_set(x_188, 1, x_185);
x_157 = x_188;
x_158 = x_183;
goto block_180;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_156);
lean_free_object(x_91);
lean_dec(x_95);
x_189 = lean_ctor_get(x_181, 1);
lean_inc(x_189);
lean_dec(x_181);
x_190 = lean_ctor_get(x_182, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_192 = x_182;
} else {
 lean_dec_ref(x_182);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
x_157 = x_193;
x_158 = x_189;
goto block_180;
}
block_180:
{
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
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
lean_inc(x_155);
x_165 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_155, x_162, x_161, x_158);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_170 = x_166;
} else {
 lean_dec_ref(x_166);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_172 = x_167;
} else {
 lean_dec_ref(x_167);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_155);
lean_ctor_set(x_173, 1, x_163);
if (lean_is_scalar(x_164)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_164;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
if (lean_is_scalar(x_170)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_170;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_169);
x_42 = x_175;
x_43 = x_168;
goto block_88;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_155);
x_176 = lean_ctor_get(x_157, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_157, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_178 = x_157;
} else {
 lean_dec_ref(x_157);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
x_42 = x_179;
x_43 = x_158;
goto block_88;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_222; lean_object* x_223; 
x_194 = lean_ctor_get(x_91, 1);
lean_inc(x_194);
lean_dec(x_91);
x_195 = lean_ctor_get(x_92, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_92, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_197 = x_92;
} else {
 lean_dec_ref(x_92);
 x_197 = lean_box(0);
}
lean_inc(x_195);
x_222 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_1, x_2, x_40, x_195, x_93, x_90);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_ctor_get(x_223, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_227 = x_223;
} else {
 lean_dec_ref(x_223);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_197;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_196);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_194);
if (lean_is_scalar(x_227)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_227;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_226);
x_198 = x_230;
x_199 = x_224;
goto block_221;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_194);
x_231 = lean_ctor_get(x_222, 1);
lean_inc(x_231);
lean_dec(x_222);
x_232 = lean_ctor_get(x_223, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_223, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_234 = x_223;
} else {
 lean_dec_ref(x_223);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
x_198 = x_235;
x_199 = x_231;
goto block_221;
}
block_221:
{
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_198, 1);
lean_inc(x_202);
lean_dec(x_198);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_205 = x_201;
} else {
 lean_dec_ref(x_201);
 x_205 = lean_box(0);
}
lean_inc(x_195);
x_206 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_195, x_203, x_202, x_199);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_211 = x_207;
} else {
 lean_dec_ref(x_207);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_208, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_213 = x_208;
} else {
 lean_dec_ref(x_208);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_195);
lean_ctor_set(x_214, 1, x_204);
if (lean_is_scalar(x_205)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_205;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
if (lean_is_scalar(x_211)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_211;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_210);
x_42 = x_216;
x_43 = x_209;
goto block_88;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_195);
x_217 = lean_ctor_get(x_198, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_198, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_219 = x_198;
} else {
 lean_dec_ref(x_198);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
x_42 = x_220;
x_43 = x_199;
goto block_88;
}
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_40);
lean_dec(x_2);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_89);
if (x_236 == 0)
{
x_42 = x_89;
x_43 = x_90;
goto block_88;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_89, 0);
x_238 = lean_ctor_get(x_89, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_89);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_42 = x_239;
x_43 = x_90;
goto block_88;
}
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_298; lean_object* x_299; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_265 = lean_ctor_get(x_37, 0);
x_266 = lean_ctor_get(x_37, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_37);
x_351 = lean_ctor_get(x_2, 4);
lean_inc(x_351);
x_352 = 1;
x_353 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_265);
x_354 = l_Lake_loadDepPackage(x_265, x_351, x_3, x_352, x_6, x_353, x_38);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
lean_dec(x_354);
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_359 = x_355;
} else {
 lean_dec_ref(x_355);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_356, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_356, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_362 = x_356;
} else {
 lean_dec_ref(x_356);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_266);
if (lean_is_scalar(x_359)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_359;
}
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_358);
x_298 = x_365;
x_299 = x_357;
goto block_350;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_266);
x_366 = lean_ctor_get(x_354, 1);
lean_inc(x_366);
lean_dec(x_354);
x_367 = lean_ctor_get(x_355, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_355, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_369 = x_355;
} else {
 lean_dec_ref(x_355);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
x_298 = x_370;
x_299 = x_366;
goto block_350;
}
block_297:
{
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
lean_dec(x_267);
x_271 = lean_array_get_size(x_270);
x_272 = lean_unsigned_to_nat(0u);
x_273 = lean_nat_dec_lt(x_272, x_271);
if (x_273 == 0)
{
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_8);
x_10 = x_269;
x_11 = x_268;
goto block_36;
}
else
{
uint8_t x_274; 
x_274 = lean_nat_dec_le(x_271, x_271);
if (x_274 == 0)
{
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_8);
x_10 = x_269;
x_11 = x_268;
goto block_36;
}
else
{
size_t x_275; size_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_275 = 0;
x_276 = lean_usize_of_nat(x_271);
lean_dec(x_271);
x_277 = lean_box(0);
x_278 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_270, x_275, x_276, x_277, x_8, x_268);
lean_dec(x_270);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_10 = x_269;
x_11 = x_279;
goto block_36;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_280 = lean_ctor_get(x_267, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_281 = x_267;
} else {
 lean_dec_ref(x_267);
 x_281 = lean_box(0);
}
x_282 = lean_array_get_size(x_280);
x_283 = lean_unsigned_to_nat(0u);
x_284 = lean_nat_dec_lt(x_283, x_282);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_282);
lean_dec(x_280);
lean_dec(x_8);
x_285 = lean_box(0);
if (lean_is_scalar(x_281)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_281;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_268);
return x_286;
}
else
{
uint8_t x_287; 
x_287 = lean_nat_dec_le(x_282, x_282);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_282);
lean_dec(x_280);
lean_dec(x_8);
x_288 = lean_box(0);
if (lean_is_scalar(x_281)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_281;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_268);
return x_289;
}
else
{
size_t x_290; size_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_281);
x_290 = 0;
x_291 = lean_usize_of_nat(x_282);
lean_dec(x_282);
x_292 = lean_box(0);
x_293 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_280, x_290, x_291, x_292, x_8, x_268);
lean_dec(x_280);
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_295 = x_293;
} else {
 lean_dec_ref(x_293);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
 lean_ctor_set_tag(x_296, 1);
}
lean_ctor_set(x_296, 0, x_292);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
}
}
block_350:
{
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_332; lean_object* x_333; 
x_300 = lean_ctor_get(x_298, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_298, 1);
lean_inc(x_302);
lean_dec(x_298);
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
x_305 = lean_ctor_get(x_301, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_301, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_307 = x_301;
} else {
 lean_dec_ref(x_301);
 x_307 = lean_box(0);
}
lean_inc(x_305);
x_332 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_1, x_2, x_265, x_305, x_302, x_299);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_333, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_337 = x_333;
} else {
 lean_dec_ref(x_333);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_338 = x_307;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_306);
if (lean_is_scalar(x_304)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_304;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_303);
if (lean_is_scalar(x_337)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_337;
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_336);
x_308 = x_340;
x_309 = x_334;
goto block_331;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_304);
lean_dec(x_303);
x_341 = lean_ctor_get(x_332, 1);
lean_inc(x_341);
lean_dec(x_332);
x_342 = lean_ctor_get(x_333, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_333, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_344 = x_333;
} else {
 lean_dec_ref(x_333);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(1, 2, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_343);
x_308 = x_345;
x_309 = x_341;
goto block_331;
}
block_331:
{
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_308, 1);
lean_inc(x_312);
lean_dec(x_308);
x_313 = lean_ctor_get(x_310, 1);
lean_inc(x_313);
lean_dec(x_310);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_315 = x_311;
} else {
 lean_dec_ref(x_311);
 x_315 = lean_box(0);
}
lean_inc(x_305);
x_316 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_305, x_313, x_312, x_309);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
lean_dec(x_316);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_321 = x_317;
} else {
 lean_dec_ref(x_317);
 x_321 = lean_box(0);
}
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_323 = x_318;
} else {
 lean_dec_ref(x_318);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_305);
lean_ctor_set(x_324, 1, x_314);
if (lean_is_scalar(x_315)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_315;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_322);
if (lean_is_scalar(x_321)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_321;
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_320);
x_267 = x_326;
x_268 = x_319;
goto block_297;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_305);
x_327 = lean_ctor_get(x_308, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_308, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_329 = x_308;
} else {
 lean_dec_ref(x_308);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
x_267 = x_330;
x_268 = x_309;
goto block_297;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_265);
lean_dec(x_2);
lean_dec(x_1);
x_346 = lean_ctor_get(x_298, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_298, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_348 = x_298;
} else {
 lean_dec_ref(x_298);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_347);
x_267 = x_349;
x_268 = x_299;
goto block_297;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = 1;
x_17 = l_Lake_loadDepPackage___closed__1;
x_18 = l_Lean_Name_toString(x_11, x_16, x_17);
x_19 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_apply_2(x_8, x_24, x_9);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_usize_sub(x_4, x_13);
x_15 = lean_array_uget(x_3, x_14);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(x_2, x_15, x_1, x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_4 = x_14;
x_6 = x_25;
x_8 = x_26;
x_9 = x_24;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_15);
x_32 = lean_box(0);
x_4 = x_14;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_usize_sub(x_4, x_13);
x_15 = lean_array_uget(x_3, x_14);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(x_2, x_15, x_1, x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_4 = x_14;
x_6 = x_25;
x_8 = x_26;
x_9 = x_24;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_15);
x_32 = lean_box(0);
x_4 = x_14;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
x_11 = lean_ctor_get(x_2, 7);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_nat_dec_le(x_12, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_10, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_10, x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
else
{
size_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_27 = lean_box(0);
x_28 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__2(x_3, x_9, x_26, x_26, x_27, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_28;
}
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
x_29 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_30 = 0;
x_31 = lean_box(0);
lean_inc(x_7);
x_32 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3(x_1, x_2, x_11, x_29, x_30, x_31, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_33, 1);
x_40 = lean_ctor_get(x_33, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_34, 1);
x_43 = lean_ctor_get(x_34, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_42, 3);
lean_inc(x_44);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_10, x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_34, 0, x_31);
return x_32;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_34, 0, x_31);
return x_32;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
lean_free_object(x_34);
lean_free_object(x_33);
lean_free_object(x_32);
x_48 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_49 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__4(x_3, x_44, x_48, x_49, x_31, x_4, x_42, x_39, x_7, x_36);
lean_dec(x_44);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_dec(x_34);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_10, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_33, 0, x_55);
return x_32;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_53, x_53);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_31);
lean_ctor_set(x_57, 1, x_51);
lean_ctor_set(x_33, 0, x_57);
return x_32;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
lean_free_object(x_33);
lean_free_object(x_32);
x_58 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_59 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_60 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__4(x_3, x_52, x_58, x_59, x_31, x_4, x_51, x_39, x_7, x_36);
lean_dec(x_52);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_33, 1);
lean_inc(x_61);
lean_dec(x_33);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_63 = x_34;
} else {
 lean_dec_ref(x_34);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_62, 3);
lean_inc(x_64);
x_65 = lean_array_get_size(x_64);
x_66 = lean_nat_dec_lt(x_10, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_31);
lean_ctor_set(x_67, 1, x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_32, 0, x_68);
return x_32;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_65, x_65);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_31);
lean_ctor_set(x_70, 1, x_62);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_61);
lean_ctor_set(x_32, 0, x_71);
return x_32;
}
else
{
size_t x_72; size_t x_73; lean_object* x_74; 
lean_dec(x_63);
lean_free_object(x_32);
x_72 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_73 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_74 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__4(x_3, x_64, x_72, x_73, x_31, x_4, x_62, x_61, x_7, x_36);
lean_dec(x_64);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_75 = lean_ctor_get(x_32, 1);
lean_inc(x_75);
lean_dec(x_32);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_77 = x_33;
} else {
 lean_dec_ref(x_33);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_34, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_79 = x_34;
} else {
 lean_dec_ref(x_34);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_78, 3);
lean_inc(x_80);
x_81 = lean_array_get_size(x_80);
x_82 = lean_nat_dec_lt(x_10, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_31);
lean_ctor_set(x_83, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_77;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_81, x_81);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_79)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_79;
}
lean_ctor_set(x_87, 0, x_31);
lean_ctor_set(x_87, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_77;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_76);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_75);
return x_89;
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
lean_dec(x_79);
lean_dec(x_77);
x_90 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_91 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_92 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__4(x_3, x_80, x_90, x_91, x_31, x_4, x_78, x_76, x_7, x_75);
lean_dec(x_80);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_32);
if (x_93 == 0)
{
return x_32;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_32, 0);
x_95 = lean_ctor_get(x_32, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_32);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_lt(x_97, x_12);
if (x_98 == 0)
{
uint8_t x_99; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_nat_dec_lt(x_10, x_10);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_5);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_6);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_8);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_10, x_10);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_5);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_6);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_8);
return x_108;
}
else
{
size_t x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_110 = lean_box(0);
x_111 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__5(x_3, x_9, x_109, x_109, x_110, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_111;
}
}
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_9);
x_112 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_113 = 0;
x_114 = lean_box(0);
lean_inc(x_7);
x_115 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__6(x_1, x_2, x_11, x_112, x_113, x_114, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_115, 1);
x_120 = lean_ctor_get(x_115, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_116, 1);
x_123 = lean_ctor_get(x_116, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_117);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_117, 1);
x_126 = lean_ctor_get(x_117, 0);
lean_dec(x_126);
x_127 = lean_ctor_get(x_125, 3);
lean_inc(x_127);
x_128 = lean_array_get_size(x_127);
x_129 = lean_nat_dec_lt(x_10, x_128);
if (x_129 == 0)
{
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_117, 0, x_114);
return x_115;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_le(x_128, x_128);
if (x_130 == 0)
{
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_117, 0, x_114);
return x_115;
}
else
{
size_t x_131; size_t x_132; lean_object* x_133; 
lean_free_object(x_117);
lean_free_object(x_116);
lean_free_object(x_115);
x_131 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_132 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_133 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__7(x_3, x_127, x_131, x_132, x_114, x_4, x_125, x_122, x_7, x_119);
lean_dec(x_127);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_117, 1);
lean_inc(x_134);
lean_dec(x_117);
x_135 = lean_ctor_get(x_134, 3);
lean_inc(x_135);
x_136 = lean_array_get_size(x_135);
x_137 = lean_nat_dec_lt(x_10, x_136);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_114);
lean_ctor_set(x_138, 1, x_134);
lean_ctor_set(x_116, 0, x_138);
return x_115;
}
else
{
uint8_t x_139; 
x_139 = lean_nat_dec_le(x_136, x_136);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_114);
lean_ctor_set(x_140, 1, x_134);
lean_ctor_set(x_116, 0, x_140);
return x_115;
}
else
{
size_t x_141; size_t x_142; lean_object* x_143; 
lean_free_object(x_116);
lean_free_object(x_115);
x_141 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_142 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_143 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__7(x_3, x_135, x_141, x_142, x_114, x_4, x_134, x_122, x_7, x_119);
lean_dec(x_135);
return x_143;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_116, 1);
lean_inc(x_144);
lean_dec(x_116);
x_145 = lean_ctor_get(x_117, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_146 = x_117;
} else {
 lean_dec_ref(x_117);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_145, 3);
lean_inc(x_147);
x_148 = lean_array_get_size(x_147);
x_149 = lean_nat_dec_lt(x_10, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_146)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_146;
}
lean_ctor_set(x_150, 0, x_114);
lean_ctor_set(x_150, 1, x_145);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_144);
lean_ctor_set(x_115, 0, x_151);
return x_115;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_148, x_148);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_146)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_146;
}
lean_ctor_set(x_153, 0, x_114);
lean_ctor_set(x_153, 1, x_145);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_144);
lean_ctor_set(x_115, 0, x_154);
return x_115;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; 
lean_dec(x_146);
lean_free_object(x_115);
x_155 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_156 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_157 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__7(x_3, x_147, x_155, x_156, x_114, x_4, x_145, x_144, x_7, x_119);
lean_dec(x_147);
return x_157;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_158 = lean_ctor_get(x_115, 1);
lean_inc(x_158);
lean_dec(x_115);
x_159 = lean_ctor_get(x_116, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_160 = x_116;
} else {
 lean_dec_ref(x_116);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_117, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_162 = x_117;
} else {
 lean_dec_ref(x_117);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_161, 3);
lean_inc(x_163);
x_164 = lean_array_get_size(x_163);
x_165 = lean_nat_dec_lt(x_10, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_162)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_162;
}
lean_ctor_set(x_166, 0, x_114);
lean_ctor_set(x_166, 1, x_161);
if (lean_is_scalar(x_160)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_160;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_159);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_158);
return x_168;
}
else
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_164, x_164);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_162)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_162;
}
lean_ctor_set(x_170, 0, x_114);
lean_ctor_set(x_170, 1, x_161);
if (lean_is_scalar(x_160)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_160;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_159);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_158);
return x_172;
}
else
{
size_t x_173; size_t x_174; lean_object* x_175; 
lean_dec(x_162);
lean_dec(x_160);
x_173 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_174 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_175 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__7(x_3, x_163, x_173, x_174, x_114, x_4, x_161, x_159, x_7, x_158);
lean_dec(x_163);
return x_175;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_176 = !lean_is_exclusive(x_115);
if (x_176 == 0)
{
return x_115;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_115, 0);
x_178 = lean_ctor_get(x_115, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_115);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__2(x_1, x_7);
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
x_17 = lean_apply_2(x_5, x_16, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__11(x_1, x_3, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_9, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__11___lambda__1___boxed), 8, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__1(x_1, x_2, x_12, x_11, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1;
lean_inc(x_3);
x_16 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__9(x_9, x_3, x_15);
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
x_21 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10___rarg(x_20, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__11(x_1, x_3, x_4, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
lean_ctor_set(x_10, 1, x_13);
lean_ctor_set(x_10, 0, x_15);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_22 = x_10;
} else {
 lean_dec_ref(x_10);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__12(x_1, x_2, x_4);
x_9 = 1;
lean_inc(x_1);
x_10 = l_Lean_Name_toString(x_5, x_9, x_1);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_6);
x_12 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_8, x_10, x_11);
x_2 = x_12;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__12___at_Lake_Workspace_updateAndMaterializeCore___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_RBNode_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__12___at_Lake_Workspace_updateAndMaterializeCore___spec__13(x_1, x_3);
x_8 = 1;
x_9 = l_Lake_loadDepPackage___closed__1;
x_10 = l_Lean_Name_toString(x_4, x_8, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = l_Lean_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_7, x_10, x_11);
x_1 = x_12;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": updating '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' with ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_12 = lean_array_uget(x_5, x_4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_5, x_4, x_13);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = 1;
x_27 = l_Lake_loadDepPackage___closed__1;
x_28 = l_Lean_Name_toString(x_25, x_26, x_27);
x_29 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
x_34 = l_Lean_Name_toString(x_33, x_26, x_27);
x_35 = lean_string_append(x_32, x_34);
lean_dec(x_34);
x_36 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_ctor_get(x_12, 4);
lean_inc(x_38);
x_39 = lean_box(0);
x_40 = l_Lean_RBNode_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__12___at_Lake_Workspace_updateAndMaterializeCore___spec__13(x_39, x_38);
x_41 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_unsigned_to_nat(80u);
x_43 = l_Lean_Json_pretty(x_41, x_42);
x_44 = lean_string_append(x_37, x_43);
lean_dec(x_43);
x_45 = lean_string_append(x_44, x_29);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
lean_inc(x_7);
x_48 = lean_apply_2(x_7, x_47, x_8);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_2);
lean_inc(x_1);
x_51 = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(x_1, x_2, x_12, x_6, x_50, x_49);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_array_get_size(x_55);
x_57 = lean_nat_dec_lt(x_13, x_56);
if (x_57 == 0)
{
lean_dec(x_56);
lean_dec(x_55);
x_15 = x_54;
x_16 = x_53;
goto block_23;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_56, x_56);
if (x_58 == 0)
{
lean_dec(x_56);
lean_dec(x_55);
x_15 = x_54;
x_16 = x_53;
goto block_23;
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_61 = lean_box(0);
lean_inc(x_7);
x_62 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_55, x_59, x_60, x_61, x_7, x_53);
lean_dec(x_55);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_15 = x_54;
x_16 = x_63;
goto block_23;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_51);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_51, 1);
x_66 = lean_ctor_get(x_51, 0);
lean_dec(x_66);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
lean_dec(x_52);
x_68 = lean_array_get_size(x_67);
x_69 = lean_nat_dec_lt(x_13, x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_7);
x_70 = lean_box(0);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_70);
return x_51;
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_le(x_68, x_68);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_7);
x_72 = lean_box(0);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_72);
return x_51;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_free_object(x_51);
x_73 = 0;
x_74 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_75 = lean_box(0);
x_76 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_67, x_73, x_74, x_75, x_7, x_65);
lean_dec(x_67);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_51, 1);
lean_inc(x_81);
lean_dec(x_51);
x_82 = lean_ctor_get(x_52, 1);
lean_inc(x_82);
lean_dec(x_52);
x_83 = lean_array_get_size(x_82);
x_84 = lean_nat_dec_lt(x_13, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_7);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_83, x_83);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_7);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_81);
return x_89;
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_92 = lean_box(0);
x_93 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_82, x_90, x_91, x_92, x_7, x_81);
lean_dec(x_82);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
 lean_ctor_set_tag(x_96, 1);
}
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
block_23:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_array_uset(x_14, x_4, x_17);
x_4 = x_20;
x_5 = x_21;
x_6 = x_18;
x_8 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__16(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_usize_sub(x_4, x_13);
x_15 = lean_array_uget(x_3, x_14);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(x_2, x_15, x_1, x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_4 = x_14;
x_6 = x_25;
x_8 = x_26;
x_9 = x_24;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_15);
x_32 = lean_box(0);
x_4 = x_14;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__18(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__19(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_usize_sub(x_4, x_13);
x_15 = lean_array_uget(x_3, x_14);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(x_2, x_15, x_1, x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_4 = x_14;
x_6 = x_25;
x_8 = x_26;
x_9 = x_24;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_15);
x_32 = lean_box(0);
x_4 = x_14;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__21(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
x_11 = lean_ctor_get(x_2, 7);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_nat_dec_le(x_12, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_10, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_10, x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
else
{
size_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_27 = lean_box(0);
x_28 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__16(x_3, x_9, x_26, x_26, x_27, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_28;
}
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
x_29 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_30 = 0;
x_31 = lean_box(0);
lean_inc(x_7);
x_32 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__17(x_1, x_2, x_11, x_29, x_30, x_31, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_33, 1);
x_40 = lean_ctor_get(x_33, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_34, 1);
x_43 = lean_ctor_get(x_34, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_42, 3);
lean_inc(x_44);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_10, x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_34, 0, x_31);
return x_32;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_34, 0, x_31);
return x_32;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
lean_free_object(x_34);
lean_free_object(x_33);
lean_free_object(x_32);
x_48 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_49 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__18(x_3, x_44, x_48, x_49, x_31, x_4, x_42, x_39, x_7, x_36);
lean_dec(x_44);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_dec(x_34);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_10, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_33, 0, x_55);
return x_32;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_53, x_53);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_31);
lean_ctor_set(x_57, 1, x_51);
lean_ctor_set(x_33, 0, x_57);
return x_32;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
lean_free_object(x_33);
lean_free_object(x_32);
x_58 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_59 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_60 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__18(x_3, x_52, x_58, x_59, x_31, x_4, x_51, x_39, x_7, x_36);
lean_dec(x_52);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_33, 1);
lean_inc(x_61);
lean_dec(x_33);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_63 = x_34;
} else {
 lean_dec_ref(x_34);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_62, 3);
lean_inc(x_64);
x_65 = lean_array_get_size(x_64);
x_66 = lean_nat_dec_lt(x_10, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_31);
lean_ctor_set(x_67, 1, x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_32, 0, x_68);
return x_32;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_65, x_65);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_31);
lean_ctor_set(x_70, 1, x_62);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_61);
lean_ctor_set(x_32, 0, x_71);
return x_32;
}
else
{
size_t x_72; size_t x_73; lean_object* x_74; 
lean_dec(x_63);
lean_free_object(x_32);
x_72 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_73 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_74 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__18(x_3, x_64, x_72, x_73, x_31, x_4, x_62, x_61, x_7, x_36);
lean_dec(x_64);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_75 = lean_ctor_get(x_32, 1);
lean_inc(x_75);
lean_dec(x_32);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_77 = x_33;
} else {
 lean_dec_ref(x_33);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_34, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_79 = x_34;
} else {
 lean_dec_ref(x_34);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_78, 3);
lean_inc(x_80);
x_81 = lean_array_get_size(x_80);
x_82 = lean_nat_dec_lt(x_10, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_31);
lean_ctor_set(x_83, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_77;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_81, x_81);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_79)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_79;
}
lean_ctor_set(x_87, 0, x_31);
lean_ctor_set(x_87, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_77;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_76);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_75);
return x_89;
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
lean_dec(x_79);
lean_dec(x_77);
x_90 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_91 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_92 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__18(x_3, x_80, x_90, x_91, x_31, x_4, x_78, x_76, x_7, x_75);
lean_dec(x_80);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_32);
if (x_93 == 0)
{
return x_32;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_32, 0);
x_95 = lean_ctor_get(x_32, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_32);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_lt(x_97, x_12);
if (x_98 == 0)
{
uint8_t x_99; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_nat_dec_lt(x_10, x_10);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_5);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_6);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_8);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_10, x_10);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_5);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_6);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_8);
return x_108;
}
else
{
size_t x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_110 = lean_box(0);
x_111 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__19(x_3, x_9, x_109, x_109, x_110, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_111;
}
}
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_9);
x_112 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_113 = 0;
x_114 = lean_box(0);
lean_inc(x_7);
x_115 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__20(x_1, x_2, x_11, x_112, x_113, x_114, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_115, 1);
x_120 = lean_ctor_get(x_115, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_116, 1);
x_123 = lean_ctor_get(x_116, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_117);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_117, 1);
x_126 = lean_ctor_get(x_117, 0);
lean_dec(x_126);
x_127 = lean_ctor_get(x_125, 3);
lean_inc(x_127);
x_128 = lean_array_get_size(x_127);
x_129 = lean_nat_dec_lt(x_10, x_128);
if (x_129 == 0)
{
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_117, 0, x_114);
return x_115;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_le(x_128, x_128);
if (x_130 == 0)
{
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_117, 0, x_114);
return x_115;
}
else
{
size_t x_131; size_t x_132; lean_object* x_133; 
lean_free_object(x_117);
lean_free_object(x_116);
lean_free_object(x_115);
x_131 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_132 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_133 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__21(x_3, x_127, x_131, x_132, x_114, x_4, x_125, x_122, x_7, x_119);
lean_dec(x_127);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_117, 1);
lean_inc(x_134);
lean_dec(x_117);
x_135 = lean_ctor_get(x_134, 3);
lean_inc(x_135);
x_136 = lean_array_get_size(x_135);
x_137 = lean_nat_dec_lt(x_10, x_136);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_114);
lean_ctor_set(x_138, 1, x_134);
lean_ctor_set(x_116, 0, x_138);
return x_115;
}
else
{
uint8_t x_139; 
x_139 = lean_nat_dec_le(x_136, x_136);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_114);
lean_ctor_set(x_140, 1, x_134);
lean_ctor_set(x_116, 0, x_140);
return x_115;
}
else
{
size_t x_141; size_t x_142; lean_object* x_143; 
lean_free_object(x_116);
lean_free_object(x_115);
x_141 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_142 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_143 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__21(x_3, x_135, x_141, x_142, x_114, x_4, x_134, x_122, x_7, x_119);
lean_dec(x_135);
return x_143;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_116, 1);
lean_inc(x_144);
lean_dec(x_116);
x_145 = lean_ctor_get(x_117, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_146 = x_117;
} else {
 lean_dec_ref(x_117);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_145, 3);
lean_inc(x_147);
x_148 = lean_array_get_size(x_147);
x_149 = lean_nat_dec_lt(x_10, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_146)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_146;
}
lean_ctor_set(x_150, 0, x_114);
lean_ctor_set(x_150, 1, x_145);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_144);
lean_ctor_set(x_115, 0, x_151);
return x_115;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_148, x_148);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_146)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_146;
}
lean_ctor_set(x_153, 0, x_114);
lean_ctor_set(x_153, 1, x_145);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_144);
lean_ctor_set(x_115, 0, x_154);
return x_115;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; 
lean_dec(x_146);
lean_free_object(x_115);
x_155 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_156 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_157 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__21(x_3, x_147, x_155, x_156, x_114, x_4, x_145, x_144, x_7, x_119);
lean_dec(x_147);
return x_157;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_158 = lean_ctor_get(x_115, 1);
lean_inc(x_158);
lean_dec(x_115);
x_159 = lean_ctor_get(x_116, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_160 = x_116;
} else {
 lean_dec_ref(x_116);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_117, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_162 = x_117;
} else {
 lean_dec_ref(x_117);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_161, 3);
lean_inc(x_163);
x_164 = lean_array_get_size(x_163);
x_165 = lean_nat_dec_lt(x_10, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_162)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_162;
}
lean_ctor_set(x_166, 0, x_114);
lean_ctor_set(x_166, 1, x_161);
if (lean_is_scalar(x_160)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_160;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_159);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_158);
return x_168;
}
else
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_164, x_164);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_162)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_162;
}
lean_ctor_set(x_170, 0, x_114);
lean_ctor_set(x_170, 1, x_161);
if (lean_is_scalar(x_160)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_160;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_159);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_158);
return x_172;
}
else
{
size_t x_173; size_t x_174; lean_object* x_175; 
lean_dec(x_162);
lean_dec(x_160);
x_173 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_174 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_175 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__21(x_3, x_163, x_173, x_174, x_114, x_4, x_161, x_159, x_7, x_158);
lean_dec(x_163);
return x_175;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_176 = !lean_is_exclusive(x_115);
if (x_176 == 0)
{
return x_115;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_115, 0);
x_178 = lean_ctor_get(x_115, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_115);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__2(x_1, x_7);
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
x_17 = lean_apply_2(x_5, x_16, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__25___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__25(x_1, x_3, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_9, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__25___lambda__1___boxed), 8, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__15(x_1, x_2, x_12, x_11, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1;
lean_inc(x_3);
x_16 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__23(x_9, x_3, x_15);
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
x_21 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24___rarg(x_20, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__25(x_1, x_3, x_4, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
lean_ctor_set(x_10, 1, x_13);
lean_ctor_set(x_10, 0, x_15);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_22 = x_10;
} else {
 lean_dec_ref(x_10);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__26(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_array_uget(x_2, x_3);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_7);
lean_inc(x_1);
x_16 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__22(x_1, x_5, x_10, x_15, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_5 = x_19;
x_6 = x_20;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_1);
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
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__28(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_usize_sub(x_4, x_13);
x_15 = lean_array_uget(x_3, x_14);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(x_2, x_15, x_1, x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_4 = x_14;
x_6 = x_25;
x_8 = x_26;
x_9 = x_24;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_15);
x_32 = lean_box(0);
x_4 = x_14;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__30(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__31(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_usize_sub(x_4, x_13);
x_15 = lean_array_uget(x_3, x_14);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(x_2, x_15, x_1, x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_4 = x_14;
x_6 = x_25;
x_8 = x_26;
x_9 = x_24;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_15);
x_32 = lean_box(0);
x_4 = x_14;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__33(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
x_11 = lean_ctor_get(x_2, 7);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_nat_dec_le(x_12, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_10, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_10, x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
else
{
size_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_27 = lean_box(0);
x_28 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__28(x_3, x_9, x_26, x_26, x_27, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_28;
}
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
x_29 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_30 = 0;
x_31 = lean_box(0);
lean_inc(x_7);
x_32 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__29(x_1, x_2, x_11, x_29, x_30, x_31, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_33, 1);
x_40 = lean_ctor_get(x_33, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_34, 1);
x_43 = lean_ctor_get(x_34, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_42, 3);
lean_inc(x_44);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_10, x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_34, 0, x_31);
return x_32;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_34, 0, x_31);
return x_32;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
lean_free_object(x_34);
lean_free_object(x_33);
lean_free_object(x_32);
x_48 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_49 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__30(x_3, x_44, x_48, x_49, x_31, x_4, x_42, x_39, x_7, x_36);
lean_dec(x_44);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_dec(x_34);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_10, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_33, 0, x_55);
return x_32;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_53, x_53);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_31);
lean_ctor_set(x_57, 1, x_51);
lean_ctor_set(x_33, 0, x_57);
return x_32;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
lean_free_object(x_33);
lean_free_object(x_32);
x_58 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_59 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_60 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__30(x_3, x_52, x_58, x_59, x_31, x_4, x_51, x_39, x_7, x_36);
lean_dec(x_52);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_33, 1);
lean_inc(x_61);
lean_dec(x_33);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_63 = x_34;
} else {
 lean_dec_ref(x_34);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_62, 3);
lean_inc(x_64);
x_65 = lean_array_get_size(x_64);
x_66 = lean_nat_dec_lt(x_10, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_31);
lean_ctor_set(x_67, 1, x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_32, 0, x_68);
return x_32;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_65, x_65);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_31);
lean_ctor_set(x_70, 1, x_62);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_61);
lean_ctor_set(x_32, 0, x_71);
return x_32;
}
else
{
size_t x_72; size_t x_73; lean_object* x_74; 
lean_dec(x_63);
lean_free_object(x_32);
x_72 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_73 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_74 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__30(x_3, x_64, x_72, x_73, x_31, x_4, x_62, x_61, x_7, x_36);
lean_dec(x_64);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_75 = lean_ctor_get(x_32, 1);
lean_inc(x_75);
lean_dec(x_32);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_77 = x_33;
} else {
 lean_dec_ref(x_33);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_34, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_79 = x_34;
} else {
 lean_dec_ref(x_34);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_78, 3);
lean_inc(x_80);
x_81 = lean_array_get_size(x_80);
x_82 = lean_nat_dec_lt(x_10, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_31);
lean_ctor_set(x_83, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_77;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_81, x_81);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_79)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_79;
}
lean_ctor_set(x_87, 0, x_31);
lean_ctor_set(x_87, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_77;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_76);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_75);
return x_89;
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
lean_dec(x_79);
lean_dec(x_77);
x_90 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_91 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_92 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__30(x_3, x_80, x_90, x_91, x_31, x_4, x_78, x_76, x_7, x_75);
lean_dec(x_80);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_32);
if (x_93 == 0)
{
return x_32;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_32, 0);
x_95 = lean_ctor_get(x_32, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_32);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_lt(x_97, x_12);
if (x_98 == 0)
{
uint8_t x_99; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_nat_dec_lt(x_10, x_10);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_5);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_6);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_8);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_10, x_10);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_5);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_6);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_8);
return x_108;
}
else
{
size_t x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_110 = lean_box(0);
x_111 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__31(x_3, x_9, x_109, x_109, x_110, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_111;
}
}
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_9);
x_112 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_113 = 0;
x_114 = lean_box(0);
lean_inc(x_7);
x_115 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__32(x_1, x_2, x_11, x_112, x_113, x_114, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_115, 1);
x_120 = lean_ctor_get(x_115, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_116, 1);
x_123 = lean_ctor_get(x_116, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_117);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_117, 1);
x_126 = lean_ctor_get(x_117, 0);
lean_dec(x_126);
x_127 = lean_ctor_get(x_125, 3);
lean_inc(x_127);
x_128 = lean_array_get_size(x_127);
x_129 = lean_nat_dec_lt(x_10, x_128);
if (x_129 == 0)
{
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_117, 0, x_114);
return x_115;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_le(x_128, x_128);
if (x_130 == 0)
{
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_117, 0, x_114);
return x_115;
}
else
{
size_t x_131; size_t x_132; lean_object* x_133; 
lean_free_object(x_117);
lean_free_object(x_116);
lean_free_object(x_115);
x_131 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_132 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_133 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__33(x_3, x_127, x_131, x_132, x_114, x_4, x_125, x_122, x_7, x_119);
lean_dec(x_127);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_117, 1);
lean_inc(x_134);
lean_dec(x_117);
x_135 = lean_ctor_get(x_134, 3);
lean_inc(x_135);
x_136 = lean_array_get_size(x_135);
x_137 = lean_nat_dec_lt(x_10, x_136);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_114);
lean_ctor_set(x_138, 1, x_134);
lean_ctor_set(x_116, 0, x_138);
return x_115;
}
else
{
uint8_t x_139; 
x_139 = lean_nat_dec_le(x_136, x_136);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_114);
lean_ctor_set(x_140, 1, x_134);
lean_ctor_set(x_116, 0, x_140);
return x_115;
}
else
{
size_t x_141; size_t x_142; lean_object* x_143; 
lean_free_object(x_116);
lean_free_object(x_115);
x_141 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_142 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_143 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__33(x_3, x_135, x_141, x_142, x_114, x_4, x_134, x_122, x_7, x_119);
lean_dec(x_135);
return x_143;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_116, 1);
lean_inc(x_144);
lean_dec(x_116);
x_145 = lean_ctor_get(x_117, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_146 = x_117;
} else {
 lean_dec_ref(x_117);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_145, 3);
lean_inc(x_147);
x_148 = lean_array_get_size(x_147);
x_149 = lean_nat_dec_lt(x_10, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_146)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_146;
}
lean_ctor_set(x_150, 0, x_114);
lean_ctor_set(x_150, 1, x_145);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_144);
lean_ctor_set(x_115, 0, x_151);
return x_115;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_148, x_148);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_146)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_146;
}
lean_ctor_set(x_153, 0, x_114);
lean_ctor_set(x_153, 1, x_145);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_144);
lean_ctor_set(x_115, 0, x_154);
return x_115;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; 
lean_dec(x_146);
lean_free_object(x_115);
x_155 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_156 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_157 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__33(x_3, x_147, x_155, x_156, x_114, x_4, x_145, x_144, x_7, x_119);
lean_dec(x_147);
return x_157;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_158 = lean_ctor_get(x_115, 1);
lean_inc(x_158);
lean_dec(x_115);
x_159 = lean_ctor_get(x_116, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_160 = x_116;
} else {
 lean_dec_ref(x_116);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_117, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_162 = x_117;
} else {
 lean_dec_ref(x_117);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_161, 3);
lean_inc(x_163);
x_164 = lean_array_get_size(x_163);
x_165 = lean_nat_dec_lt(x_10, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_162)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_162;
}
lean_ctor_set(x_166, 0, x_114);
lean_ctor_set(x_166, 1, x_161);
if (lean_is_scalar(x_160)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_160;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_159);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_158);
return x_168;
}
else
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_164, x_164);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_162)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_162;
}
lean_ctor_set(x_170, 0, x_114);
lean_ctor_set(x_170, 1, x_161);
if (lean_is_scalar(x_160)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_160;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_159);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_158);
return x_172;
}
else
{
size_t x_173; size_t x_174; lean_object* x_175; 
lean_dec(x_162);
lean_dec(x_160);
x_173 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_174 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_175 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__33(x_3, x_163, x_173, x_174, x_114, x_4, x_161, x_159, x_7, x_158);
lean_dec(x_163);
return x_175;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_176 = !lean_is_exclusive(x_115);
if (x_176 == 0)
{
return x_115;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_115, 0);
x_178 = lean_ctor_get(x_115, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_115);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__2(x_1, x_7);
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
x_17 = lean_apply_2(x_5, x_16, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__37___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__37(x_1, x_3, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_9, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__37___lambda__1___boxed), 8, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__27(x_1, x_2, x_12, x_11, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1;
lean_inc(x_3);
x_16 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__35(x_9, x_3, x_15);
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
x_21 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36___rarg(x_20, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__37(x_1, x_3, x_4, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
lean_ctor_set(x_10, 1, x_13);
lean_ctor_set(x_10, 0, x_15);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_22 = x_10;
} else {
 lean_dec_ref(x_10);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__38(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_array_uget(x_2, x_3);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_7);
lean_inc(x_1);
x_16 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__34(x_1, x_5, x_10, x_15, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_5 = x_19;
x_6 = x_20;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_1);
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
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__39(lean_object* x_1, size_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_21; lean_object* x_22; uint8_t x_65; 
x_65 = lean_usize_dec_eq(x_4, x_5);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_array_uget(x_3, x_4);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
x_70 = lean_ctor_get(x_6, 0);
lean_inc(x_70);
x_223 = lean_ctor_get(x_68, 4);
lean_inc(x_223);
x_224 = 1;
x_225 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_1);
lean_inc(x_69);
x_226 = l_Lake_loadDepPackage(x_69, x_223, x_1, x_224, x_6, x_225, x_9);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
lean_dec(x_226);
x_230 = !lean_is_exclusive(x_227);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_ctor_get(x_227, 0);
lean_dec(x_231);
x_232 = !lean_is_exclusive(x_228);
if (x_232 == 0)
{
lean_ctor_set(x_66, 1, x_7);
lean_ctor_set(x_66, 0, x_228);
lean_ctor_set(x_227, 0, x_66);
x_71 = x_227;
x_72 = x_229;
goto block_222;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_228, 0);
x_234 = lean_ctor_get(x_228, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_228);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set(x_66, 1, x_7);
lean_ctor_set(x_66, 0, x_235);
lean_ctor_set(x_227, 0, x_66);
x_71 = x_227;
x_72 = x_229;
goto block_222;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_227, 1);
lean_inc(x_236);
lean_dec(x_227);
x_237 = lean_ctor_get(x_228, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_228, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_239 = x_228;
} else {
 lean_dec_ref(x_228);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
lean_ctor_set(x_66, 1, x_7);
lean_ctor_set(x_66, 0, x_240);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_66);
lean_ctor_set(x_241, 1, x_236);
x_71 = x_241;
x_72 = x_229;
goto block_222;
}
}
else
{
lean_object* x_242; uint8_t x_243; 
lean_free_object(x_66);
lean_dec(x_7);
x_242 = lean_ctor_get(x_226, 1);
lean_inc(x_242);
lean_dec(x_226);
x_243 = !lean_is_exclusive(x_227);
if (x_243 == 0)
{
x_71 = x_227;
x_72 = x_242;
goto block_222;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_227, 0);
x_245 = lean_ctor_get(x_227, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_227);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_71 = x_246;
x_72 = x_242;
goto block_222;
}
}
block_222:
{
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_73, 1);
x_78 = lean_ctor_get(x_73, 0);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_74);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_124; lean_object* x_125; 
x_80 = lean_ctor_get(x_74, 0);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
x_124 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_70, x_68, x_69, x_80, x_75, x_72);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = !lean_is_exclusive(x_125);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_125, 0);
lean_ctor_set(x_74, 0, x_128);
lean_ctor_set(x_125, 0, x_73);
x_82 = x_125;
x_83 = x_126;
goto block_123;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_125, 0);
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_125);
lean_ctor_set(x_74, 0, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_73);
lean_ctor_set(x_131, 1, x_130);
x_82 = x_131;
x_83 = x_126;
goto block_123;
}
}
else
{
lean_object* x_132; uint8_t x_133; 
lean_free_object(x_74);
lean_dec(x_81);
lean_free_object(x_73);
lean_dec(x_77);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
lean_dec(x_124);
x_133 = !lean_is_exclusive(x_125);
if (x_133 == 0)
{
x_82 = x_125;
x_83 = x_132;
goto block_123;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_125, 0);
x_135 = lean_ctor_get(x_125, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_125);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_82 = x_136;
x_83 = x_132;
goto block_123;
}
}
block_123:
{
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = !lean_is_exclusive(x_85);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_89 = lean_ctor_get(x_85, 1);
x_90 = lean_ctor_get(x_85, 0);
lean_dec(x_90);
lean_inc(x_80);
x_91 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_80, x_87, x_86, x_83);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = !lean_is_exclusive(x_92);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_92, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_93);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_93, 1);
x_99 = lean_ctor_get(x_93, 0);
lean_dec(x_99);
lean_ctor_set(x_93, 1, x_89);
lean_ctor_set(x_93, 0, x_80);
lean_ctor_set(x_85, 1, x_98);
lean_ctor_set(x_85, 0, x_93);
lean_ctor_set(x_92, 0, x_85);
x_21 = x_92;
x_22 = x_94;
goto block_64;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_80);
lean_ctor_set(x_101, 1, x_89);
lean_ctor_set(x_85, 1, x_100);
lean_ctor_set(x_85, 0, x_101);
lean_ctor_set(x_92, 0, x_85);
x_21 = x_92;
x_22 = x_94;
goto block_64;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
lean_dec(x_92);
x_103 = lean_ctor_get(x_93, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_104 = x_93;
} else {
 lean_dec_ref(x_93);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_80);
lean_ctor_set(x_105, 1, x_89);
lean_ctor_set(x_85, 1, x_103);
lean_ctor_set(x_85, 0, x_105);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_85);
lean_ctor_set(x_106, 1, x_102);
x_21 = x_106;
x_22 = x_94;
goto block_64;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_107 = lean_ctor_get(x_85, 1);
lean_inc(x_107);
lean_dec(x_85);
lean_inc(x_80);
x_108 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_80, x_87, x_86, x_83);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_113 = x_109;
} else {
 lean_dec_ref(x_109);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_115 = x_110;
} else {
 lean_dec_ref(x_110);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_80);
lean_ctor_set(x_116, 1, x_107);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
if (lean_is_scalar(x_113)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_113;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_112);
x_21 = x_118;
x_22 = x_111;
goto block_64;
}
}
else
{
uint8_t x_119; 
lean_dec(x_80);
x_119 = !lean_is_exclusive(x_82);
if (x_119 == 0)
{
x_21 = x_82;
x_22 = x_83;
goto block_64;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_82, 0);
x_121 = lean_ctor_get(x_82, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_82);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_21 = x_122;
x_22 = x_83;
goto block_64;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_163; lean_object* x_164; 
x_137 = lean_ctor_get(x_74, 0);
x_138 = lean_ctor_get(x_74, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_74);
lean_inc(x_137);
x_163 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_70, x_68, x_69, x_137, x_75, x_72);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_168 = x_164;
} else {
 lean_dec_ref(x_164);
 x_168 = lean_box(0);
}
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_138);
lean_ctor_set(x_73, 0, x_169);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_73);
lean_ctor_set(x_170, 1, x_167);
x_139 = x_170;
x_140 = x_165;
goto block_162;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_138);
lean_free_object(x_73);
lean_dec(x_77);
x_171 = lean_ctor_get(x_163, 1);
lean_inc(x_171);
lean_dec(x_163);
x_172 = lean_ctor_get(x_164, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_164, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_174 = x_164;
} else {
 lean_dec_ref(x_164);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
x_139 = x_175;
x_140 = x_171;
goto block_162;
}
block_162:
{
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_146 = x_142;
} else {
 lean_dec_ref(x_142);
 x_146 = lean_box(0);
}
lean_inc(x_137);
x_147 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_137, x_144, x_143, x_140);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
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
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_137);
lean_ctor_set(x_155, 1, x_145);
if (lean_is_scalar(x_146)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_146;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
if (lean_is_scalar(x_152)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_152;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_151);
x_21 = x_157;
x_22 = x_150;
goto block_64;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_137);
x_158 = lean_ctor_get(x_139, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_139, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_160 = x_139;
} else {
 lean_dec_ref(x_139);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
x_21 = x_161;
x_22 = x_140;
goto block_64;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_204; lean_object* x_205; 
x_176 = lean_ctor_get(x_73, 1);
lean_inc(x_176);
lean_dec(x_73);
x_177 = lean_ctor_get(x_74, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_74, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_179 = x_74;
} else {
 lean_dec_ref(x_74);
 x_179 = lean_box(0);
}
lean_inc(x_177);
x_204 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_70, x_68, x_69, x_177, x_75, x_72);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_209 = x_205;
} else {
 lean_dec_ref(x_205);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_179;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_178);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_176);
if (lean_is_scalar(x_209)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_209;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_208);
x_180 = x_212;
x_181 = x_206;
goto block_203;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_176);
x_213 = lean_ctor_get(x_204, 1);
lean_inc(x_213);
lean_dec(x_204);
x_214 = lean_ctor_get(x_205, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_205, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_216 = x_205;
} else {
 lean_dec_ref(x_205);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
x_180 = x_217;
x_181 = x_213;
goto block_203;
}
block_203:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
lean_dec(x_180);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_187 = x_183;
} else {
 lean_dec_ref(x_183);
 x_187 = lean_box(0);
}
lean_inc(x_177);
x_188 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_177, x_185, x_184, x_181);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_193 = x_189;
} else {
 lean_dec_ref(x_189);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_195 = x_190;
} else {
 lean_dec_ref(x_190);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_177);
lean_ctor_set(x_196, 1, x_186);
if (lean_is_scalar(x_187)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_187;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_194);
if (lean_is_scalar(x_193)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_193;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_192);
x_21 = x_198;
x_22 = x_191;
goto block_64;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_177);
x_199 = lean_ctor_get(x_180, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_180, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_201 = x_180;
} else {
 lean_dec_ref(x_180);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
x_21 = x_202;
x_22 = x_181;
goto block_64;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
x_218 = !lean_is_exclusive(x_71);
if (x_218 == 0)
{
x_21 = x_71;
x_22 = x_72;
goto block_64;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_71, 0);
x_220 = lean_ctor_get(x_71, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_71);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_21 = x_221;
x_22 = x_72;
goto block_64;
}
}
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_303; uint8_t x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_247 = lean_ctor_get(x_66, 0);
x_248 = lean_ctor_get(x_66, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_66);
x_249 = lean_ctor_get(x_6, 0);
lean_inc(x_249);
x_303 = lean_ctor_get(x_247, 4);
lean_inc(x_303);
x_304 = 1;
x_305 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_1);
lean_inc(x_248);
x_306 = l_Lake_loadDepPackage(x_248, x_303, x_1, x_304, x_6, x_305, x_9);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_dec(x_306);
x_310 = lean_ctor_get(x_307, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_311 = x_307;
} else {
 lean_dec_ref(x_307);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_308, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_308, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_314 = x_308;
} else {
 lean_dec_ref(x_308);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_313);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_7);
if (lean_is_scalar(x_311)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_311;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_310);
x_250 = x_317;
x_251 = x_309;
goto block_302;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_7);
x_318 = lean_ctor_get(x_306, 1);
lean_inc(x_318);
lean_dec(x_306);
x_319 = lean_ctor_get(x_307, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_307, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_321 = x_307;
} else {
 lean_dec_ref(x_307);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_320);
x_250 = x_322;
x_251 = x_318;
goto block_302;
}
block_302:
{
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_284; lean_object* x_285; 
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_250, 1);
lean_inc(x_254);
lean_dec(x_250);
x_255 = lean_ctor_get(x_252, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_256 = x_252;
} else {
 lean_dec_ref(x_252);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_253, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_259 = x_253;
} else {
 lean_dec_ref(x_253);
 x_259 = lean_box(0);
}
lean_inc(x_257);
x_284 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_249, x_247, x_248, x_257, x_254, x_251);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_ctor_get(x_285, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_289 = x_285;
} else {
 lean_dec_ref(x_285);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_259;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_258);
if (lean_is_scalar(x_256)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_256;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_255);
if (lean_is_scalar(x_289)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_289;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_288);
x_260 = x_292;
x_261 = x_286;
goto block_283;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_256);
lean_dec(x_255);
x_293 = lean_ctor_get(x_284, 1);
lean_inc(x_293);
lean_dec(x_284);
x_294 = lean_ctor_get(x_285, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_285, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_296 = x_285;
} else {
 lean_dec_ref(x_285);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
x_260 = x_297;
x_261 = x_293;
goto block_283;
}
block_283:
{
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_260, 1);
lean_inc(x_264);
lean_dec(x_260);
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_dec(x_262);
x_266 = lean_ctor_get(x_263, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_267 = x_263;
} else {
 lean_dec_ref(x_263);
 x_267 = lean_box(0);
}
lean_inc(x_257);
x_268 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_257, x_265, x_264, x_261);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
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
x_274 = lean_ctor_get(x_270, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_275 = x_270;
} else {
 lean_dec_ref(x_270);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_257);
lean_ctor_set(x_276, 1, x_266);
if (lean_is_scalar(x_267)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_267;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_274);
if (lean_is_scalar(x_273)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_273;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_272);
x_21 = x_278;
x_22 = x_271;
goto block_64;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_257);
x_279 = lean_ctor_get(x_260, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_260, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_281 = x_260;
} else {
 lean_dec_ref(x_260);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
x_21 = x_282;
x_22 = x_261;
goto block_64;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
x_298 = lean_ctor_get(x_250, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_250, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_300 = x_250;
} else {
 lean_dec_ref(x_250);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
x_21 = x_301;
x_22 = x_251;
goto block_64;
}
}
}
}
else
{
lean_object* x_323; lean_object* x_324; 
lean_dec(x_8);
lean_dec(x_1);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_6);
lean_ctor_set(x_323, 1, x_7);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_9);
return x_324;
}
block_20:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
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
x_16 = l_Lake_Workspace_addPackage(x_14, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_6 = x_16;
x_7 = x_13;
x_9 = x_11;
goto _start;
}
block_64:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_array_get_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
if (x_27 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
x_10 = x_23;
x_11 = x_22;
goto block_20;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_25, x_25);
if (x_28 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
x_10 = x_23;
x_11 = x_22;
goto block_20;
}
else
{
size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_30 = lean_box(0);
lean_inc(x_8);
x_31 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_24, x_2, x_29, x_30, x_8, x_22);
lean_dec(x_24);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_10 = x_23;
x_11 = x_32;
goto block_20;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_21, 1);
x_35 = lean_ctor_get(x_21, 0);
lean_dec(x_35);
x_36 = lean_array_get_size(x_34);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_8);
x_39 = lean_box(0);
lean_ctor_set(x_21, 1, x_22);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_36, x_36);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_8);
x_41 = lean_box(0);
lean_ctor_set(x_21, 1, x_22);
lean_ctor_set(x_21, 0, x_41);
return x_21;
}
else
{
size_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_free_object(x_21);
x_42 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_43 = lean_box(0);
x_44 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_34, x_2, x_42, x_43, x_8, x_22);
lean_dec(x_34);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_dec(x_21);
x_50 = lean_array_get_size(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_8);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_22);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_50, x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_8);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_22);
return x_57;
}
else
{
size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_59 = lean_box(0);
x_60 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_49, x_2, x_58, x_59, x_8, x_22);
lean_dec(x_49);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__41(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__42(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_usize_sub(x_4, x_13);
x_15 = lean_array_uget(x_3, x_14);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(x_2, x_15, x_1, x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_4 = x_14;
x_6 = x_25;
x_8 = x_26;
x_9 = x_24;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_15);
x_32 = lean_box(0);
x_4 = x_14;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__43(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__44(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_usize_sub(x_4, x_13);
x_15 = lean_array_uget(x_3, x_14);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(x_2, x_15, x_1, x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
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
x_4 = x_14;
x_6 = x_25;
x_8 = x_26;
x_9 = x_24;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_15);
x_32 = lean_box(0);
x_4 = x_14;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__46(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
x_8 = x_17;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
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
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
x_11 = lean_ctor_get(x_2, 7);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_nat_dec_le(x_12, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_10, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_10, x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
else
{
size_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_27 = lean_box(0);
x_28 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__41(x_3, x_9, x_26, x_26, x_27, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_28;
}
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
x_29 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_30 = 0;
x_31 = lean_box(0);
lean_inc(x_7);
x_32 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__42(x_1, x_2, x_11, x_29, x_30, x_31, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_33, 1);
x_40 = lean_ctor_get(x_33, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_34, 1);
x_43 = lean_ctor_get(x_34, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_42, 3);
lean_inc(x_44);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_10, x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_34, 0, x_31);
return x_32;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_34, 0, x_31);
return x_32;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
lean_free_object(x_34);
lean_free_object(x_33);
lean_free_object(x_32);
x_48 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_49 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__43(x_3, x_44, x_48, x_49, x_31, x_4, x_42, x_39, x_7, x_36);
lean_dec(x_44);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_dec(x_34);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_10, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_33, 0, x_55);
return x_32;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_53, x_53);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_31);
lean_ctor_set(x_57, 1, x_51);
lean_ctor_set(x_33, 0, x_57);
return x_32;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
lean_free_object(x_33);
lean_free_object(x_32);
x_58 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_59 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_60 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__43(x_3, x_52, x_58, x_59, x_31, x_4, x_51, x_39, x_7, x_36);
lean_dec(x_52);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_33, 1);
lean_inc(x_61);
lean_dec(x_33);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_63 = x_34;
} else {
 lean_dec_ref(x_34);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_62, 3);
lean_inc(x_64);
x_65 = lean_array_get_size(x_64);
x_66 = lean_nat_dec_lt(x_10, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_31);
lean_ctor_set(x_67, 1, x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_32, 0, x_68);
return x_32;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_65, x_65);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_31);
lean_ctor_set(x_70, 1, x_62);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_61);
lean_ctor_set(x_32, 0, x_71);
return x_32;
}
else
{
size_t x_72; size_t x_73; lean_object* x_74; 
lean_dec(x_63);
lean_free_object(x_32);
x_72 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_73 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_74 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__43(x_3, x_64, x_72, x_73, x_31, x_4, x_62, x_61, x_7, x_36);
lean_dec(x_64);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_75 = lean_ctor_get(x_32, 1);
lean_inc(x_75);
lean_dec(x_32);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_77 = x_33;
} else {
 lean_dec_ref(x_33);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_34, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_79 = x_34;
} else {
 lean_dec_ref(x_34);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_78, 3);
lean_inc(x_80);
x_81 = lean_array_get_size(x_80);
x_82 = lean_nat_dec_lt(x_10, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_31);
lean_ctor_set(x_83, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_77;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_81, x_81);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_79)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_79;
}
lean_ctor_set(x_87, 0, x_31);
lean_ctor_set(x_87, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_77;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_76);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_75);
return x_89;
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
lean_dec(x_79);
lean_dec(x_77);
x_90 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_91 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_92 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__43(x_3, x_80, x_90, x_91, x_31, x_4, x_78, x_76, x_7, x_75);
lean_dec(x_80);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_32);
if (x_93 == 0)
{
return x_32;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_32, 0);
x_95 = lean_ctor_get(x_32, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_32);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_lt(x_97, x_12);
if (x_98 == 0)
{
uint8_t x_99; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_nat_dec_lt(x_10, x_10);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_5);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_6);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_8);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_10, x_10);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_5);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_6);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_8);
return x_108;
}
else
{
size_t x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_110 = lean_box(0);
x_111 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__44(x_3, x_9, x_109, x_109, x_110, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_111;
}
}
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_9);
x_112 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_113 = 0;
x_114 = lean_box(0);
lean_inc(x_7);
x_115 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__45(x_1, x_2, x_11, x_112, x_113, x_114, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_115, 1);
x_120 = lean_ctor_get(x_115, 0);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_116, 1);
x_123 = lean_ctor_get(x_116, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_117);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_117, 1);
x_126 = lean_ctor_get(x_117, 0);
lean_dec(x_126);
x_127 = lean_ctor_get(x_125, 3);
lean_inc(x_127);
x_128 = lean_array_get_size(x_127);
x_129 = lean_nat_dec_lt(x_10, x_128);
if (x_129 == 0)
{
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_117, 0, x_114);
return x_115;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_le(x_128, x_128);
if (x_130 == 0)
{
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_117, 0, x_114);
return x_115;
}
else
{
size_t x_131; size_t x_132; lean_object* x_133; 
lean_free_object(x_117);
lean_free_object(x_116);
lean_free_object(x_115);
x_131 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_132 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_133 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__46(x_3, x_127, x_131, x_132, x_114, x_4, x_125, x_122, x_7, x_119);
lean_dec(x_127);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_117, 1);
lean_inc(x_134);
lean_dec(x_117);
x_135 = lean_ctor_get(x_134, 3);
lean_inc(x_135);
x_136 = lean_array_get_size(x_135);
x_137 = lean_nat_dec_lt(x_10, x_136);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_114);
lean_ctor_set(x_138, 1, x_134);
lean_ctor_set(x_116, 0, x_138);
return x_115;
}
else
{
uint8_t x_139; 
x_139 = lean_nat_dec_le(x_136, x_136);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_114);
lean_ctor_set(x_140, 1, x_134);
lean_ctor_set(x_116, 0, x_140);
return x_115;
}
else
{
size_t x_141; size_t x_142; lean_object* x_143; 
lean_free_object(x_116);
lean_free_object(x_115);
x_141 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_142 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_143 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__46(x_3, x_135, x_141, x_142, x_114, x_4, x_134, x_122, x_7, x_119);
lean_dec(x_135);
return x_143;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_116, 1);
lean_inc(x_144);
lean_dec(x_116);
x_145 = lean_ctor_get(x_117, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_146 = x_117;
} else {
 lean_dec_ref(x_117);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_145, 3);
lean_inc(x_147);
x_148 = lean_array_get_size(x_147);
x_149 = lean_nat_dec_lt(x_10, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_146)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_146;
}
lean_ctor_set(x_150, 0, x_114);
lean_ctor_set(x_150, 1, x_145);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_144);
lean_ctor_set(x_115, 0, x_151);
return x_115;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_148, x_148);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_146)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_146;
}
lean_ctor_set(x_153, 0, x_114);
lean_ctor_set(x_153, 1, x_145);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_144);
lean_ctor_set(x_115, 0, x_154);
return x_115;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; 
lean_dec(x_146);
lean_free_object(x_115);
x_155 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_156 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_157 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__46(x_3, x_147, x_155, x_156, x_114, x_4, x_145, x_144, x_7, x_119);
lean_dec(x_147);
return x_157;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_158 = lean_ctor_get(x_115, 1);
lean_inc(x_158);
lean_dec(x_115);
x_159 = lean_ctor_get(x_116, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_160 = x_116;
} else {
 lean_dec_ref(x_116);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_117, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_162 = x_117;
} else {
 lean_dec_ref(x_117);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_161, 3);
lean_inc(x_163);
x_164 = lean_array_get_size(x_163);
x_165 = lean_nat_dec_lt(x_10, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_162)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_162;
}
lean_ctor_set(x_166, 0, x_114);
lean_ctor_set(x_166, 1, x_161);
if (lean_is_scalar(x_160)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_160;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_159);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_158);
return x_168;
}
else
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_164, x_164);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_162)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_162;
}
lean_ctor_set(x_170, 0, x_114);
lean_ctor_set(x_170, 1, x_161);
if (lean_is_scalar(x_160)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_160;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_159);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_158);
return x_172;
}
else
{
size_t x_173; size_t x_174; lean_object* x_175; 
lean_dec(x_162);
lean_dec(x_160);
x_173 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_174 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_175 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__46(x_3, x_163, x_173, x_174, x_114, x_4, x_161, x_159, x_7, x_158);
lean_dec(x_163);
return x_175;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_176 = !lean_is_exclusive(x_115);
if (x_176 == 0)
{
return x_115;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_115, 0);
x_178 = lean_ctor_get(x_115, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_115);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__48(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__2(x_1, x_7);
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
x_17 = lean_apply_2(x_5, x_16, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__50___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__50(x_1, x_3, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_9, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__50___lambda__1___boxed), 8, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_updateAndMaterializeCore___spec__40(x_1, x_2, x_12, x_11, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1;
lean_inc(x_3);
x_16 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__48(x_9, x_3, x_15);
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
x_21 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49___rarg(x_20, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__47(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__50(x_1, x_3, x_4, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
lean_ctor_set(x_10, 1, x_13);
lean_ctor_set(x_10, 0, x_15);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_22 = x_10;
} else {
 lean_dec_ref(x_10);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__51(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_array_uget(x_2, x_3);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_7);
lean_inc(x_1);
x_16 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__47(x_1, x_5, x_10, x_15, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_5 = x_19;
x_6 = x_20;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_1);
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
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_box(0);
x_200 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_1);
x_201 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(x_1, x_2, x_199, x_200, x_6);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_array_get_size(x_205);
x_207 = lean_unsigned_to_nat(0u);
x_208 = lean_nat_dec_lt(x_207, x_206);
if (x_208 == 0)
{
lean_dec(x_206);
lean_dec(x_205);
x_7 = x_204;
x_8 = x_203;
goto block_198;
}
else
{
uint8_t x_209; 
x_209 = lean_nat_dec_le(x_206, x_206);
if (x_209 == 0)
{
lean_dec(x_206);
lean_dec(x_205);
x_7 = x_204;
x_8 = x_203;
goto block_198;
}
else
{
size_t x_210; size_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = 0;
x_211 = lean_usize_of_nat(x_206);
lean_dec(x_206);
x_212 = lean_box(0);
lean_inc(x_5);
x_213 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_205, x_210, x_211, x_212, x_5, x_203);
lean_dec(x_205);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_7 = x_204;
x_8 = x_214;
goto block_198;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_3);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_201);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_216 = lean_ctor_get(x_201, 1);
x_217 = lean_ctor_get(x_201, 0);
lean_dec(x_217);
x_218 = lean_ctor_get(x_202, 1);
lean_inc(x_218);
lean_dec(x_202);
x_219 = lean_array_get_size(x_218);
x_220 = lean_unsigned_to_nat(0u);
x_221 = lean_nat_dec_lt(x_220, x_219);
if (x_221 == 0)
{
lean_object* x_222; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_5);
x_222 = lean_box(0);
lean_ctor_set_tag(x_201, 1);
lean_ctor_set(x_201, 0, x_222);
return x_201;
}
else
{
uint8_t x_223; 
x_223 = lean_nat_dec_le(x_219, x_219);
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_5);
x_224 = lean_box(0);
lean_ctor_set_tag(x_201, 1);
lean_ctor_set(x_201, 0, x_224);
return x_201;
}
else
{
size_t x_225; size_t x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
lean_free_object(x_201);
x_225 = 0;
x_226 = lean_usize_of_nat(x_219);
lean_dec(x_219);
x_227 = lean_box(0);
x_228 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_218, x_225, x_226, x_227, x_5, x_216);
lean_dec(x_218);
x_229 = !lean_is_exclusive(x_228);
if (x_229 == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_228, 0);
lean_dec(x_230);
lean_ctor_set_tag(x_228, 1);
lean_ctor_set(x_228, 0, x_227);
return x_228;
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_227);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_233 = lean_ctor_get(x_201, 1);
lean_inc(x_233);
lean_dec(x_201);
x_234 = lean_ctor_get(x_202, 1);
lean_inc(x_234);
lean_dec(x_202);
x_235 = lean_array_get_size(x_234);
x_236 = lean_unsigned_to_nat(0u);
x_237 = lean_nat_dec_lt(x_236, x_235);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_5);
x_238 = lean_box(0);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_233);
return x_239;
}
else
{
uint8_t x_240; 
x_240 = lean_nat_dec_le(x_235, x_235);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_5);
x_241 = lean_box(0);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_233);
return x_242;
}
else
{
size_t x_243; size_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_243 = 0;
x_244 = lean_usize_of_nat(x_235);
lean_dec(x_235);
x_245 = lean_box(0);
x_246 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_234, x_243, x_244, x_245, x_5, x_233);
lean_dec(x_234);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
 lean_ctor_set_tag(x_249, 1);
}
lean_ctor_set(x_249, 0, x_245);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
}
}
block_198:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = l_Lake_Workspace_addPackage(x_10, x_1);
if (x_4 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_updateAndMaterializeCore___spec__8(x_3, x_11, x_12, x_13, x_9, x_5, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 7);
lean_inc(x_16);
x_17 = l_Array_reverse___rarg(x_16);
x_18 = lean_array_size(x_17);
x_19 = 0;
lean_inc(x_5);
lean_inc(x_17);
lean_inc(x_11);
x_20 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14(x_11, x_15, x_18, x_19, x_17, x_9, x_5, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_5);
lean_inc(x_11);
x_26 = l_Lake_Workspace_updateToolchain(x_11, x_24, x_5, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_11, 3);
lean_inc(x_30);
x_31 = lean_array_get_size(x_30);
x_32 = l_Array_zip___rarg(x_17, x_24);
lean_dec(x_24);
lean_dec(x_17);
x_33 = lean_array_get_size(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_33);
lean_dec(x_32);
x_36 = lean_nat_dec_lt(x_31, x_31);
if (x_36 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_31, x_31);
if (x_37 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
size_t x_38; lean_object* x_39; 
lean_free_object(x_26);
lean_free_object(x_21);
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__26(x_3, x_30, x_38, x_38, x_11, x_25, x_5, x_28);
lean_dec(x_30);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_33, x_33);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_33);
lean_dec(x_32);
x_41 = lean_nat_dec_lt(x_31, x_31);
if (x_41 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_31, x_31);
if (x_42 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
size_t x_43; lean_object* x_44; 
lean_free_object(x_26);
lean_free_object(x_21);
x_43 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_44 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__38(x_3, x_30, x_43, x_43, x_11, x_25, x_5, x_28);
lean_dec(x_30);
return x_44;
}
}
}
else
{
size_t x_45; lean_object* x_46; 
lean_dec(x_30);
lean_free_object(x_26);
lean_free_object(x_21);
x_45 = lean_usize_of_nat(x_33);
lean_dec(x_33);
lean_inc(x_5);
lean_inc(x_3);
x_46 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__39(x_3, x_19, x_32, x_19, x_45, x_11, x_25, x_5, x_28);
lean_dec(x_32);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_46, 1);
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
x_53 = lean_ctor_get(x_51, 3);
lean_inc(x_53);
x_54 = lean_array_get_size(x_53);
x_55 = lean_nat_dec_lt(x_31, x_54);
if (x_55 == 0)
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_3);
return x_46;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_54, x_54);
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_3);
return x_46;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
lean_free_object(x_48);
lean_free_object(x_46);
x_57 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_58 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_59 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__51(x_3, x_53, x_57, x_58, x_51, x_52, x_5, x_50);
lean_dec(x_53);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_46, 1);
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_63 = lean_ctor_get(x_61, 3);
lean_inc(x_63);
x_64 = lean_array_get_size(x_63);
x_65 = lean_nat_dec_lt(x_31, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_3);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_46, 0, x_66);
return x_46;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_64, x_64);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_3);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_46, 0, x_68);
return x_46;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; 
lean_free_object(x_46);
x_69 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_70 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_71 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__51(x_3, x_63, x_69, x_70, x_61, x_62, x_5, x_60);
lean_dec(x_63);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_72 = lean_ctor_get(x_46, 0);
x_73 = lean_ctor_get(x_46, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_46);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_74, 3);
lean_inc(x_77);
x_78 = lean_array_get_size(x_77);
x_79 = lean_nat_dec_lt(x_31, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_76)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_76;
}
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_75);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
return x_81;
}
else
{
uint8_t x_82; 
x_82 = lean_nat_dec_le(x_78, x_78);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_76;
}
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_75);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_73);
return x_84;
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; 
lean_dec(x_76);
x_85 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_86 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_87 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__51(x_3, x_77, x_85, x_86, x_74, x_75, x_5, x_73);
lean_dec(x_77);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_46);
if (x_88 == 0)
{
return x_46;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_46, 0);
x_90 = lean_ctor_get(x_46, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_46);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_92 = lean_ctor_get(x_26, 1);
lean_inc(x_92);
lean_dec(x_26);
x_93 = lean_ctor_get(x_11, 3);
lean_inc(x_93);
x_94 = lean_array_get_size(x_93);
x_95 = l_Array_zip___rarg(x_17, x_24);
lean_dec(x_24);
lean_dec(x_17);
x_96 = lean_array_get_size(x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_lt(x_97, x_96);
if (x_98 == 0)
{
uint8_t x_99; 
lean_dec(x_96);
lean_dec(x_95);
x_99 = lean_nat_dec_lt(x_94, x_94);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_21, 0, x_11);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_21);
lean_ctor_set(x_100, 1, x_92);
return x_100;
}
else
{
uint8_t x_101; 
x_101 = lean_nat_dec_le(x_94, x_94);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_21, 0, x_11);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_21);
lean_ctor_set(x_102, 1, x_92);
return x_102;
}
else
{
size_t x_103; lean_object* x_104; 
lean_free_object(x_21);
x_103 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_104 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__26(x_3, x_93, x_103, x_103, x_11, x_25, x_5, x_92);
lean_dec(x_93);
return x_104;
}
}
}
else
{
uint8_t x_105; 
x_105 = lean_nat_dec_le(x_96, x_96);
if (x_105 == 0)
{
uint8_t x_106; 
lean_dec(x_96);
lean_dec(x_95);
x_106 = lean_nat_dec_lt(x_94, x_94);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_21, 0, x_11);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_21);
lean_ctor_set(x_107, 1, x_92);
return x_107;
}
else
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_94, x_94);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_21, 0, x_11);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_21);
lean_ctor_set(x_109, 1, x_92);
return x_109;
}
else
{
size_t x_110; lean_object* x_111; 
lean_free_object(x_21);
x_110 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_111 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__38(x_3, x_93, x_110, x_110, x_11, x_25, x_5, x_92);
lean_dec(x_93);
return x_111;
}
}
}
else
{
size_t x_112; lean_object* x_113; 
lean_dec(x_93);
lean_free_object(x_21);
x_112 = lean_usize_of_nat(x_96);
lean_dec(x_96);
lean_inc(x_5);
lean_inc(x_3);
x_113 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__39(x_3, x_19, x_95, x_19, x_112, x_11, x_25, x_5, x_92);
lean_dec(x_95);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
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
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_117, 3);
lean_inc(x_120);
x_121 = lean_array_get_size(x_120);
x_122 = lean_nat_dec_lt(x_94, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_94);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_119;
}
lean_ctor_set(x_123, 0, x_117);
lean_ctor_set(x_123, 1, x_118);
if (lean_is_scalar(x_116)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_116;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_115);
return x_124;
}
else
{
uint8_t x_125; 
x_125 = lean_nat_dec_le(x_121, x_121);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_94);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_119)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_119;
}
lean_ctor_set(x_126, 0, x_117);
lean_ctor_set(x_126, 1, x_118);
if (lean_is_scalar(x_116)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_116;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_115);
return x_127;
}
else
{
size_t x_128; size_t x_129; lean_object* x_130; 
lean_dec(x_119);
lean_dec(x_116);
x_128 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_129 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_130 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__51(x_3, x_120, x_128, x_129, x_117, x_118, x_5, x_115);
lean_dec(x_120);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_94);
lean_dec(x_5);
lean_dec(x_3);
x_131 = lean_ctor_get(x_113, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_113, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_133 = x_113;
} else {
 lean_dec_ref(x_113);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
}
}
else
{
uint8_t x_135; 
lean_free_object(x_21);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_135 = !lean_is_exclusive(x_26);
if (x_135 == 0)
{
return x_26;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_26, 0);
x_137 = lean_ctor_get(x_26, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_26);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_21, 0);
x_140 = lean_ctor_get(x_21, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_21);
lean_inc(x_5);
lean_inc(x_11);
x_141 = l_Lake_Workspace_updateToolchain(x_11, x_139, x_5, x_22);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_11, 3);
lean_inc(x_144);
x_145 = lean_array_get_size(x_144);
x_146 = l_Array_zip___rarg(x_17, x_139);
lean_dec(x_139);
lean_dec(x_17);
x_147 = lean_array_get_size(x_146);
x_148 = lean_unsigned_to_nat(0u);
x_149 = lean_nat_dec_lt(x_148, x_147);
if (x_149 == 0)
{
uint8_t x_150; 
lean_dec(x_147);
lean_dec(x_146);
x_150 = lean_nat_dec_lt(x_145, x_145);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_3);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_11);
lean_ctor_set(x_151, 1, x_140);
if (lean_is_scalar(x_143)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_143;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_142);
return x_152;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_145, x_145);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_3);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_11);
lean_ctor_set(x_154, 1, x_140);
if (lean_is_scalar(x_143)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_143;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_142);
return x_155;
}
else
{
size_t x_156; lean_object* x_157; 
lean_dec(x_143);
x_156 = lean_usize_of_nat(x_145);
lean_dec(x_145);
x_157 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__26(x_3, x_144, x_156, x_156, x_11, x_140, x_5, x_142);
lean_dec(x_144);
return x_157;
}
}
}
else
{
uint8_t x_158; 
x_158 = lean_nat_dec_le(x_147, x_147);
if (x_158 == 0)
{
uint8_t x_159; 
lean_dec(x_147);
lean_dec(x_146);
x_159 = lean_nat_dec_lt(x_145, x_145);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_3);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_11);
lean_ctor_set(x_160, 1, x_140);
if (lean_is_scalar(x_143)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_143;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_142);
return x_161;
}
else
{
uint8_t x_162; 
x_162 = lean_nat_dec_le(x_145, x_145);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_5);
lean_dec(x_3);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_11);
lean_ctor_set(x_163, 1, x_140);
if (lean_is_scalar(x_143)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_143;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_142);
return x_164;
}
else
{
size_t x_165; lean_object* x_166; 
lean_dec(x_143);
x_165 = lean_usize_of_nat(x_145);
lean_dec(x_145);
x_166 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__38(x_3, x_144, x_165, x_165, x_11, x_140, x_5, x_142);
lean_dec(x_144);
return x_166;
}
}
}
else
{
size_t x_167; lean_object* x_168; 
lean_dec(x_144);
lean_dec(x_143);
x_167 = lean_usize_of_nat(x_147);
lean_dec(x_147);
lean_inc(x_5);
lean_inc(x_3);
x_168 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__39(x_3, x_19, x_146, x_19, x_167, x_11, x_140, x_5, x_142);
lean_dec(x_146);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_174 = x_169;
} else {
 lean_dec_ref(x_169);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_172, 3);
lean_inc(x_175);
x_176 = lean_array_get_size(x_175);
x_177 = lean_nat_dec_lt(x_145, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_145);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_174;
}
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_173);
if (lean_is_scalar(x_171)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_171;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_170);
return x_179;
}
else
{
uint8_t x_180; 
x_180 = lean_nat_dec_le(x_176, x_176);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_145);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_174)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_174;
}
lean_ctor_set(x_181, 0, x_172);
lean_ctor_set(x_181, 1, x_173);
if (lean_is_scalar(x_171)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_171;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_170);
return x_182;
}
else
{
size_t x_183; size_t x_184; lean_object* x_185; 
lean_dec(x_174);
lean_dec(x_171);
x_183 = lean_usize_of_nat(x_145);
lean_dec(x_145);
x_184 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_185 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__51(x_3, x_175, x_183, x_184, x_172, x_173, x_5, x_170);
lean_dec(x_175);
return x_185;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_145);
lean_dec(x_5);
lean_dec(x_3);
x_186 = lean_ctor_get(x_168, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_168, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_188 = x_168;
} else {
 lean_dec_ref(x_168);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_190 = lean_ctor_get(x_141, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_141, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_192 = x_141;
} else {
 lean_dec_ref(x_141);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_194 = !lean_is_exclusive(x_20);
if (x_194 == 0)
{
return x_20;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_20, 0);
x_196 = lean_ctor_get(x_20, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_20);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__3(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__5(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__6(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__7(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__9(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__10(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__11___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__16(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__17(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__18(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__19(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__20(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__21(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__23(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__24(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__25___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__25___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__26(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__28(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__29(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__30(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__31(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__32(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__33(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__35(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__36(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__37___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__37___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__38(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__39(x_1, x_10, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__41(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__42(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__43(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__44(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__45(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__46(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__48___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at_Lake_Workspace_updateAndMaterializeCore___spec__48(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_depCycleError___at_Lake_Workspace_updateAndMaterializeCore___spec__49(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__50___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_Lake_Workspace_updateAndMaterializeCore___spec__50___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__51___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterializeCore___spec__51(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lake_Workspace_updateAndMaterializeCore(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_writeManifest___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 4);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_1, x_11);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_12, 0, x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_dec(x_20);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 2, x_9);
x_21 = lean_array_push(x_5, x_17);
x_3 = x_14;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get_uint8(x_17, sizeof(void*)*5);
x_26 = lean_ctor_get(x_17, 4);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_9);
lean_ctor_set(x_27, 3, x_12);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_25);
x_28 = lean_array_push(x_5, x_27);
x_3 = x_14;
x_5 = x_28;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_10);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_30, sizeof(void*)*5);
x_35 = lean_ctor_get(x_30, 4);
lean_inc(x_35);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 lean_ctor_release(x_30, 4);
 x_36 = x_30;
} else {
 lean_dec_ref(x_30);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 5, 1);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_9);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*5, x_34);
x_38 = lean_array_push(x_5, x_37);
x_3 = x_14;
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
LEAN_EXPORT lean_object* l_Lake_Workspace_writeManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 4);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_System_FilePath_join(x_14, x_15);
lean_dec(x_15);
if (x_8 == 0)
{
lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
x_46 = l_Lake_Workspace_updateToolchain___closed__9;
x_17 = x_46;
goto block_45;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_6, x_6);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_6);
lean_dec(x_5);
x_48 = l_Lake_Workspace_updateToolchain___closed__9;
x_17 = x_48;
goto block_45;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_51 = l_Lake_Workspace_updateToolchain___closed__9;
x_52 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_writeManifest___spec__1(x_2, x_5, x_49, x_50, x_51);
lean_dec(x_5);
x_17 = x_52;
goto block_45;
}
}
block_45:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lake_defaultLakeDir;
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_13);
lean_ctor_set(x_19, 3, x_17);
x_20 = l_Lake_Manifest_saveToFile(x_19, x_16, x_4);
lean_dec(x_16);
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
lean_ctor_set(x_23, 1, x_3);
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
lean_ctor_set(x_26, 1, x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_io_error_to_string(x_29);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_get_size(x_3);
x_34 = lean_array_push(x_3, x_32);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_io_error_to_string(x_36);
x_39 = 3;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_array_get_size(x_3);
x_42 = lean_array_push(x_3, x_40);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_writeManifest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_writeManifest___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_writeManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_writeManifest(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_runPostUpdateHooks___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Lake_Package_runPostUpdateHooks___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": running post-update hooks", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 15);
lean_inc(x_5);
x_6 = l_Array_isEmpty___rarg(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 1;
x_10 = l_Lake_loadDepPackage___closed__1;
lean_inc(x_8);
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lake_Package_runPostUpdateHooks___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = 1;
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = lean_array_push(x_3, x_17);
x_19 = lean_array_get_size(x_5);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_19, x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_31 = lean_box(0);
x_32 = l_Array_foldlMUnsafe_fold___at_Lake_Package_runPostUpdateHooks___spec__1(x_1, x_8, x_5, x_29, x_30, x_31, x_2, x_18, x_4);
lean_dec(x_5);
lean_dec(x_8);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_4);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Package_runPostUpdateHooks___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Package_runPostUpdateHooks___spec__1(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_2);
x_16 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_5);
x_17 = l_Lake_Package_runPostUpdateHooks(x_15, x_5, x_16, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
x_8 = x_20;
x_9 = x_19;
goto block_13;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
x_8 = x_20;
x_9 = x_19;
goto block_13;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_28 = lean_box(0);
lean_inc(x_6);
x_29 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_21, x_26, x_27, x_28, x_6, x_19);
lean_dec(x_21);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_8 = x_20;
x_9 = x_30;
goto block_13;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_17, 1);
x_33 = lean_ctor_get(x_17, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_array_get_size(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_lt(x_36, x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_6);
x_38 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_38);
return x_17;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_35, x_35);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_6);
x_40 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_40);
return x_17;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_free_object(x_17);
x_41 = 0;
x_42 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_43 = lean_box(0);
x_44 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_34, x_41, x_42, x_43, x_6, x_32);
lean_dec(x_34);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_dec(x_17);
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_dec(x_18);
x_51 = lean_array_get_size(x_50);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_lt(x_52, x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_6);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_51, x_51);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_6);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_61 = lean_box(0);
x_62 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_50, x_59, x_60, x_61, x_6, x_49);
lean_dec(x_50);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_6);
lean_dec(x_5);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_7);
return x_66;
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lake_Workspace_updateAndMaterializeCore(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_34 = l_Lake_Workspace_updateToolchain___closed__9;
lean_inc(x_11);
x_35 = l_Lake_Workspace_writeManifest(x_11, x_12, x_34, x_9);
lean_dec(x_12);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_array_get_size(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_lt(x_40, x_39);
if (x_41 == 0)
{
lean_dec(x_39);
lean_dec(x_38);
x_13 = x_37;
goto block_33;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_39, x_39);
if (x_42 == 0)
{
lean_dec(x_39);
lean_dec(x_38);
x_13 = x_37;
goto block_33;
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = 0;
x_44 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_45 = lean_box(0);
lean_inc(x_5);
x_46 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_38, x_43, x_44, x_45, x_5, x_37);
lean_dec(x_38);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_13 = x_47;
goto block_33;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_11);
lean_dec(x_10);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_35, 1);
x_50 = lean_ctor_get(x_35, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
x_52 = lean_array_get_size(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_lt(x_53, x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_5);
x_55 = lean_box(0);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_55);
return x_35;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_52, x_52);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_5);
x_57 = lean_box(0);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_57);
return x_35;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_free_object(x_35);
x_58 = 0;
x_59 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_60 = lean_box(0);
x_61 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_51, x_58, x_59, x_60, x_5, x_49);
lean_dec(x_51);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_35, 1);
lean_inc(x_66);
lean_dec(x_35);
x_67 = lean_ctor_get(x_36, 1);
lean_inc(x_67);
lean_dec(x_36);
x_68 = lean_array_get_size(x_67);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_lt(x_69, x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_68, x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_66);
return x_75;
}
else
{
size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = 0;
x_77 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_78 = lean_box(0);
x_79 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_67, x_76, x_77, x_78, x_5, x_66);
lean_dec(x_67);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
block_33:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 3);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_5);
if (lean_is_scalar(x_10)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_10;
}
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_5);
if (lean_is_scalar(x_10)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_10;
}
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = lean_box(0);
lean_inc(x_11);
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1(x_14, x_21, x_22, x_23, x_11, x_5, x_13);
lean_dec(x_14);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_11);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_5);
x_83 = !lean_is_exclusive(x_7);
if (x_83 == 0)
{
return x_7;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_7, 0);
x_85 = lean_ctor_get(x_7, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_7);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateAndMaterialize___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lake_Workspace_updateAndMaterialize(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("manifest out of date: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git revision", 12, 12);
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
x_1 = lean_mk_string_unchecked(" of dependency '", 16, 16);
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
x_1 = lean_mk_string_unchecked("' changed; use `lake update ", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` to update it", 14, 14);
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
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_12 = 1;
x_13 = l_Lake_loadDepPackage___closed__1;
x_14 = l_Lean_Name_toString(x_3, x_12, x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__5;
x_16 = lean_string_append(x_15, x_14);
x_17 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_14);
lean_dec(x_14);
x_20 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7;
x_21 = lean_string_append(x_19, x_20);
x_22 = 2;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = lean_array_push(x_5, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("source kind (git/path)", 22, 22);
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
x_1 = lean_mk_string_unchecked("git url", 7, 7);
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
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_array_uget(x_2, x_3);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
x_8 = x_20;
x_9 = x_7;
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_1, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
x_8 = x_25;
x_9 = x_7;
goto block_15;
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_26, 4);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
x_8 = x_29;
x_9 = x_7;
goto block_15;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_27);
x_30 = 1;
x_31 = l_Lake_loadDepPackage___closed__1;
x_32 = l_Lean_Name_toString(x_22, x_30, x_31);
x_33 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__3;
x_34 = lean_string_append(x_33, x_32);
x_35 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_32);
lean_dec(x_32);
x_38 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7;
x_39 = lean_string_append(x_37, x_38);
x_40 = 2;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_push(x_6, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_8 = x_44;
x_9 = x_7;
goto block_15;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_23, 0);
lean_inc(x_45);
lean_dec(x_23);
x_46 = lean_ctor_get(x_45, 4);
lean_inc(x_46);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_46);
lean_dec(x_21);
x_47 = 1;
x_48 = l_Lake_loadDepPackage___closed__1;
x_49 = l_Lean_Name_toString(x_22, x_47, x_48);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__3;
x_51 = lean_string_append(x_50, x_49);
x_52 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_53, x_49);
lean_dec(x_49);
x_55 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7;
x_56 = lean_string_append(x_54, x_55);
x_57 = 2;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = lean_array_push(x_6, x_58);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_8 = x_61;
x_9 = x_7;
goto block_15;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_21, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
lean_dec(x_21);
x_64 = lean_ctor_get(x_46, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_46, 2);
lean_inc(x_65);
lean_dec(x_46);
x_66 = lean_string_dec_eq(x_62, x_64);
lean_dec(x_64);
lean_dec(x_62);
x_67 = l_instDecidableNot___rarg(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_box(0);
x_69 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1(x_63, x_65, x_22, x_68, x_6, x_7);
lean_dec(x_65);
lean_dec(x_63);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_8 = x_70;
x_9 = x_71;
goto block_15;
}
else
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_72 = 1;
x_73 = l_Lake_loadDepPackage___closed__1;
lean_inc(x_22);
x_74 = l_Lean_Name_toString(x_22, x_72, x_73);
x_75 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___closed__6;
x_76 = lean_string_append(x_75, x_74);
x_77 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__6;
x_78 = lean_string_append(x_76, x_77);
x_79 = lean_string_append(x_78, x_74);
lean_dec(x_74);
x_80 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1___closed__7;
x_81 = lean_string_append(x_79, x_80);
x_82 = 2;
x_83 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_82);
x_84 = lean_array_push(x_6, x_83);
x_85 = lean_box(0);
x_86 = l_Array_foldlMUnsafe_fold___at_Lake_validateManifest___spec__1___lambda__1(x_63, x_65, x_22, x_85, x_84, x_7);
lean_dec(x_65);
lean_dec(x_63);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_8 = x_87;
x_9 = x_88;
goto block_15;
}
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_5);
lean_ctor_set(x_89, 1, x_6);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_7);
return x_90;
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
x_1 = lean_mk_string_unchecked("missing manifest; use `lake update` to generate one", 51, 51);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_6);
x_12 = lean_apply_5(x_1, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_7 = x_18;
x_8 = x_16;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_9);
return x_40;
}
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dependency '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' of '", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' not in manifest; this suggests that the manifest is corrupt; use `lake update` to generate a new, complete file (warning: this will update ALL workspace dependencies)", 168, 168);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' not in manifest; use `lake update ", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` to add it", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_2, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
lean_dec(x_3);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_9, 0);
lean_inc(x_49);
lean_dec(x_9);
x_50 = lean_ctor_get(x_49, 2);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 2);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_name_eq(x_48, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_53 = 1;
x_54 = l_Lake_loadDepPackage___closed__1;
x_55 = l_Lean_Name_toString(x_45, x_53, x_54);
x_56 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__1;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lean_Name_toString(x_48, x_53, x_54);
x_61 = lean_string_append(x_59, x_60);
lean_dec(x_60);
x_62 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__3;
x_63 = lean_string_append(x_61, x_62);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_10);
x_67 = lean_array_push(x_10, x_65);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_12 = x_68;
x_13 = x_11;
goto block_44;
}
else
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_48);
x_69 = 1;
x_70 = l_Lake_loadDepPackage___closed__1;
x_71 = l_Lean_Name_toString(x_45, x_69, x_70);
x_72 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__1;
x_73 = lean_string_append(x_72, x_71);
x_74 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__4;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_string_append(x_75, x_71);
lean_dec(x_71);
x_77 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__5;
x_78 = lean_string_append(x_76, x_77);
x_79 = 3;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_array_get_size(x_10);
x_82 = lean_array_push(x_10, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_12 = x_83;
x_13 = x_11;
goto block_44;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_45);
lean_dec(x_3);
x_84 = lean_ctor_get(x_46, 0);
lean_inc(x_84);
lean_dec(x_46);
x_85 = lean_ctor_get(x_9, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_9, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lake_PackageEntry_materialize(x_84, x_85, x_87, x_4, x_10, x_11);
lean_dec(x_85);
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
x_93 = lean_ctor_get(x_1, 4);
lean_inc(x_93);
lean_dec(x_1);
x_94 = l_Lake_loadDepPackage(x_91, x_93, x_5, x_6, x_9, x_92, x_90);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_12 = x_95;
x_13 = x_96;
goto block_44;
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_94, 0);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_94);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; uint8_t x_102; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_101 = lean_ctor_get(x_88, 1);
lean_inc(x_101);
lean_dec(x_88);
x_102 = !lean_is_exclusive(x_89);
if (x_102 == 0)
{
x_12 = x_89;
x_13 = x_101;
goto block_44;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_89, 0);
x_104 = lean_ctor_get(x_89, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_89);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_12 = x_105;
x_13 = x_101;
goto block_44;
}
}
}
block_44:
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lake_Workspace_addPackage(x_17, x_18);
x_20 = lean_box(0);
lean_ctor_set(x_15, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = l_Lake_Workspace_addPackage(x_22, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_12, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_13);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_33 = l_Lake_Workspace_addPackage(x_30, x_31);
x_34 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_13);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_13);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_12);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_13);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_name_eq(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = 1;
x_19 = l_Lake_loadDepPackage___closed__1;
x_20 = l_Lean_Name_toString(x_13, x_18, x_19);
x_21 = l_Lake_depCycleError___rarg___lambda__1___closed__2;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_get_size(x_10);
x_28 = lean_array_push(x_10, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_11);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_7, x_8);
if (x_14 == 0)
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_15 = 1;
x_16 = lean_usize_sub(x_7, x_15);
x_17 = lean_array_uget(x_6, x_16);
x_18 = lean_ctor_get(x_11, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_5);
x_22 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__2(x_17, x_4, x_5, x_3, x_1, x_2, x_21, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_7 = x_16;
x_9 = x_27;
x_11 = x_28;
x_12 = x_26;
x_13 = x_25;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_22, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_22, 0, x_35);
return x_22;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_39 = x_23;
} else {
 lean_dec_ref(x_23);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_22);
if (x_42 == 0)
{
return x_22;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_22, 0);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_22);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_20);
lean_dec(x_17);
x_46 = lean_box(0);
x_7 = x_16;
x_9 = x_46;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_11);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_12);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_13);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_6);
x_12 = lean_apply_5(x_1, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_7 = x_18;
x_8 = x_16;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_9);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_6);
x_12 = lean_apply_5(x_1, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_7 = x_18;
x_8 = x_16;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_9);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_7, x_8);
if (x_14 == 0)
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_15 = 1;
x_16 = lean_usize_sub(x_7, x_15);
x_17 = lean_array_uget(x_6, x_16);
x_18 = lean_ctor_get(x_11, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_5);
x_22 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__2(x_17, x_4, x_5, x_3, x_1, x_2, x_21, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_7 = x_16;
x_9 = x_27;
x_11 = x_28;
x_12 = x_26;
x_13 = x_25;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_22, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_22, 0, x_35);
return x_22;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_39 = x_23;
} else {
 lean_dec_ref(x_23);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_22);
if (x_42 == 0)
{
return x_22;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_22, 0);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_22);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_20);
lean_dec(x_17);
x_46 = lean_box(0);
x_7 = x_16;
x_9 = x_46;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_11);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_12);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_13);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_6);
x_12 = lean_apply_5(x_1, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_7 = x_18;
x_8 = x_16;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_9);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_materializeDeps___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 3);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_ctor_get(x_5, 7);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_le(x_14, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_14);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_nat_dec_lt(x_12, x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_12, x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
else
{
size_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_29 = lean_box(0);
x_30 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__2(x_6, x_11, x_28, x_28, x_29, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_30;
}
}
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
x_31 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_32 = 0;
x_33 = lean_box(0);
x_34 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3(x_1, x_2, x_3, x_4, x_5, x_13, x_31, x_32, x_33, x_7, x_8, x_9, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_ctor_get(x_34, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_35, 1);
x_42 = lean_ctor_get(x_35, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_36, 1);
x_45 = lean_ctor_get(x_36, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_44, 3);
lean_inc(x_46);
x_47 = lean_array_get_size(x_46);
x_48 = lean_nat_dec_lt(x_12, x_47);
if (x_48 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_36, 0, x_33);
return x_34;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_47, x_47);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_36, 0, x_33);
return x_34;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_34);
x_50 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_51 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_52 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(x_6, x_46, x_50, x_51, x_33, x_7, x_44, x_41, x_38);
lean_dec(x_46);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_ctor_get(x_53, 3);
lean_inc(x_54);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_12, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_35, 0, x_57);
return x_34;
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
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_33);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_35, 0, x_59);
return x_34;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
lean_free_object(x_35);
lean_free_object(x_34);
x_60 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_61 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_62 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(x_6, x_54, x_60, x_61, x_33, x_7, x_53, x_41, x_38);
lean_dec(x_54);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_35, 1);
lean_inc(x_63);
lean_dec(x_35);
x_64 = lean_ctor_get(x_36, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_65 = x_36;
} else {
 lean_dec_ref(x_36);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_64, 3);
lean_inc(x_66);
x_67 = lean_array_get_size(x_66);
x_68 = lean_nat_dec_lt(x_12, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_65;
}
lean_ctor_set(x_69, 0, x_33);
lean_ctor_set(x_69, 1, x_64);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
lean_ctor_set(x_34, 0, x_70);
return x_34;
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_le(x_67, x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_65)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_65;
}
lean_ctor_set(x_72, 0, x_33);
lean_ctor_set(x_72, 1, x_64);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_63);
lean_ctor_set(x_34, 0, x_73);
return x_34;
}
else
{
size_t x_74; size_t x_75; lean_object* x_76; 
lean_dec(x_65);
lean_free_object(x_34);
x_74 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_75 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_76 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(x_6, x_66, x_74, x_75, x_33, x_7, x_64, x_63, x_38);
lean_dec(x_66);
return x_76;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_77 = lean_ctor_get(x_34, 1);
lean_inc(x_77);
lean_dec(x_34);
x_78 = lean_ctor_get(x_35, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_79 = x_35;
} else {
 lean_dec_ref(x_35);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_36, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_81 = x_36;
} else {
 lean_dec_ref(x_36);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_80, 3);
lean_inc(x_82);
x_83 = lean_array_get_size(x_82);
x_84 = lean_nat_dec_lt(x_12, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_33);
lean_ctor_set(x_85, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_79;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_78);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_77);
return x_87;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_83, x_83);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_81)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_81;
}
lean_ctor_set(x_89, 0, x_33);
lean_ctor_set(x_89, 1, x_80);
if (lean_is_scalar(x_79)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_79;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_78);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_77);
return x_91;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; 
lean_dec(x_81);
lean_dec(x_79);
x_92 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_93 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_94 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(x_6, x_82, x_92, x_93, x_33, x_7, x_80, x_78, x_77);
lean_dec(x_82);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_95 = !lean_is_exclusive(x_34);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_34, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_35);
if (x_97 == 0)
{
return x_34;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_35, 0);
x_99 = lean_ctor_get(x_35, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_35);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_34, 0, x_100);
return x_34;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_34, 1);
lean_inc(x_101);
lean_dec(x_34);
x_102 = lean_ctor_get(x_35, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_35, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_104 = x_35;
} else {
 lean_dec_ref(x_35);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_107 = !lean_is_exclusive(x_34);
if (x_107 == 0)
{
return x_34;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_34, 0);
x_109 = lean_ctor_get(x_34, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_34);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_nat_dec_lt(x_111, x_14);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_113 = lean_nat_dec_lt(x_12, x_12);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_8);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_9);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_10);
return x_117;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_12, x_12);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_8);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_9);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_10);
return x_122;
}
else
{
size_t x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_124 = lean_box(0);
x_125 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__5(x_6, x_11, x_123, x_123, x_124, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_125;
}
}
}
else
{
size_t x_126; size_t x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_11);
x_126 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_127 = 0;
x_128 = lean_box(0);
x_129 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__6(x_1, x_2, x_3, x_4, x_5, x_13, x_126, x_127, x_128, x_7, x_8, x_9, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = !lean_is_exclusive(x_129);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_129, 1);
x_134 = lean_ctor_get(x_129, 0);
lean_dec(x_134);
x_135 = !lean_is_exclusive(x_130);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_130, 1);
x_137 = lean_ctor_get(x_130, 0);
lean_dec(x_137);
x_138 = !lean_is_exclusive(x_131);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_131, 1);
x_140 = lean_ctor_get(x_131, 0);
lean_dec(x_140);
x_141 = lean_ctor_get(x_139, 3);
lean_inc(x_141);
x_142 = lean_array_get_size(x_141);
x_143 = lean_nat_dec_lt(x_12, x_142);
if (x_143 == 0)
{
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_131, 0, x_128);
return x_129;
}
else
{
uint8_t x_144; 
x_144 = lean_nat_dec_le(x_142, x_142);
if (x_144 == 0)
{
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_131, 0, x_128);
return x_129;
}
else
{
size_t x_145; size_t x_146; lean_object* x_147; 
lean_free_object(x_131);
lean_free_object(x_130);
lean_free_object(x_129);
x_145 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_146 = lean_usize_of_nat(x_142);
lean_dec(x_142);
x_147 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__7(x_6, x_141, x_145, x_146, x_128, x_7, x_139, x_136, x_133);
lean_dec(x_141);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = lean_ctor_get(x_131, 1);
lean_inc(x_148);
lean_dec(x_131);
x_149 = lean_ctor_get(x_148, 3);
lean_inc(x_149);
x_150 = lean_array_get_size(x_149);
x_151 = lean_nat_dec_lt(x_12, x_150);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_128);
lean_ctor_set(x_152, 1, x_148);
lean_ctor_set(x_130, 0, x_152);
return x_129;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_150, x_150);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_128);
lean_ctor_set(x_154, 1, x_148);
lean_ctor_set(x_130, 0, x_154);
return x_129;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; 
lean_free_object(x_130);
lean_free_object(x_129);
x_155 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_156 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_157 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__7(x_6, x_149, x_155, x_156, x_128, x_7, x_148, x_136, x_133);
lean_dec(x_149);
return x_157;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_130, 1);
lean_inc(x_158);
lean_dec(x_130);
x_159 = lean_ctor_get(x_131, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_160 = x_131;
} else {
 lean_dec_ref(x_131);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_159, 3);
lean_inc(x_161);
x_162 = lean_array_get_size(x_161);
x_163 = lean_nat_dec_lt(x_12, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_160)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_160;
}
lean_ctor_set(x_164, 0, x_128);
lean_ctor_set(x_164, 1, x_159);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_158);
lean_ctor_set(x_129, 0, x_165);
return x_129;
}
else
{
uint8_t x_166; 
x_166 = lean_nat_dec_le(x_162, x_162);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_160)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_160;
}
lean_ctor_set(x_167, 0, x_128);
lean_ctor_set(x_167, 1, x_159);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_158);
lean_ctor_set(x_129, 0, x_168);
return x_129;
}
else
{
size_t x_169; size_t x_170; lean_object* x_171; 
lean_dec(x_160);
lean_free_object(x_129);
x_169 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_170 = lean_usize_of_nat(x_162);
lean_dec(x_162);
x_171 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__7(x_6, x_161, x_169, x_170, x_128, x_7, x_159, x_158, x_133);
lean_dec(x_161);
return x_171;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_172 = lean_ctor_get(x_129, 1);
lean_inc(x_172);
lean_dec(x_129);
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
x_177 = lean_ctor_get(x_175, 3);
lean_inc(x_177);
x_178 = lean_array_get_size(x_177);
x_179 = lean_nat_dec_lt(x_12, x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_176)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_176;
}
lean_ctor_set(x_180, 0, x_128);
lean_ctor_set(x_180, 1, x_175);
if (lean_is_scalar(x_174)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_174;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_173);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_172);
return x_182;
}
else
{
uint8_t x_183; 
x_183 = lean_nat_dec_le(x_178, x_178);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_176)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_176;
}
lean_ctor_set(x_184, 0, x_128);
lean_ctor_set(x_184, 1, x_175);
if (lean_is_scalar(x_174)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_174;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_173);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_172);
return x_186;
}
else
{
size_t x_187; size_t x_188; lean_object* x_189; 
lean_dec(x_176);
lean_dec(x_174);
x_187 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_188 = lean_usize_of_nat(x_178);
lean_dec(x_178);
x_189 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__7(x_6, x_177, x_187, x_188, x_128, x_7, x_175, x_173, x_172);
lean_dec(x_177);
return x_189;
}
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_190 = !lean_is_exclusive(x_129);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_129, 0);
lean_dec(x_191);
x_192 = !lean_is_exclusive(x_130);
if (x_192 == 0)
{
return x_129;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_130, 0);
x_194 = lean_ctor_get(x_130, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_130);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_129, 0, x_195);
return x_129;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_196 = lean_ctor_get(x_129, 1);
lean_inc(x_196);
lean_dec(x_129);
x_197 = lean_ctor_get(x_130, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_130, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_199 = x_130;
} else {
 lean_dec_ref(x_130);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_196);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_202 = !lean_is_exclusive(x_129);
if (x_202 == 0)
{
return x_129;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_129, 0);
x_204 = lean_ctor_get(x_129, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_129);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___at_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___spec__2(x_1, x_6);
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
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11(x_1, x_2, x_3, x_4, x_6, x_5, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_11, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_box(x_2);
lean_inc(x_13);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11___lambda__1___boxed), 10, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_13);
x_16 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_materializeDeps___spec__1(x_1, x_2, x_3, x_4, x_5, x_15, x_13, x_7, x_8, x_9);
lean_dec(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1;
lean_inc(x_6);
x_19 = l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__9(x_11, x_6, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_17);
x_23 = l_List_appendTR___rarg(x_21, x_22);
x_24 = l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10___rarg(x_23, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_materializeDeps___spec__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11(x_1, x_2, x_3, x_4, x_6, x_7, x_5, x_8, x_9);
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
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_23 = x_11;
} else {
 lean_dec_ref(x_11);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_10, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_10, 0, x_32);
return x_10;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
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
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
return x_10;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__13(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 7);
lean_inc(x_15);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_14, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_16 = x_45;
goto block_43;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_8, 0);
lean_inc(x_46);
lean_dec(x_8);
x_16 = x_46;
goto block_43;
}
block_43:
{
lean_object* x_17; 
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
x_17 = x_9;
goto block_38;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_11, x_11);
if (x_39 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
x_17 = x_9;
goto block_38;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_42 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__12(x_10, x_40, x_41, x_9);
lean_dec(x_10);
x_17 = x_42;
goto block_38;
}
}
block_38:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lake_validateManifest(x_17, x_15, x_6, x_7);
lean_dec(x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lake_Workspace_addPackage(x_14, x_2);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_box(0);
x_25 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_materializeDeps___spec__8(x_3, x_4, x_16, x_17, x_22, x_23, x_24, x_21, x_20);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("manifest out of date: packages directory changed; use `lake update` to rebuild the manifest (warning: this will update ALL workspace dependencies)", 146, 146);
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
x_15 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__13(x_9, x_14);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__2(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3(x_1, x_14, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__4(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__5(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__6(x_1, x_14, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__7(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_materializeDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at_Lake_Workspace_materializeDeps___spec__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_partition_loop___at_Lake_Workspace_materializeDeps___spec__9(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_depCycleError___at_Lake_Workspace_materializeDeps___spec__10(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_recFetch___at_Lake_Workspace_materializeDeps___spec__11(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_materializeDeps___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at_Lake_Workspace_materializeDeps___spec__8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__12(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_Workspace_materializeDeps___spec__13(x_1, x_2);
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
l_Lake_loadDepPackage___closed__1 = _init_l_Lake_loadDepPackage___closed__1();
lean_mark_persistent(l_Lake_loadDepPackage___closed__1);
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
l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__1);
l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__2 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__2();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___rarg___lambda__4___closed__2);
l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__6___closed__1);
l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__7___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__7___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___rarg___lambda__7___closed__1);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__1___closed__1);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__1);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__2 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__2();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__2);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__3 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__3();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__3);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lambda__2___closed__4);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1);
l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1);
l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__2 = _init_l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__2();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__2);
l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__1);
l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__1);
l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__2 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__2();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__1___closed__2);
l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__1);
l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__2 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__2();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___lambda__2___closed__2);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3);
l_Lake_restartCode = _init_l_Lake_restartCode();
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_updateToolchain___spec__1___closed__2);
l_Lake_Workspace_updateToolchain___lambda__1___closed__1 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__1);
l_Lake_Workspace_updateToolchain___lambda__1___closed__2 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__2);
l_Lake_Workspace_updateToolchain___lambda__1___closed__3 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__3);
l_Lake_Workspace_updateToolchain___lambda__1___closed__4 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__4();
l_Lake_Workspace_updateToolchain___lambda__1___closed__5 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__5);
l_Lake_Workspace_updateToolchain___lambda__1___closed__6 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__6);
l_Lake_Workspace_updateToolchain___lambda__1___closed__7 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__7();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__7);
l_Lake_Workspace_updateToolchain___lambda__1___closed__8 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__8();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__8);
l_Lake_Workspace_updateToolchain___lambda__1___closed__9 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__9();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__9);
l_Lake_Workspace_updateToolchain___lambda__1___closed__10 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__10();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__10);
l_Lake_Workspace_updateToolchain___lambda__1___closed__11 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__11();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__11);
l_Lake_Workspace_updateToolchain___lambda__1___closed__12 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__12();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__12);
l_Lake_Workspace_updateToolchain___lambda__1___closed__13 = _init_l_Lake_Workspace_updateToolchain___lambda__1___closed__13();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___lambda__1___closed__13);
l_Lake_Workspace_updateToolchain___closed__1 = _init_l_Lake_Workspace_updateToolchain___closed__1();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__1);
l_Lake_Workspace_updateToolchain___closed__2 = _init_l_Lake_Workspace_updateToolchain___closed__2();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__2);
l_Lake_Workspace_updateToolchain___closed__3 = _init_l_Lake_Workspace_updateToolchain___closed__3();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__3);
l_Lake_Workspace_updateToolchain___closed__4 = _init_l_Lake_Workspace_updateToolchain___closed__4();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__4);
l_Lake_Workspace_updateToolchain___closed__5 = _init_l_Lake_Workspace_updateToolchain___closed__5();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__5);
l_Lake_Workspace_updateToolchain___closed__6 = _init_l_Lake_Workspace_updateToolchain___closed__6();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__6);
l_Lake_Workspace_updateToolchain___closed__7 = _init_l_Lake_Workspace_updateToolchain___closed__7();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__7);
l_Lake_Workspace_updateToolchain___closed__8 = _init_l_Lake_Workspace_updateToolchain___closed__8();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__8);
l_Lake_Workspace_updateToolchain___closed__9 = _init_l_Lake_Workspace_updateToolchain___closed__9();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__9);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__1);
l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_Workspace_updateAndMaterializeCore___spec__14___closed__2);
l_Lake_Package_runPostUpdateHooks___closed__1 = _init_l_Lake_Package_runPostUpdateHooks___closed__1();
lean_mark_persistent(l_Lake_Package_runPostUpdateHooks___closed__1);
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
l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__1 = _init_l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__1);
l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__2 = _init_l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__2);
l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__3 = _init_l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__3);
l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__4 = _init_l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__4();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__4);
l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__5 = _init_l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__5();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at_Lake_Workspace_materializeDeps___spec__3___lambda__1___closed__5);
l_Lake_Workspace_materializeDeps___closed__1 = _init_l_Lake_Workspace_materializeDeps___closed__1();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___closed__1);
l_Lake_Workspace_materializeDeps___closed__2 = _init_l_Lake_Workspace_materializeDeps___closed__2();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

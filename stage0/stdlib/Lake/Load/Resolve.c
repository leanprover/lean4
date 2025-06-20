// Lean compiler output
// Module: Lake.Load.Resolve
// Imports: Lake.Config.Monad Lake.Util.StoreInsts Lake.Build.Topological Lake.Load.Materialize Lake.Load.Package
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_runPostUpdateHooks___closed__0;
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_writeManifest_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___closed__4;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__17;
static lean_object* l_Lake_Workspace_updateToolchain___closed__13;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep___closed__0;
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint8_t l_Lean_NameMap_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___at___Lake_Workspace_updateAndMaterializeCore_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___at___Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___Lake_Workspace_updateAndMaterializeCore___elam__3_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadDepPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__20;
LEAN_EXPORT lean_object* l_Lake_loadDepPackage___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___at___Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__6;
LEAN_EXPORT lean_object* l_Lake_stdMismatchError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__7;
static uint8_t l_Lake_Workspace_updateToolchain___closed__3;
lean_object* l_Lake_instMonadErrorLoggerIO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___elam__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__5___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__3;
LEAN_EXPORT lean_object* l_Lake_UpdateT_run(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Option_decEqOption___redArg____x40_Init_Data_Option_Basic___hyg_5_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__4;
static lean_object* l_Lake_Workspace_updateToolchain___closed__10;
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ResolveT_run___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__16;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_validateManifest___elam__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_DepStackT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at___Lean_Environment_realizeConst_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks___elam__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_decEqToolchainVer____x40_Lake_Util_Version___hyg_1773_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdMismatchError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___at___Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___at___Lake_Workspace_updateAndMaterializeCore_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__1;
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Workspace_updateAndMaterializeCore_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks___elam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_validateManifest___elam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__0;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___closed__0;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_validateManifest___elam__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___elam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks___at___Lake_Workspace_updateAndMaterialize___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_depCycleError___redArg___closed__0;
uint8_t l_Lake_ToolchainVer_decLe(lean_object*, lean_object*);
lean_object* l_Lake_ToolchainVer_toString(lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___elam__0___closed__0;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___elam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_validateManifest___elam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_runPostUpdateHooks_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_ToolchainVer_decLt(lean_object*, lean_object*);
lean_object* l_Lean_NameMap_toJson___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_472__spec__0(lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___elam__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___closed__2;
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__9;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_validateManifest___elam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_UpdateT_run___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___elam__4___closed__4;
lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2;
static lean_object* l_Lake_Workspace_updateToolchain___closed__14;
extern lean_object* l_Lake_Env_noToolchainVars;
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___elam__4___closed__0;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Workspace_updateAndMaterializeCore_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___lam__0(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__5;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_restartCode;
static lean_object* l_Lake_Workspace_updateToolchain___closed__12;
LEAN_EXPORT uint8_t l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_validateManifest_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instToString;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__11;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_writeManifest___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___elam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__1;
lean_object* l_Lake_recFetch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__8;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0;
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_save(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__4;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_validateManifest___elam__1___redArg___closed__2;
static size_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8;
static uint8_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7;
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks___elam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_loadDepPackage___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_Workspace_materializeDeps_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DepStackT_run___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__0;
static lean_object* l_Lake_Workspace_materializeDeps___elam__4___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_validateManifest___elam__0___closed__3;
lean_object* l_StateT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0___lam__5___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_validateManifest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadDepPackage(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__19;
LEAN_EXPORT lean_object* l_Lake_Workspace_writeManifest___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__18;
lean_object* l_String_intercalate(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__0;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___elam__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_depCycleError___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_loadDepPackage___lam__0(uint8_t, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___closed__3;
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__5___boxed__const__1;
static lean_object* l_Lake_Workspace_updateToolchain___closed__2;
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__5;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9;
lean_object* l_List_partition_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdMismatchError___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__15;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Workspace_materializeDeps___lam__1(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__2(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lake_formatCycle___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__21;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ResolveT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___elam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateToolchain___closed__5;
static lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateAndMaterializeCore___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_writeManifest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadDepPackage___closed__1;
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___lam__0(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__0;
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_Workspace_materializeDeps_spec__10(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_materializeDeps___elam__4___closed__1;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_writeManifest(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1;
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___Lake_Workspace_updateAndMaterializeCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_stdMismatchError___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the 'std' package has been renamed to '", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' and moved to the\n'leanprover-community' organization; downstream packages which wish to\nupdate to the new std should replace\n\n  require std from\n    git \"https://github.com/leanprover/std4\"", 191, 191);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nin their Lake configuration file with\n\n  require ", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" from\n    git \"https://github.com/leanprover-community/", 55, 55);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_stdMismatchError___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdMismatchError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_3 = l_Lake_stdMismatchError___closed__0;
x_4 = lean_string_append(x_3, x_1);
x_5 = l_Lake_stdMismatchError___closed__1;
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_string_append(x_6, x_2);
x_8 = l_Lake_stdMismatchError___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_1);
x_11 = l_Lake_stdMismatchError___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_1);
x_14 = l_Lake_stdMismatchError___closed__4;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_2);
x_17 = l_Lake_stdMismatchError___closed__5;
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
LEAN_EXPORT uint8_t l_Lake_loadDepPackage___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lake_loadDepPackage___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_loadDepPackage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package directory not found: ", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadDepPackage(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_10);
x_14 = l_Lake_joinRelative(x_10, x_11);
lean_inc(x_14);
x_15 = l_Lake_resolvePath(x_14, x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 2);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_box(0);
x_23 = lean_alloc_closure((void*)(l_Lake_loadDepPackage___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_unbox(x_22);
x_25 = l_Lean_Name_toString(x_19, x_24, x_23);
x_26 = lean_string_utf8_byte_size(x_17);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_15);
lean_dec(x_14);
x_29 = lean_box(0);
lean_inc(x_17);
x_30 = l_Lake_joinRelative(x_17, x_21);
x_31 = l_Lake_loadDepPackage___closed__0;
x_32 = lean_box(1);
lean_inc(x_3);
x_33 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_10);
lean_ctor_set(x_33, 3, x_11);
lean_ctor_set(x_33, 4, x_17);
lean_ctor_set(x_33, 5, x_21);
lean_ctor_set(x_33, 6, x_30);
lean_ctor_set(x_33, 7, x_31);
lean_ctor_set(x_33, 8, x_2);
lean_ctor_set(x_33, 9, x_3);
lean_ctor_set(x_33, 10, x_20);
lean_ctor_set(x_33, 11, x_12);
lean_ctor_set_uint8(x_33, sizeof(void*)*12, x_4);
x_34 = lean_unbox(x_22);
lean_ctor_set_uint8(x_33, sizeof(void*)*12 + 1, x_34);
x_35 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*12 + 2, x_35);
x_36 = l_Lake_loadPackageCore(x_25, x_33, x_6, x_18);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_37, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_38, 1);
lean_dec(x_45);
lean_ctor_set(x_38, 1, x_5);
return x_36;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_5);
lean_ctor_set(x_37, 0, x_47);
return x_36;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_50 = x_38;
} else {
 lean_dec_ref(x_38);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_5);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_36, 0, x_52);
return x_36;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_ctor_get(x_37, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_55 = x_37;
} else {
 lean_dec_ref(x_37);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_38, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_57 = x_38;
} else {
 lean_dec_ref(x_38);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_5);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_36, 1);
lean_inc(x_61);
lean_dec(x_36);
x_62 = !lean_is_exclusive(x_37);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_37, 1);
x_64 = lean_ctor_get(x_37, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_38);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_38, 0);
x_67 = lean_ctor_get(x_38, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
lean_dec(x_39);
x_69 = l_Lake_Workspace_addFacetsFromEnv(x_68, x_3, x_5);
lean_dec(x_3);
x_70 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_69, x_61);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_ctor_set(x_38, 1, x_72);
lean_ctor_set(x_70, 0, x_37);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_70);
lean_ctor_set(x_38, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_37);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_free_object(x_38);
lean_dec(x_66);
x_76 = !lean_is_exclusive(x_70);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_70, 0);
x_78 = lean_io_error_to_string(x_77);
x_79 = lean_box(3);
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
x_81 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_81);
x_82 = lean_array_get_size(x_63);
x_83 = lean_array_push(x_63, x_80);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_83);
lean_ctor_set(x_37, 0, x_82);
lean_ctor_set_tag(x_70, 0);
lean_ctor_set(x_70, 0, x_37);
return x_70;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_70, 0);
x_85 = lean_ctor_get(x_70, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_70);
x_86 = lean_io_error_to_string(x_84);
x_87 = lean_box(3);
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
x_89 = lean_unbox(x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_89);
x_90 = lean_array_get_size(x_63);
x_91 = lean_array_push(x_63, x_88);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_91);
lean_ctor_set(x_37, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_37);
lean_ctor_set(x_92, 1, x_85);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_38, 0);
lean_inc(x_93);
lean_dec(x_38);
x_94 = lean_ctor_get(x_39, 0);
lean_inc(x_94);
lean_dec(x_39);
x_95 = l_Lake_Workspace_addFacetsFromEnv(x_94, x_3, x_5);
lean_dec(x_3);
x_96 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_95, x_61);
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
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_93);
lean_ctor_set(x_100, 1, x_97);
lean_ctor_set(x_37, 0, x_100);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_37);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_93);
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
x_106 = lean_box(3);
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_105);
x_108 = lean_unbox(x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_108);
x_109 = lean_array_get_size(x_63);
x_110 = lean_array_push(x_63, x_107);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_110);
lean_ctor_set(x_37, 0, x_109);
if (lean_is_scalar(x_104)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_104;
 lean_ctor_set_tag(x_111, 0);
}
lean_ctor_set(x_111, 0, x_37);
lean_ctor_set(x_111, 1, x_103);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_37, 1);
lean_inc(x_112);
lean_dec(x_37);
x_113 = lean_ctor_get(x_38, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_114 = x_38;
} else {
 lean_dec_ref(x_38);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_39, 0);
lean_inc(x_115);
lean_dec(x_39);
x_116 = l_Lake_Workspace_addFacetsFromEnv(x_115, x_3, x_5);
lean_dec(x_3);
x_117 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_116, x_61);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_114;
}
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_118);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_112);
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_120;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_119);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_114);
lean_dec(x_113);
x_124 = lean_ctor_get(x_117, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_126 = x_117;
} else {
 lean_dec_ref(x_117);
 x_126 = lean_box(0);
}
x_127 = lean_io_error_to_string(x_124);
x_128 = lean_box(3);
x_129 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_129, 0, x_127);
x_130 = lean_unbox(x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_130);
x_131 = lean_array_get_size(x_112);
x_132 = lean_array_push(x_112, x_129);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_126)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_126;
 lean_ctor_set_tag(x_134, 0);
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_125);
return x_134;
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_5);
lean_dec(x_3);
x_135 = !lean_is_exclusive(x_36);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_36, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_37);
if (x_137 == 0)
{
return x_36;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_37, 0);
x_139 = lean_ctor_get(x_37, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_37);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_36, 0, x_140);
return x_36;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_36, 1);
lean_inc(x_141);
lean_dec(x_36);
x_142 = lean_ctor_get(x_37, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_37, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_144 = x_37;
} else {
 lean_dec_ref(x_37);
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
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_147 = l_Lake_loadDepPackage___closed__1;
x_148 = lean_string_append(x_25, x_147);
x_149 = lean_string_append(x_148, x_14);
lean_dec(x_14);
x_150 = lean_box(3);
x_151 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_151, 0, x_149);
x_152 = lean_unbox(x_150);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_152);
x_153 = lean_array_get_size(x_6);
x_154 = lean_array_push(x_6, x_151);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_15, 0, x_155);
return x_15;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_156 = lean_ctor_get(x_15, 0);
x_157 = lean_ctor_get(x_15, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_15);
x_158 = lean_ctor_get(x_13, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_13, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_13, 2);
lean_inc(x_160);
lean_dec(x_13);
x_161 = lean_box(0);
x_162 = lean_alloc_closure((void*)(l_Lake_loadDepPackage___lam__0___boxed), 2, 1);
lean_closure_set(x_162, 0, x_161);
x_163 = lean_unbox(x_161);
x_164 = l_Lean_Name_toString(x_158, x_163, x_162);
x_165 = lean_string_utf8_byte_size(x_156);
x_166 = lean_unsigned_to_nat(0u);
x_167 = lean_nat_dec_eq(x_165, x_166);
lean_dec(x_165);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_14);
x_168 = lean_box(0);
lean_inc(x_156);
x_169 = l_Lake_joinRelative(x_156, x_160);
x_170 = l_Lake_loadDepPackage___closed__0;
x_171 = lean_box(1);
lean_inc(x_3);
x_172 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_172, 0, x_9);
lean_ctor_set(x_172, 1, x_168);
lean_ctor_set(x_172, 2, x_10);
lean_ctor_set(x_172, 3, x_11);
lean_ctor_set(x_172, 4, x_156);
lean_ctor_set(x_172, 5, x_160);
lean_ctor_set(x_172, 6, x_169);
lean_ctor_set(x_172, 7, x_170);
lean_ctor_set(x_172, 8, x_2);
lean_ctor_set(x_172, 9, x_3);
lean_ctor_set(x_172, 10, x_159);
lean_ctor_set(x_172, 11, x_12);
lean_ctor_set_uint8(x_172, sizeof(void*)*12, x_4);
x_173 = lean_unbox(x_161);
lean_ctor_set_uint8(x_172, sizeof(void*)*12 + 1, x_173);
x_174 = lean_unbox(x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*12 + 2, x_174);
x_175 = l_Lake_loadPackageCore(x_164, x_172, x_6, x_157);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_3);
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_180 = x_175;
} else {
 lean_dec_ref(x_175);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_182 = x_176;
} else {
 lean_dec_ref(x_176);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_177, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_184 = x_177;
} else {
 lean_dec_ref(x_177);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_5);
if (lean_is_scalar(x_182)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_182;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_181);
if (lean_is_scalar(x_180)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_180;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_188 = lean_ctor_get(x_175, 1);
lean_inc(x_188);
lean_dec(x_175);
x_189 = lean_ctor_get(x_176, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_190 = x_176;
} else {
 lean_dec_ref(x_176);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_177, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_192 = x_177;
} else {
 lean_dec_ref(x_177);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_178, 0);
lean_inc(x_193);
lean_dec(x_178);
x_194 = l_Lake_Workspace_addFacetsFromEnv(x_193, x_3, x_5);
lean_dec(x_3);
x_195 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_194, x_188);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_192;
}
lean_ctor_set(x_199, 0, x_191);
lean_ctor_set(x_199, 1, x_196);
if (lean_is_scalar(x_190)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_190;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_189);
if (lean_is_scalar(x_198)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_198;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_197);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_192);
lean_dec(x_191);
x_202 = lean_ctor_get(x_195, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_195, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_204 = x_195;
} else {
 lean_dec_ref(x_195);
 x_204 = lean_box(0);
}
x_205 = lean_io_error_to_string(x_202);
x_206 = lean_box(3);
x_207 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_207, 0, x_205);
x_208 = lean_unbox(x_206);
lean_ctor_set_uint8(x_207, sizeof(void*)*1, x_208);
x_209 = lean_array_get_size(x_189);
x_210 = lean_array_push(x_189, x_207);
if (lean_is_scalar(x_190)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_190;
 lean_ctor_set_tag(x_211, 1);
}
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
if (lean_is_scalar(x_204)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_204;
 lean_ctor_set_tag(x_212, 0);
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_203);
return x_212;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_5);
lean_dec(x_3);
x_213 = lean_ctor_get(x_175, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_214 = x_175;
} else {
 lean_dec_ref(x_175);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_176, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_176, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_217 = x_176;
} else {
 lean_dec_ref(x_176);
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
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_156);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_220 = l_Lake_loadDepPackage___closed__1;
x_221 = lean_string_append(x_164, x_220);
x_222 = lean_string_append(x_221, x_14);
lean_dec(x_14);
x_223 = lean_box(3);
x_224 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_224, 0, x_222);
x_225 = lean_unbox(x_223);
lean_ctor_set_uint8(x_224, sizeof(void*)*1, x_225);
x_226 = lean_array_get_size(x_6);
x_227 = lean_array_push(x_6, x_224);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_157);
return x_229;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadDepPackage___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_loadDepPackage___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_DepStackT_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DepStackT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_depCycleError___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dependency cycle detected:\n", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Name_instToString;
x_4 = l_Lake_depCycleError___redArg___closed__0;
x_5 = l_Lake_formatCycle___redArg(x_3, x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_depCycleError___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lake_depCycleError___redArg(x_1, x_3);
x_6 = lean_apply_1(x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(x_1);
x_4 = l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0;
x_5 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ResolveT_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ResolveT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, x_3, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0___boxed), 5, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_apply_4(x_2, x_3, x_8, x_4, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_name_eq(x_3, x_1);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0() {
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_inc(x_2);
x_14 = l_List_elem___redArg(x_1, x_2, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_12);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__1), 5, 4);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_5);
lean_closure_set(x_16, 3, x_15);
lean_ctor_set(x_10, 0, x_15);
x_17 = lean_apply_2(x_6, lean_box(0), x_10);
x_18 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_17, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(x_14);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
x_23 = l_List_partition_loop___redArg(x_20, x_12, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_dec(x_26);
lean_inc(x_2);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_25);
lean_ctor_set(x_23, 0, x_2);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_21);
x_28 = l_List_appendTR___redArg(x_23, x_27);
x_29 = l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0;
x_30 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_30, 0, x_8);
lean_closure_set(x_30, 1, x_29);
x_31 = l_Lake_depCycleError___redArg(x_30, x_28);
x_32 = lean_apply_2(x_31, x_9, x_13);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
lean_inc(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_21);
x_36 = l_List_appendTR___redArg(x_34, x_35);
x_37 = l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0;
x_38 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_38, 0, x_8);
lean_closure_set(x_38, 1, x_37);
x_39 = l_Lake_depCycleError___redArg(x_38, x_36);
x_40 = lean_apply_2(x_39, x_9, x_13);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
lean_inc(x_41);
lean_inc(x_2);
x_43 = l_List_elem___redArg(x_1, x_2, x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_41);
lean_inc(x_44);
x_45 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__1), 5, 4);
lean_closure_set(x_45, 0, x_3);
lean_closure_set(x_45, 1, x_4);
lean_closure_set(x_45, 2, x_5);
lean_closure_set(x_45, 3, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_apply_2(x_6, lean_box(0), x_46);
x_48 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_47, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = lean_box(x_43);
lean_inc(x_2);
x_50 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_50, 0, x_2);
lean_closure_set(x_50, 1, x_49);
x_51 = lean_box(0);
x_52 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
x_53 = l_List_partition_loop___redArg(x_50, x_41, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
lean_inc(x_2);
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_51);
x_58 = l_List_appendTR___redArg(x_56, x_57);
x_59 = l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0;
x_60 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_60, 0, x_8);
lean_closure_set(x_60, 1, x_59);
x_61 = l_Lake_depCycleError___redArg(x_60, x_58);
x_62 = lean_apply_2(x_61, x_9, x_42);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3), 10, 9);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_6);
lean_closure_set(x_11, 5, x_3);
lean_closure_set(x_11, 6, x_4);
lean_closure_set(x_11, 7, x_5);
lean_closure_set(x_11, 8, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_apply_2(x_3, lean_box(0), x_12);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_13, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0;
x_11 = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_11);
lean_inc(x_8);
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__4), 9, 5);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_9);
lean_closure_set(x_13, 3, x_8);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__5), 2, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = l_Lake_recFetch___redArg(x_13, x_5);
x_16 = lean_apply_2(x_15, x_6, x_3);
x_17 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_box(0);
x_7 = l_Lake_Workspace_addPackage(x_4, x_5);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
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
x_11 = lean_box(0);
x_12 = l_Lake_Workspace_addPackage(x_9, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_apply_2(x_1, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_3(x_1, x_2, x_3, x_8);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package requires itself (or a package with the same name)", 59, 59);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_name_eq(x_13, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
lean_ctor_set(x_9, 0, x_15);
x_16 = lean_apply_2(x_3, lean_box(0), x_9);
x_17 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_16, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_9);
lean_dec(x_5);
x_18 = l_Lean_Name_toString(x_13, x_14, x_6);
x_19 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_apply_2(x_7, lean_box(0), x_20);
x_22 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5), 3, 2);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_3);
lean_inc(x_4);
x_23 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_21, x_22);
x_24 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_23, x_8);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_name_eq(x_26, x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
x_30 = lean_apply_2(x_3, lean_box(0), x_29);
x_31 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_30, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_5);
x_32 = l_Lean_Name_toString(x_26, x_27, x_6);
x_33 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_apply_2(x_7, lean_box(0), x_34);
x_36 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5), 3, 2);
lean_closure_set(x_36, 0, x_25);
lean_closure_set(x_36, 1, x_3);
lean_inc(x_4);
x_37 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_35, x_36);
x_38 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_37, x_8);
return x_38;
}
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lake_loadDepPackage___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0;
lean_inc(x_12);
x_14 = l_Lake_RBNode_dFind___redArg(x_13, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1;
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed), 9, 8);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_15);
lean_closure_set(x_16, 6, x_6);
lean_closure_set(x_16, 7, x_7);
x_17 = lean_box(0);
lean_ctor_set(x_8, 0, x_17);
x_18 = lean_apply_2(x_3, lean_box(0), x_8);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_18, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = lean_box(0);
lean_ctor_set(x_8, 0, x_20);
x_21 = lean_apply_2(x_3, lean_box(0), x_8);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_ctor_get(x_22, 4);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0;
lean_inc(x_25);
x_27 = l_Lake_RBNode_dFind___redArg(x_26, x_24, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1;
lean_inc(x_4);
lean_inc(x_3);
x_29 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed), 9, 8);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_25);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_5);
lean_closure_set(x_29, 5, x_28);
lean_closure_set(x_29, 6, x_6);
lean_closure_set(x_29, 7, x_7);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
x_32 = lean_apply_2(x_3, lean_box(0), x_31);
x_33 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_32, x_29);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
x_36 = lean_apply_2(x_3, lean_box(0), x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_3);
lean_inc(x_7);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed), 8, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_9);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_5);
x_13 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4), 8, 7);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
lean_closure_set(x_13, 5, x_6);
lean_closure_set(x_13, 6, x_12);
lean_inc(x_5);
x_14 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6), 2, 1);
lean_closure_set(x_14, 0, x_5);
lean_inc(x_5);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 2, 1);
lean_closure_set(x_15, 0, x_5);
lean_inc(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_apply_2(x_5, lean_box(0), x_16);
lean_inc(x_3);
x_18 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_17, x_15);
lean_inc(x_3);
x_19 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_18, x_14);
x_20 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_19, x_13);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = lean_box(0);
x_13 = lean_nat_dec_lt(x_1, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_6, 0, x_12);
x_14 = lean_apply_2(x_2, lean_box(0), x_6);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_6, 0, x_12);
x_16 = lean_apply_2(x_2, lean_box(0), x_6);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_6);
lean_dec(x_2);
x_17 = lean_usize_of_nat(x_1);
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_foldlMUnsafe_fold___redArg(x_3, x_4, x_10, x_17, x_18, x_12);
x_20 = lean_apply_2(x_19, x_5, x_9);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_ctor_get(x_21, 3);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_23);
x_25 = lean_box(0);
x_26 = lean_nat_dec_lt(x_1, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_22);
x_28 = lean_apply_2(x_2, lean_box(0), x_27);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_24, x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_22);
x_31 = lean_apply_2(x_2, lean_box(0), x_30);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_32 = lean_usize_of_nat(x_1);
x_33 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_34 = l_Array_foldlMUnsafe_fold___redArg(x_3, x_4, x_23, x_32, x_33, x_25);
x_35 = lean_apply_2(x_34, x_5, x_22);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6), 2, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 2, 1);
lean_closure_set(x_9, 0, x_1);
lean_inc(x_6);
lean_ctor_set(x_4, 0, x_6);
x_10 = lean_apply_2(x_1, lean_box(0), x_4);
lean_inc(x_2);
x_11 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_10, x_9);
lean_inc(x_2);
x_12 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_11, x_8);
x_13 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_12, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6), 2, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 2, 1);
lean_closure_set(x_16, 0, x_1);
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_apply_2(x_1, lean_box(0), x_17);
lean_inc(x_2);
x_19 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_18, x_16);
lean_inc(x_2);
x_20 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_19, x_15);
x_21 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_20, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 9);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_array_get_size(x_12);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed), 6, 5);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_inc(x_6);
lean_inc(x_2);
x_16 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13), 4, 3);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_6);
lean_closure_set(x_16, 2, x_15);
x_17 = lean_array_get_size(x_13);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_box(0);
x_20 = lean_nat_dec_lt(x_18, x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_19);
x_21 = lean_apply_2(x_2, lean_box(0), x_8);
x_22 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_21, x_16);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_8);
lean_dec(x_2);
x_23 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_24 = 0;
x_25 = l_Array_foldrMUnsafe_fold___redArg(x_3, x_7, x_13, x_23, x_24, x_19);
x_26 = lean_apply_2(x_25, x_5, x_11);
x_27 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_26, x_16);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_30 = lean_ctor_get(x_28, 3);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_1, 9);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_array_get_size(x_30);
lean_dec(x_30);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_33 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed), 6, 5);
lean_closure_set(x_33, 0, x_32);
lean_closure_set(x_33, 1, x_2);
lean_closure_set(x_33, 2, x_3);
lean_closure_set(x_33, 3, x_4);
lean_closure_set(x_33, 4, x_5);
lean_inc(x_6);
lean_inc(x_2);
x_34 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13), 4, 3);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_6);
lean_closure_set(x_34, 2, x_33);
x_35 = lean_array_get_size(x_31);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_box(0);
x_38 = lean_nat_dec_lt(x_36, x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_29);
x_40 = lean_apply_2(x_2, lean_box(0), x_39);
x_41 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_40, x_34);
return x_41;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_42 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_43 = 0;
x_44 = l_Array_foldrMUnsafe_fold___redArg(x_3, x_7, x_31, x_42, x_43, x_37);
x_45 = lean_apply_2(x_44, x_5, x_29);
x_46 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_45, x_34);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_9, 0, x_1);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_1);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_ReaderT_instMonad___redArg(x_17);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0), 2, 1);
lean_closure_set(x_23, 0, x_22);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_4);
x_24 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed), 10, 6);
lean_closure_set(x_24, 0, x_3);
lean_closure_set(x_24, 1, x_4);
lean_closure_set(x_24, 2, x_21);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_22);
lean_closure_set(x_24, 5, x_2);
x_25 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed), 5, 1);
lean_closure_set(x_25, 0, x_5);
lean_inc(x_21);
lean_inc(x_22);
x_26 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11), 8, 7);
lean_closure_set(x_26, 0, x_4);
lean_closure_set(x_26, 1, x_22);
lean_closure_set(x_26, 2, x_18);
lean_closure_set(x_26, 3, x_25);
lean_closure_set(x_26, 4, x_6);
lean_closure_set(x_26, 5, x_21);
lean_closure_set(x_26, 6, x_24);
lean_inc(x_22);
x_27 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6), 2, 1);
lean_closure_set(x_27, 0, x_22);
lean_inc(x_22);
x_28 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 2, 1);
lean_closure_set(x_28, 0, x_22);
lean_inc(x_7);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_7);
x_29 = lean_apply_2(x_22, lean_box(0), x_1);
lean_inc(x_21);
x_30 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_29, x_28);
lean_inc(x_21);
x_31 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_30, x_27);
x_32 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_31, x_26);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_1);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0), 2, 1);
lean_closure_set(x_36, 0, x_35);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_4);
x_37 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed), 10, 6);
lean_closure_set(x_37, 0, x_3);
lean_closure_set(x_37, 1, x_4);
lean_closure_set(x_37, 2, x_34);
lean_closure_set(x_37, 3, x_36);
lean_closure_set(x_37, 4, x_35);
lean_closure_set(x_37, 5, x_2);
x_38 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed), 5, 1);
lean_closure_set(x_38, 0, x_5);
lean_inc(x_34);
lean_inc(x_35);
x_39 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11), 8, 7);
lean_closure_set(x_39, 0, x_4);
lean_closure_set(x_39, 1, x_35);
lean_closure_set(x_39, 2, x_18);
lean_closure_set(x_39, 3, x_38);
lean_closure_set(x_39, 4, x_6);
lean_closure_set(x_39, 5, x_34);
lean_closure_set(x_39, 6, x_37);
lean_inc(x_35);
x_40 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6), 2, 1);
lean_closure_set(x_40, 0, x_35);
lean_inc(x_35);
x_41 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 2, 1);
lean_closure_set(x_41, 0, x_35);
lean_inc(x_7);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_7);
lean_ctor_set(x_42, 1, x_7);
x_43 = lean_apply_2(x_35, lean_box(0), x_42);
lean_inc(x_34);
x_44 = lean_apply_4(x_34, lean_box(0), lean_box(0), x_43, x_41);
lean_inc(x_34);
x_45 = lean_apply_4(x_34, lean_box(0), lean_box(0), x_44, x_40);
x_46 = lean_apply_4(x_34, lean_box(0), lean_box(0), x_45, x_39);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go), 8, 4);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_4);
x_8 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go), 8, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_5);
x_9 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_UpdateT_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_UpdateT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_2, x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = l_Lean_NameSet_contains(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(0);
x_13 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_10, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_dec(x_10);
lean_dec(x_2);
goto block_8;
}
}
else
{
lean_dec(x_2);
goto block_8;
}
block_8:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2___redArg(x_1, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___at___Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___at___Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___at___Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___at___Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0_spec__0___redArg(x_5, x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_7);
x_11 = lean_apply_5(x_1, x_5, x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_6 = x_15;
x_8 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not rename workspace packages directory: ", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("workspace packages directory changed; renaming '", 48, 48);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to '", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": no previous manifest, creating one from scratch", 49, 49);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ignoring previous manifest because it failed to load: ", 56, 56);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_197; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
lean_dec(x_1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 6);
lean_inc(x_65);
lean_dec(x_61);
lean_inc(x_2);
x_120 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2___boxed), 6, 1);
lean_closure_set(x_120, 0, x_2);
x_121 = lean_box(0);
x_122 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1;
x_123 = lean_unbox(x_121);
x_124 = l_Lean_Name_toString(x_62, x_123, x_122);
lean_inc(x_63);
x_185 = l_Lake_joinRelative(x_63, x_65);
lean_dec(x_65);
x_186 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_197 = l_Lake_Manifest_load(x_185, x_5);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_198);
x_187 = x_200;
x_188 = x_199;
goto block_196;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_197, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_203, 0, x_201);
x_187 = x_203;
x_188 = x_202;
goto block_196;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
block_33:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0;
x_18 = lean_io_error_to_string(x_16);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_box(3);
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
x_23 = lean_apply_2(x_12, x_21, x_15);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
lean_dec(x_12);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_14);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_15);
return x_32;
}
}
block_48:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_array_get_size(x_35);
x_41 = lean_nat_dec_lt(x_37, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_35);
x_12 = x_36;
x_13 = x_38;
x_14 = x_34;
x_15 = x_39;
goto block_33;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_40, x_40);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_35);
x_12 = x_36;
x_13 = x_38;
x_14 = x_34;
x_15 = x_39;
goto block_33;
}
else
{
lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_box(0);
x_44 = 0;
x_45 = lean_usize_of_nat(x_40);
lean_dec(x_40);
lean_inc(x_36);
x_46 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_35, x_44, x_45, x_43, x_36, x_39);
lean_dec(x_35);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_12 = x_36;
x_13 = x_38;
x_14 = x_34;
x_15 = x_47;
goto block_33;
}
}
}
block_60:
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
x_34 = x_49;
x_35 = x_50;
x_36 = x_51;
x_37 = x_52;
x_38 = x_56;
x_39 = x_55;
goto block_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_34 = x_49;
x_35 = x_50;
x_36 = x_51;
x_37 = x_52;
x_38 = x_59;
x_39 = x_58;
goto block_48;
}
}
block_95:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
lean_dec(x_64);
x_73 = l_System_FilePath_normalize(x_66);
x_74 = l_System_FilePath_normalize(x_72);
lean_inc(x_74);
x_75 = l_System_FilePath_normalize(x_74);
x_76 = lean_string_dec_eq(x_73, x_75);
lean_dec(x_75);
lean_dec(x_73);
if (x_76 == 0)
{
if (x_69 == 0)
{
lean_dec(x_74);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_63);
x_6 = x_70;
x_7 = x_71;
goto block_11;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_77 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1;
x_78 = lean_string_append(x_77, x_68);
x_79 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2;
x_80 = lean_string_append(x_78, x_79);
x_81 = l_Lake_joinRelative(x_63, x_74);
lean_dec(x_74);
x_82 = lean_string_append(x_80, x_81);
x_83 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_box(1);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_87);
lean_inc(x_67);
x_88 = lean_apply_2(x_67, x_86, x_71);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_unsigned_to_nat(0u);
x_91 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_92 = l_Lake_createParentDirs(x_81, x_89);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_io_rename(x_68, x_81, x_93);
lean_dec(x_81);
lean_dec(x_68);
x_49 = x_70;
x_50 = x_91;
x_51 = x_67;
x_52 = x_90;
x_53 = x_94;
goto block_60;
}
else
{
lean_dec(x_81);
lean_dec(x_68);
x_49 = x_70;
x_50 = x_91;
x_51 = x_67;
x_52 = x_90;
x_53 = x_92;
goto block_60;
}
}
}
else
{
lean_dec(x_74);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_63);
x_6 = x_70;
x_7 = x_71;
goto block_11;
}
}
block_119:
{
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
lean_dec(x_64);
lean_dec(x_63);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_103 = lean_ctor_get(x_96, 0);
lean_inc(x_103);
lean_dec(x_96);
lean_inc(x_63);
x_104 = l_Lake_joinRelative(x_63, x_103);
x_105 = l_System_FilePath_pathExists(x_104, x_99);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_109 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6;
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = lean_unbox(x_106);
lean_dec(x_106);
x_66 = x_103;
x_67 = x_98;
x_68 = x_104;
x_69 = x_110;
x_70 = x_97;
x_71 = x_107;
goto block_95;
}
else
{
uint8_t x_111; 
x_111 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7;
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = lean_unbox(x_106);
lean_dec(x_106);
x_66 = x_103;
x_67 = x_98;
x_68 = x_104;
x_69 = x_112;
x_70 = x_97;
x_71 = x_107;
goto block_95;
}
else
{
lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_113 = lean_box(0);
x_114 = 0;
x_115 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8;
lean_inc(x_98);
x_116 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_108, x_114, x_115, x_113, x_98, x_107);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_unbox(x_106);
lean_dec(x_106);
x_66 = x_103;
x_67 = x_98;
x_68 = x_104;
x_69 = x_118;
x_70 = x_97;
x_71 = x_117;
goto block_95;
}
}
}
}
block_184:
{
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_128; 
lean_dec(x_120);
lean_dec(x_64);
lean_dec(x_63);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
lean_dec(x_125);
if (lean_obj_tag(x_128) == 11)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_128);
lean_dec(x_2);
x_129 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9;
x_130 = lean_string_append(x_124, x_129);
x_131 = lean_box(1);
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
x_133 = lean_unbox(x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_133);
x_134 = lean_apply_2(x_4, x_132, x_127);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_126);
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
lean_ctor_set(x_140, 1, x_126);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; uint8_t x_150; 
x_142 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10;
x_143 = lean_string_append(x_124, x_142);
x_144 = lean_io_error_to_string(x_128);
x_145 = lean_string_append(x_143, x_144);
lean_dec(x_144);
x_146 = lean_box(2);
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_145);
x_148 = lean_unbox(x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_148);
x_149 = lean_apply_2(x_4, x_147, x_127);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_126);
lean_ctor_set(x_149, 0, x_152);
return x_149;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_149, 0);
x_154 = lean_ctor_get(x_149, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_149);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_126);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_2);
x_157 = lean_io_error_to_string(x_128);
x_158 = lean_box(3);
x_159 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_159, 0, x_157);
x_160 = lean_unbox(x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_160);
x_161 = lean_apply_2(x_4, x_159, x_127);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_161, 0);
lean_dec(x_163);
x_164 = lean_box(0);
lean_ctor_set_tag(x_161, 1);
lean_ctor_set(x_161, 0, x_164);
return x_161;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
lean_dec(x_161);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
}
else
{
lean_dec(x_124);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_120);
x_168 = lean_ctor_get(x_125, 0);
lean_inc(x_168);
lean_dec(x_125);
x_169 = lean_ctor_get(x_168, 2);
lean_inc(x_169);
lean_dec(x_168);
x_96 = x_169;
x_97 = x_126;
x_98 = x_4;
x_99 = x_127;
goto block_119;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_2);
x_170 = lean_ctor_get(x_125, 0);
lean_inc(x_170);
lean_dec(x_125);
x_171 = lean_ctor_get(x_170, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 3);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_array_get_size(x_172);
x_175 = lean_nat_dec_lt(x_173, x_174);
if (x_175 == 0)
{
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_120);
x_96 = x_171;
x_97 = x_126;
x_98 = x_4;
x_99 = x_127;
goto block_119;
}
else
{
uint8_t x_176; 
x_176 = lean_nat_dec_le(x_174, x_174);
if (x_176 == 0)
{
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_120);
x_96 = x_171;
x_97 = x_126;
x_98 = x_4;
x_99 = x_127;
goto block_119;
}
else
{
lean_object* x_177; size_t x_178; size_t x_179; lean_object* x_180; 
x_177 = lean_box(0);
x_178 = 0;
x_179 = lean_usize_of_nat(x_174);
lean_dec(x_174);
lean_inc(x_4);
x_180 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(x_120, x_172, x_178, x_179, x_177, x_126, x_4, x_127);
lean_dec(x_172);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_96 = x_171;
x_97 = x_183;
x_98 = x_4;
x_99 = x_182;
goto block_119;
}
else
{
lean_dec(x_171);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_4);
return x_180;
}
}
}
}
}
}
block_196:
{
uint8_t x_189; 
x_189 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6;
if (x_189 == 0)
{
x_125 = x_187;
x_126 = x_3;
x_127 = x_188;
goto block_184;
}
else
{
uint8_t x_190; 
x_190 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7;
if (x_190 == 0)
{
x_125 = x_187;
x_126 = x_3;
x_127 = x_188;
goto block_184;
}
else
{
lean_object* x_191; size_t x_192; size_t x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_box(0);
x_192 = 0;
x_193 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8;
lean_inc(x_4);
x_194 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_186, x_192, x_193, x_191, x_4, x_188);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_125 = x_187;
x_126 = x_3;
x_127 = x_195;
goto block_184;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___at___Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___at___Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___elam__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
x_17 = lean_ctor_get(x_2, 4);
x_18 = l_Lean_NameMap_contains___redArg(x_3, x_13);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_box(1);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_Lake_joinRelative(x_22, x_21);
lean_dec(x_21);
lean_ctor_set(x_17, 0, x_23);
lean_inc(x_13);
x_24 = lean_unbox(x_19);
lean_ctor_set_uint8(x_2, sizeof(void*)*5, x_24);
x_5 = x_2;
x_6 = x_13;
goto block_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lake_joinRelative(x_26, x_25);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_13);
lean_ctor_set(x_2, 4, x_28);
x_29 = lean_unbox(x_19);
lean_ctor_set_uint8(x_2, sizeof(void*)*5, x_29);
x_5 = x_2;
x_6 = x_13;
goto block_11;
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
lean_inc(x_13);
x_30 = lean_unbox(x_19);
lean_ctor_set_uint8(x_2, sizeof(void*)*5, x_30);
x_5 = x_2;
x_6 = x_13;
goto block_11;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_2);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = lean_ctor_get(x_2, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_39 = l_Lean_NameMap_contains___redArg(x_3, x_34);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_box(1);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
lean_dec(x_1);
x_44 = l_Lake_joinRelative(x_43, x_41);
lean_dec(x_41);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_inc(x_34);
x_46 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_35);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_37);
lean_ctor_set(x_46, 4, x_45);
x_47 = lean_unbox(x_40);
lean_ctor_set_uint8(x_46, sizeof(void*)*5, x_47);
x_5 = x_46;
x_6 = x_34;
goto block_11;
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_1);
lean_inc(x_34);
x_48 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_48, 2, x_36);
lean_ctor_set(x_48, 3, x_37);
lean_ctor_set(x_48, 4, x_38);
x_49 = lean_unbox(x_40);
lean_ctor_set_uint8(x_48, sizeof(void*)*5, x_49);
x_5 = x_48;
x_6 = x_34;
goto block_11;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_3);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
return x_52;
}
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_box(0);
x_8 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_3, x_6, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___elam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___elam__1___redArg(x_1, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ignoring missing manifest '", 29, 29);
return x_1;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_78; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 6);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___lam__0___boxed), 1, 0);
x_9 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___elam__1___boxed), 6, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lake_joinRelative(x_6, x_7);
lean_dec(x_7);
x_67 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
lean_inc(x_10);
x_78 = l_Lake_Manifest_load(x_10, x_4);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_79);
x_68 = x_81;
x_69 = x_80;
goto block_77;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_dec(x_78);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_82);
x_68 = x_84;
x_69 = x_83;
goto block_77;
}
block_66:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 11)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_14);
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Name_toString(x_5, x_16, x_8);
x_18 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_10);
lean_dec(x_10);
x_21 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_box(2);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_25);
x_26 = lean_apply_2(x_3, x_24, x_13);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_12);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_10);
x_34 = lean_box(1);
x_35 = lean_unbox(x_34);
x_36 = l_Lean_Name_toString(x_5, x_35, x_8);
x_37 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_io_error_to_string(x_14);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
x_41 = lean_box(2);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_43);
x_44 = lean_apply_2(x_3, x_42, x_13);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_12);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_12);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
x_52 = lean_ctor_get(x_11, 0);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_53);
x_56 = lean_box(0);
x_57 = lean_nat_dec_lt(x_54, x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_9);
lean_dec(x_3);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_12);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_13);
return x_59;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_le(x_55, x_55);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_9);
lean_dec(x_3);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_12);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_13);
return x_62;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_65 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(x_9, x_53, x_63, x_64, x_56, x_12, x_3, x_13);
lean_dec(x_53);
return x_65;
}
}
}
}
block_77:
{
uint8_t x_70; 
x_70 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6;
if (x_70 == 0)
{
x_11 = x_68;
x_12 = x_2;
x_13 = x_69;
goto block_66;
}
else
{
uint8_t x_71; 
x_71 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7;
if (x_71 == 0)
{
x_11 = x_68;
x_12 = x_2;
x_13 = x_69;
goto block_66;
}
else
{
lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_box(0);
x_73 = 0;
x_74 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8;
lean_inc(x_3);
x_75 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_67, x_73, x_74, x_72, x_3, x_69);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_11 = x_68;
x_12 = x_2;
x_13 = x_76;
goto block_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___elam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___elam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0() {
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
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_4, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_79; uint8_t x_80; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_dec(x_2);
x_79 = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0;
x_80 = lean_string_dec_eq(x_27, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = l_Lake_joinRelative(x_27, x_79);
x_28 = x_81;
goto block_78;
}
else
{
x_28 = x_27;
goto block_78;
}
block_78:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_name_eq(x_26, x_32);
lean_dec(x_32);
lean_dec(x_26);
x_36 = l_instDecidableNot___redArg(x_35);
x_37 = l_System_FilePath_normalize(x_34);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_40 = l_Lake_Dependency_materialize(x_3, x_36, x_31, x_33, x_37, x_28, x_39, x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_38, x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_5);
x_11 = x_43;
x_12 = x_4;
x_13 = x_42;
goto block_19;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_5);
x_11 = x_43;
x_12 = x_4;
x_13 = x_42;
goto block_19;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_box(0);
x_49 = 0;
x_50 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_51 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_44, x_49, x_50, x_48, x_5, x_42);
lean_dec(x_44);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_11 = x_43;
x_12 = x_4;
x_13 = x_52;
goto block_19;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_40, 1);
x_55 = lean_ctor_get(x_40, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_dec(x_41);
x_57 = lean_array_get_size(x_56);
x_58 = lean_nat_dec_lt(x_38, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_5);
x_59 = lean_box(0);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_59);
return x_40;
}
else
{
uint8_t x_60; 
lean_free_object(x_40);
x_60 = lean_nat_dec_le(x_57, x_57);
if (x_60 == 0)
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_5);
x_7 = x_54;
goto block_10;
}
else
{
lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_box(0);
x_62 = 0;
x_63 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_64 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_56, x_62, x_63, x_61, x_5, x_54);
lean_dec(x_56);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_7 = x_65;
goto block_10;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_40, 1);
lean_inc(x_66);
lean_dec(x_40);
x_67 = lean_ctor_get(x_41, 1);
lean_inc(x_67);
lean_dec(x_41);
x_68 = lean_array_get_size(x_67);
x_69 = lean_nat_dec_lt(x_38, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_68, x_68);
if (x_72 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
x_7 = x_66;
goto block_10;
}
else
{
lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_box(0);
x_74 = 0;
x_75 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_76 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_67, x_74, x_75, x_73, x_5, x_66);
lean_dec(x_67);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_7 = x_77;
goto block_10;
}
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_3);
lean_dec(x_2);
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_25, 0);
lean_inc(x_84);
lean_dec(x_25);
x_85 = lean_ctor_get(x_1, 1);
lean_inc(x_85);
lean_dec(x_1);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec(x_83);
x_88 = l_System_FilePath_normalize(x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_91 = l_Lake_PackageEntry_materialize(x_84, x_85, x_86, x_88, x_90, x_6);
lean_dec(x_85);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_102; uint8_t x_103; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
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
x_102 = lean_array_get_size(x_96);
x_103 = lean_nat_dec_lt(x_89, x_102);
if (x_103 == 0)
{
lean_dec(x_102);
lean_dec(x_96);
lean_dec(x_5);
x_98 = x_93;
goto block_101;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_102, x_102);
if (x_104 == 0)
{
lean_dec(x_102);
lean_dec(x_96);
lean_dec(x_5);
x_98 = x_93;
goto block_101;
}
else
{
lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_box(0);
x_106 = 0;
x_107 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_108 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_96, x_106, x_107, x_105, x_5, x_93);
lean_dec(x_96);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_98 = x_109;
goto block_101;
}
}
block_101:
{
lean_object* x_99; lean_object* x_100; 
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_4);
if (lean_is_scalar(x_94)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_94;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
uint8_t x_110; 
lean_dec(x_4);
x_110 = !lean_is_exclusive(x_91);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_91, 1);
x_112 = lean_ctor_get(x_91, 0);
lean_dec(x_112);
x_113 = lean_ctor_get(x_92, 1);
lean_inc(x_113);
lean_dec(x_92);
x_114 = lean_array_get_size(x_113);
x_115 = lean_nat_dec_lt(x_89, x_114);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_5);
x_116 = lean_box(0);
lean_ctor_set_tag(x_91, 1);
lean_ctor_set(x_91, 0, x_116);
return x_91;
}
else
{
uint8_t x_117; 
lean_free_object(x_91);
x_117 = lean_nat_dec_le(x_114, x_114);
if (x_117 == 0)
{
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_5);
x_20 = x_111;
goto block_23;
}
else
{
lean_object* x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_box(0);
x_119 = 0;
x_120 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_121 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_113, x_119, x_120, x_118, x_5, x_111);
lean_dec(x_113);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_20 = x_122;
goto block_23;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_ctor_get(x_91, 1);
lean_inc(x_123);
lean_dec(x_91);
x_124 = lean_ctor_get(x_92, 1);
lean_inc(x_124);
lean_dec(x_92);
x_125 = lean_array_get_size(x_124);
x_126 = lean_nat_dec_lt(x_89, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_5);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_123);
return x_128;
}
else
{
uint8_t x_129; 
x_129 = lean_nat_dec_le(x_125, x_125);
if (x_129 == 0)
{
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_5);
x_20 = x_123;
goto block_23;
}
else
{
lean_object* x_130; size_t x_131; size_t x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_box(0);
x_131 = 0;
x_132 = lean_usize_of_nat(x_125);
lean_dec(x_125);
x_133 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_124, x_131, x_132, x_130, x_5, x_123);
lean_dec(x_124);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_20 = x_134;
goto block_23;
}
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_12, x_15, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package '", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' was required as '", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' was downloaded incorrectly; you will need to manually delete '", 64, 64);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': ", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("std", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__5;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__8() {
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
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_name_eq(x_7, x_9);
x_11 = l_instDecidableNot___redArg(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_76; lean_object* x_77; lean_object* x_90; uint8_t x_91; 
x_14 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
x_90 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__6;
x_91 = lean_name_eq(x_9, x_90);
if (x_91 == 0)
{
x_76 = x_5;
x_77 = x_6;
goto block_89;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_3, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 4);
lean_inc(x_93);
lean_dec(x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_dec(x_93);
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_93, 2);
lean_inc(x_105);
lean_dec(x_93);
if (lean_obj_tag(x_105) == 0)
{
goto block_104;
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__8;
x_109 = l_String_quote(x_107);
lean_dec(x_107);
lean_ctor_set_tag(x_105, 3);
lean_ctor_set(x_105, 0, x_109);
x_110 = lean_unsigned_to_nat(120u);
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_format_pretty(x_105, x_110, x_111, x_111);
x_113 = lean_string_append(x_108, x_112);
lean_dec(x_112);
x_94 = x_113;
goto block_102;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_114 = lean_ctor_get(x_105, 0);
lean_inc(x_114);
lean_dec(x_105);
x_115 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__8;
x_116 = l_String_quote(x_114);
lean_dec(x_114);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_unsigned_to_nat(120u);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_format_pretty(x_117, x_118, x_119, x_119);
x_121 = lean_string_append(x_115, x_120);
lean_dec(x_120);
x_94 = x_121;
goto block_102;
}
}
}
block_102:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
lean_inc(x_7);
x_95 = l_Lean_Name_toString(x_7, x_91, x_14);
x_96 = l_Lake_stdMismatchError(x_95, x_94);
lean_dec(x_94);
lean_dec(x_95);
x_97 = lean_box(3);
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
x_99 = lean_unbox(x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_99);
lean_inc(x_5);
x_100 = lean_apply_2(x_5, x_98, x_6);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_76 = x_5;
x_77 = x_101;
goto block_89;
}
block_104:
{
lean_object* x_103; 
x_103 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__7;
x_94 = x_103;
goto block_102;
}
}
block_39:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Name_toString(x_17, x_11, x_14);
x_19 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Name_toString(x_7, x_11, x_14);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lean_Name_toString(x_9, x_11, x_14);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_box(3);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = lean_apply_2(x_15, x_30, x_16);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
block_60:
{
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
lean_inc(x_9);
x_46 = l_Lean_Name_toString(x_9, x_40, x_14);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_8);
lean_dec(x_8);
x_51 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__4;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_io_error_to_string(x_44);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_55 = lean_box(3);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_unbox(x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
lean_inc(x_41);
x_58 = lean_apply_2(x_41, x_56, x_43);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_15 = x_41;
x_16 = x_59;
goto block_39;
}
else
{
lean_dec(x_42);
lean_dec(x_8);
x_15 = x_41;
x_16 = x_43;
goto block_39;
}
}
block_75:
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_array_get_size(x_64);
x_68 = lean_nat_dec_lt(x_61, x_67);
if (x_68 == 0)
{
lean_dec(x_67);
lean_dec(x_64);
x_40 = x_62;
x_41 = x_63;
x_42 = x_65;
x_43 = x_66;
goto block_60;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_67, x_67);
if (x_69 == 0)
{
lean_dec(x_67);
lean_dec(x_64);
x_40 = x_62;
x_41 = x_63;
x_42 = x_65;
x_43 = x_66;
goto block_60;
}
else
{
lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = 0;
x_72 = lean_usize_of_nat(x_67);
lean_dec(x_67);
lean_inc(x_63);
x_73 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_64, x_71, x_72, x_70, x_63, x_66);
lean_dec(x_64);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_40 = x_62;
x_41 = x_63;
x_42 = x_65;
x_43 = x_74;
goto block_60;
}
}
}
block_89:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_3, 2);
lean_inc(x_78);
lean_dec(x_3);
x_79 = lean_ctor_get(x_78, 4);
lean_inc(x_79);
lean_dec(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_dec(x_79);
lean_dec(x_8);
x_15 = x_76;
x_16 = x_77;
goto block_39;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_79);
x_80 = lean_unsigned_to_nat(0u);
x_81 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_82 = l_IO_FS_removeDirAll(x_8, x_77);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_83);
x_61 = x_80;
x_62 = x_11;
x_63 = x_76;
x_64 = x_81;
x_65 = x_85;
x_66 = x_84;
goto block_75;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_dec(x_82);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_86);
x_61 = x_80;
x_62 = x_11;
x_63 = x_76;
x_64 = x_81;
x_65 = x_88;
x_66 = x_87;
goto block_75;
}
}
}
}
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
static lean_object* _init_l_Lake_Workspace_updateToolchain___elam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean-toolchain", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lake_joinRelative(x_1, x_6);
x_9 = l_Lake_Workspace_updateToolchain___elam__0___closed__0;
x_10 = l_System_FilePath_join(x_8, x_9);
x_11 = l_Lake_ToolchainVer_ofFile_x3f(x_10, x_5);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_2, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_11, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_7, 0);
lean_ctor_set(x_17, 0, x_12);
lean_inc(x_26);
lean_ctor_set(x_2, 0, x_26);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_27);
lean_inc(x_28);
lean_ctor_set(x_2, 1, x_29);
lean_ctor_set(x_2, 0, x_28);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_32 = x_17;
} else {
 lean_dec_ref(x_17);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_7, 0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_31);
lean_inc(x_33);
lean_ctor_set(x_2, 1, x_34);
lean_ctor_set(x_2, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_37 = x_11;
} else {
 lean_dec_ref(x_11);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_39 = x_17;
} else {
 lean_dec_ref(x_17);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_7, 0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_12);
lean_ctor_set(x_41, 1, x_38);
lean_inc(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_11, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_12, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_17, 1);
x_50 = lean_ctor_get(x_17, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_18, 0);
lean_inc(x_51);
x_52 = l_Lake_ToolchainVer_decLe(x_46, x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_2, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_2, 0);
lean_dec(x_55);
x_56 = l_Lake_ToolchainVer_decLt(x_51, x_46);
lean_dec(x_51);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_12);
x_57 = lean_ctor_get(x_7, 0);
lean_inc(x_57);
lean_ctor_set(x_17, 1, x_46);
lean_ctor_set(x_17, 0, x_57);
x_58 = lean_array_push(x_49, x_17);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_18);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_2);
lean_ctor_set(x_11, 0, x_59);
return x_11;
}
else
{
lean_object* x_60; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_18);
x_60 = lean_ctor_get(x_7, 0);
lean_ctor_set(x_17, 0, x_12);
lean_inc(x_60);
lean_ctor_set(x_2, 0, x_60);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
}
else
{
uint8_t x_61; 
lean_dec(x_2);
x_61 = l_Lake_ToolchainVer_decLt(x_51, x_46);
lean_dec(x_51);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_12);
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
lean_ctor_set(x_17, 1, x_46);
lean_ctor_set(x_17, 0, x_62);
x_63 = lean_array_push(x_49, x_17);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_18);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_47);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_11, 0, x_65);
return x_11;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_18);
x_66 = lean_ctor_get(x_7, 0);
lean_ctor_set(x_17, 0, x_12);
lean_inc(x_66);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_17);
lean_ctor_set(x_11, 0, x_67);
return x_11;
}
}
}
else
{
lean_dec(x_51);
lean_free_object(x_17);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_18);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_17, 1);
lean_inc(x_68);
lean_dec(x_17);
x_69 = lean_ctor_get(x_18, 0);
lean_inc(x_69);
x_70 = l_Lake_ToolchainVer_decLe(x_46, x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_71 = x_2;
} else {
 lean_dec_ref(x_2);
 x_71 = lean_box(0);
}
x_72 = l_Lake_ToolchainVer_decLt(x_69, x_46);
lean_dec(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_12);
x_73 = lean_ctor_get(x_7, 0);
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_46);
x_75 = lean_array_push(x_68, x_74);
if (lean_is_scalar(x_71)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_71;
}
lean_ctor_set(x_76, 0, x_18);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_47);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_11, 0, x_77);
return x_11;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_18);
x_78 = lean_ctor_get(x_7, 0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_12);
lean_ctor_set(x_79, 1, x_68);
lean_inc(x_78);
if (lean_is_scalar(x_71)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_71;
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_11, 0, x_80);
return x_11;
}
}
else
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_18);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_81 = lean_ctor_get(x_11, 1);
lean_inc(x_81);
lean_dec(x_11);
x_82 = lean_ctor_get(x_12, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_2, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_17, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_85 = x_17;
} else {
 lean_dec_ref(x_17);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_18, 0);
lean_inc(x_86);
x_87 = l_Lake_ToolchainVer_decLe(x_82, x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_88 = x_2;
} else {
 lean_dec_ref(x_2);
 x_88 = lean_box(0);
}
x_89 = l_Lake_ToolchainVer_decLt(x_86, x_82);
lean_dec(x_86);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_12);
x_90 = lean_ctor_get(x_7, 0);
lean_inc(x_90);
if (lean_is_scalar(x_85)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_85;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_82);
x_92 = lean_array_push(x_84, x_91);
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_18);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_81);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_18);
x_96 = lean_ctor_get(x_7, 0);
if (lean_is_scalar(x_85)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_85;
}
lean_ctor_set(x_97, 0, x_12);
lean_ctor_set(x_97, 1, x_84);
lean_inc(x_96);
if (lean_is_scalar(x_88)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_88;
}
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_81);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_18);
lean_dec(x_12);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_81);
return x_100;
}
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; uint8_t x_108; 
lean_dec(x_2);
x_101 = lean_ctor_get(x_11, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_11, 1);
lean_inc(x_102);
lean_dec(x_11);
x_103 = lean_io_error_to_string(x_101);
x_104 = lean_box(3);
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
x_106 = lean_unbox(x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_106);
x_107 = lean_apply_2(x_4, x_105, x_102);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_107, 0);
lean_dec(x_109);
x_110 = lean_box(0);
lean_ctor_set_tag(x_107, 1);
lean_ctor_set(x_107, 0, x_110);
return x_107;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n  ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n    from ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__0;
x_11 = lean_string_append(x_5, x_10);
x_12 = l_Lake_ToolchainVer_toString(x_9);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
lean_inc(x_1);
x_18 = l_Lean_Name_toString(x_8, x_17, x_1);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_19;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_6);
x_10 = lean_apply_4(x_1, x_5, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
x_7 = x_12;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("updating toolchain to '", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot auto-restart; you will need to manually restart Lake", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Workspace_updateToolchain___closed__1;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static uint8_t _init_l_Lake_Workspace_updateToolchain___closed__3() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 4;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no Elan detected; you will need to manually restart Lake", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Workspace_updateToolchain___closed__4;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("restarting Lake via Elan", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Workspace_updateToolchain___closed__6;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 0, 3);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 2, x_5);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("run", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--install", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_updateToolchain___closed__9;
x_2 = l_Lake_Workspace_updateToolchain___closed__12;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_updateToolchain___closed__10;
x_2 = l_Lake_Workspace_updateToolchain___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toolchain not updated; no toolchain information found", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Workspace_updateToolchain___closed__15;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toolchain not updated; already up-to-date", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Workspace_updateToolchain___closed__17;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toolchain not updated; multiple toolchain candidates:", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toolchain not updated; multiple toolchain candidates:\n  ", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateToolchain___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_dec(x_1);
x_165 = lean_ctor_get(x_16, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_16, 1);
lean_inc(x_166);
lean_dec(x_16);
x_167 = l_Lake_Workspace_updateToolchain___elam__0___closed__0;
lean_inc(x_166);
x_168 = l_System_FilePath_join(x_166, x_167);
x_169 = l_Lake_ToolchainVer_ofFile_x3f(x_168, x_4);
lean_dec(x_168);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = lean_ctor_get(x_169, 1);
x_173 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
x_174 = lean_unsigned_to_nat(0u);
x_219 = l_Lake_Workspace_updateToolchain___closed__21;
x_220 = lean_array_get_size(x_2);
x_221 = lean_nat_dec_lt(x_174, x_220);
if (x_221 == 0)
{
lean_dec(x_220);
lean_free_object(x_169);
lean_inc(x_171);
x_185 = x_165;
x_186 = x_171;
x_187 = x_219;
x_188 = x_172;
goto block_218;
}
else
{
uint8_t x_222; 
x_222 = lean_nat_dec_le(x_220, x_220);
if (x_222 == 0)
{
lean_dec(x_220);
lean_free_object(x_169);
lean_inc(x_171);
x_185 = x_165;
x_186 = x_171;
x_187 = x_219;
x_188 = x_172;
goto block_218;
}
else
{
lean_object* x_223; lean_object* x_224; size_t x_225; size_t x_226; lean_object* x_227; 
lean_inc(x_171);
lean_ctor_set(x_169, 1, x_219);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_165);
lean_ctor_set(x_223, 1, x_169);
lean_inc(x_166);
x_224 = lean_alloc_closure((void*)(l_Lake_Workspace_updateToolchain___elam__0___boxed), 5, 1);
lean_closure_set(x_224, 0, x_166);
x_225 = 0;
x_226 = lean_usize_of_nat(x_220);
lean_dec(x_220);
lean_inc(x_3);
x_227 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__1(x_224, x_2, x_225, x_226, x_223, x_3, x_172);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_ctor_get(x_229, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_229, 1);
lean_inc(x_233);
lean_dec(x_229);
x_185 = x_231;
x_186 = x_232;
x_187 = x_233;
x_188 = x_230;
goto block_218;
}
else
{
uint8_t x_234; 
lean_dec(x_171);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
x_234 = !lean_is_exclusive(x_227);
if (x_234 == 0)
{
return x_227;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_227, 0);
x_236 = lean_ctor_get(x_227, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_227);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
block_184:
{
uint8_t x_179; 
x_179 = lean_nat_dec_lt(x_174, x_175);
if (x_179 == 0)
{
lean_dec(x_176);
lean_dec(x_175);
x_5 = x_177;
x_6 = x_178;
goto block_15;
}
else
{
uint8_t x_180; 
x_180 = lean_nat_dec_le(x_175, x_175);
if (x_180 == 0)
{
lean_dec(x_176);
lean_dec(x_175);
x_5 = x_177;
x_6 = x_178;
goto block_15;
}
else
{
size_t x_181; size_t x_182; lean_object* x_183; 
x_181 = 0;
x_182 = lean_usize_of_nat(x_175);
lean_dec(x_175);
x_183 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0(x_173, x_176, x_181, x_182, x_178);
lean_dec(x_176);
x_5 = x_177;
x_6 = x_183;
goto block_15;
}
}
}
block_218:
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_array_get_size(x_187);
x_190 = lean_nat_dec_lt(x_174, x_189);
if (x_190 == 0)
{
lean_dec(x_189);
lean_dec(x_187);
lean_dec(x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_dec(x_171);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
x_191 = l_Lake_Workspace_updateToolchain___closed__16;
x_192 = lean_apply_2(x_3, x_191, x_188);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
return x_192;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_192);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_186, 0);
lean_inc(x_197);
lean_dec(x_186);
x_198 = l_Lake_joinRelative(x_166, x_167);
if (lean_obj_tag(x_171) == 0)
{
x_19 = x_198;
x_20 = x_197;
x_21 = x_188;
x_22 = x_190;
goto block_164;
}
else
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_171, 0);
lean_inc(x_199);
lean_dec(x_171);
x_200 = l_Lake_decEqToolchainVer____x40_Lake_Util_Version___hyg_1773_(x_199, x_197);
lean_dec(x_199);
if (x_200 == 0)
{
x_19 = x_198;
x_20 = x_197;
x_21 = x_188;
x_22 = x_200;
goto block_164;
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_18);
lean_dec(x_17);
x_201 = l_Lake_Workspace_updateToolchain___closed__18;
x_202 = lean_apply_2(x_3, x_201, x_188);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_202, 0);
lean_dec(x_204);
x_205 = lean_box(0);
lean_ctor_set(x_202, 0, x_205);
return x_202;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
lean_dec(x_202);
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
}
}
else
{
lean_dec(x_171);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_209; 
lean_dec(x_185);
x_209 = l_Lake_Workspace_updateToolchain___closed__19;
x_175 = x_189;
x_176 = x_187;
x_177 = x_188;
x_178 = x_209;
goto block_184;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_186, 0);
lean_inc(x_210);
lean_dec(x_186);
x_211 = l_Lake_Workspace_updateToolchain___closed__20;
x_212 = l_Lake_ToolchainVer_toString(x_210);
x_213 = lean_string_append(x_211, x_212);
lean_dec(x_212);
x_214 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__1;
x_215 = lean_string_append(x_213, x_214);
x_216 = l_Lean_Name_toString(x_185, x_190, x_173);
x_217 = lean_string_append(x_215, x_216);
lean_dec(x_216);
x_175 = x_189;
x_176 = x_187;
x_177 = x_188;
x_178 = x_217;
goto block_184;
}
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_238 = lean_ctor_get(x_169, 0);
x_239 = lean_ctor_get(x_169, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_169);
x_240 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
x_241 = lean_unsigned_to_nat(0u);
x_284 = l_Lake_Workspace_updateToolchain___closed__21;
x_285 = lean_array_get_size(x_2);
x_286 = lean_nat_dec_lt(x_241, x_285);
if (x_286 == 0)
{
lean_dec(x_285);
lean_inc(x_238);
x_252 = x_165;
x_253 = x_238;
x_254 = x_284;
x_255 = x_239;
goto block_283;
}
else
{
uint8_t x_287; 
x_287 = lean_nat_dec_le(x_285, x_285);
if (x_287 == 0)
{
lean_dec(x_285);
lean_inc(x_238);
x_252 = x_165;
x_253 = x_238;
x_254 = x_284;
x_255 = x_239;
goto block_283;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; size_t x_291; size_t x_292; lean_object* x_293; 
lean_inc(x_238);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_238);
lean_ctor_set(x_288, 1, x_284);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_165);
lean_ctor_set(x_289, 1, x_288);
lean_inc(x_166);
x_290 = lean_alloc_closure((void*)(l_Lake_Workspace_updateToolchain___elam__0___boxed), 5, 1);
lean_closure_set(x_290, 0, x_166);
x_291 = 0;
x_292 = lean_usize_of_nat(x_285);
lean_dec(x_285);
lean_inc(x_3);
x_293 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__1(x_290, x_2, x_291, x_292, x_289, x_3, x_239);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_293, 1);
lean_inc(x_296);
lean_dec(x_293);
x_297 = lean_ctor_get(x_294, 0);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_ctor_get(x_295, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_295, 1);
lean_inc(x_299);
lean_dec(x_295);
x_252 = x_297;
x_253 = x_298;
x_254 = x_299;
x_255 = x_296;
goto block_283;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_238);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
x_300 = lean_ctor_get(x_293, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_293, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_302 = x_293;
} else {
 lean_dec_ref(x_293);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
}
block_251:
{
uint8_t x_246; 
x_246 = lean_nat_dec_lt(x_241, x_242);
if (x_246 == 0)
{
lean_dec(x_243);
lean_dec(x_242);
x_5 = x_244;
x_6 = x_245;
goto block_15;
}
else
{
uint8_t x_247; 
x_247 = lean_nat_dec_le(x_242, x_242);
if (x_247 == 0)
{
lean_dec(x_243);
lean_dec(x_242);
x_5 = x_244;
x_6 = x_245;
goto block_15;
}
else
{
size_t x_248; size_t x_249; lean_object* x_250; 
x_248 = 0;
x_249 = lean_usize_of_nat(x_242);
lean_dec(x_242);
x_250 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0(x_240, x_243, x_248, x_249, x_245);
lean_dec(x_243);
x_5 = x_244;
x_6 = x_250;
goto block_15;
}
}
}
block_283:
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_array_get_size(x_254);
x_257 = lean_nat_dec_lt(x_241, x_256);
if (x_257 == 0)
{
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_238);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
x_258 = l_Lake_Workspace_updateToolchain___closed__16;
x_259 = lean_apply_2(x_3, x_258, x_255);
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
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_253, 0);
lean_inc(x_264);
lean_dec(x_253);
x_265 = l_Lake_joinRelative(x_166, x_167);
if (lean_obj_tag(x_238) == 0)
{
x_19 = x_265;
x_20 = x_264;
x_21 = x_255;
x_22 = x_257;
goto block_164;
}
else
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_238, 0);
lean_inc(x_266);
lean_dec(x_238);
x_267 = l_Lake_decEqToolchainVer____x40_Lake_Util_Version___hyg_1773_(x_266, x_264);
lean_dec(x_266);
if (x_267 == 0)
{
x_19 = x_265;
x_20 = x_264;
x_21 = x_255;
x_22 = x_267;
goto block_164;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_18);
lean_dec(x_17);
x_268 = l_Lake_Workspace_updateToolchain___closed__18;
x_269 = lean_apply_2(x_3, x_268, x_255);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
x_272 = lean_box(0);
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_271;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_270);
return x_273;
}
}
}
}
else
{
lean_dec(x_238);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_274; 
lean_dec(x_252);
x_274 = l_Lake_Workspace_updateToolchain___closed__19;
x_242 = x_256;
x_243 = x_254;
x_244 = x_255;
x_245 = x_274;
goto block_251;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_275 = lean_ctor_get(x_253, 0);
lean_inc(x_275);
lean_dec(x_253);
x_276 = l_Lake_Workspace_updateToolchain___closed__20;
x_277 = l_Lake_ToolchainVer_toString(x_275);
x_278 = lean_string_append(x_276, x_277);
lean_dec(x_277);
x_279 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__1;
x_280 = lean_string_append(x_278, x_279);
x_281 = l_Lean_Name_toString(x_252, x_257, x_240);
x_282 = lean_string_append(x_280, x_281);
lean_dec(x_281);
x_242 = x_256;
x_243 = x_254;
x_244 = x_255;
x_245 = x_282;
goto block_251;
}
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; uint8_t x_311; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_18);
lean_dec(x_17);
x_304 = lean_ctor_get(x_169, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_169, 1);
lean_inc(x_305);
lean_dec(x_169);
x_306 = lean_io_error_to_string(x_304);
x_307 = lean_box(3);
x_308 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_308, 0, x_306);
x_309 = lean_unbox(x_307);
lean_ctor_set_uint8(x_308, sizeof(void*)*1, x_309);
x_310 = lean_apply_2(x_3, x_308, x_305);
x_311 = !lean_is_exclusive(x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_310, 0);
lean_dec(x_312);
x_313 = lean_box(0);
lean_ctor_set_tag(x_310, 1);
lean_ctor_set(x_310, 0, x_313);
return x_310;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_310, 1);
lean_inc(x_314);
lean_dec(x_310);
x_315 = lean_box(0);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
block_15:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_box(2);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_apply_2(x_3, x_8, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
block_164:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = l_Lake_Workspace_updateToolchain___closed__0;
x_24 = l_Lake_ToolchainVer_toString(x_20);
x_25 = lean_string_append(x_23, x_24);
x_26 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
lean_inc(x_3);
x_31 = lean_apply_2(x_3, x_29, x_21);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_IO_FS_writeFile(x_19, x_24, x_32);
lean_dec(x_19);
if (lean_obj_tag(x_33) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_dec(x_24);
lean_dec(x_17);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lake_Workspace_updateToolchain___closed__2;
lean_inc(x_3);
x_36 = lean_apply_2(x_3, x_35, x_34);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lake_Workspace_updateToolchain___closed__3;
x_39 = lean_io_exit(x_38, x_37);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_io_error_to_string(x_44);
x_47 = lean_box(3);
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_apply_2(x_3, x_48, x_45);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_17, 2);
lean_inc(x_57);
lean_dec(x_17);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
lean_dec(x_24);
lean_dec(x_18);
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
lean_dec(x_33);
x_59 = l_Lake_Workspace_updateToolchain___closed__5;
lean_inc(x_3);
x_60 = lean_apply_2(x_3, x_59, x_58);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lake_Workspace_updateToolchain___closed__3;
x_63 = lean_io_exit(x_62, x_61);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; 
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_io_error_to_string(x_68);
x_71 = lean_box(3);
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
x_73 = lean_unbox(x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_73);
x_74 = lean_apply_2(x_3, x_72, x_69);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_81 = lean_ctor_get(x_33, 1);
lean_inc(x_81);
lean_dec(x_33);
x_82 = lean_ctor_get(x_18, 0);
lean_inc(x_82);
lean_dec(x_18);
x_83 = lean_ctor_get(x_57, 0);
lean_inc(x_83);
lean_dec(x_57);
x_84 = l_Lake_Workspace_updateToolchain___closed__7;
lean_inc(x_3);
x_85 = lean_apply_2(x_3, x_84, x_81);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = l_Lake_Workspace_updateToolchain___closed__8;
x_89 = l_Lake_Workspace_updateToolchain___closed__11;
x_90 = l_Lake_Workspace_updateToolchain___closed__14;
x_91 = lean_array_push(x_90, x_24);
x_92 = lean_array_push(x_91, x_89);
x_93 = l_Array_append___redArg(x_92, x_82);
lean_dec(x_82);
x_94 = lean_box(0);
x_95 = l_Lake_Env_noToolchainVars;
x_96 = lean_box(1);
x_97 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_87);
lean_ctor_set(x_97, 2, x_93);
lean_ctor_set(x_97, 3, x_94);
lean_ctor_set(x_97, 4, x_95);
x_98 = lean_unbox(x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*5, x_98);
lean_ctor_set_uint8(x_97, sizeof(void*)*5 + 1, x_22);
x_99 = lean_io_process_spawn(x_97, x_86);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_io_process_child_wait(x_88, x_100, x_101);
lean_dec(x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint32_t x_105; uint8_t x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_unbox_uint32(x_103);
lean_dec(x_103);
x_106 = lean_uint32_to_uint8(x_105);
x_107 = lean_io_exit(x_106, x_104);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
return x_107;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_107);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
x_114 = lean_io_error_to_string(x_112);
x_115 = lean_box(3);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
x_117 = lean_unbox(x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_117);
x_118 = lean_apply_2(x_3, x_116, x_113);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_118, 0);
lean_dec(x_120);
x_121 = lean_box(0);
lean_ctor_set_tag(x_118, 1);
lean_ctor_set(x_118, 0, x_121);
return x_118;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; uint8_t x_132; 
x_125 = lean_ctor_get(x_102, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_102, 1);
lean_inc(x_126);
lean_dec(x_102);
x_127 = lean_io_error_to_string(x_125);
x_128 = lean_box(3);
x_129 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_129, 0, x_127);
x_130 = lean_unbox(x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_130);
x_131 = lean_apply_2(x_3, x_129, x_126);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 0);
lean_dec(x_133);
x_134 = lean_box(0);
lean_ctor_set_tag(x_131, 1);
lean_ctor_set(x_131, 0, x_134);
return x_131;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; 
x_138 = lean_ctor_get(x_99, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_99, 1);
lean_inc(x_139);
lean_dec(x_99);
x_140 = lean_io_error_to_string(x_138);
x_141 = lean_box(3);
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_140);
x_143 = lean_unbox(x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_143);
x_144 = lean_apply_2(x_3, x_142, x_139);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 0);
lean_dec(x_146);
x_147 = lean_box(0);
lean_ctor_set_tag(x_144, 1);
lean_ctor_set(x_144, 0, x_147);
return x_144;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; uint8_t x_158; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
x_151 = lean_ctor_get(x_33, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_33, 1);
lean_inc(x_152);
lean_dec(x_33);
x_153 = lean_io_error_to_string(x_151);
x_154 = lean_box(3);
x_155 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_155, 0, x_153);
x_156 = lean_unbox(x_154);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_156);
x_157 = lean_apply_2(x_3, x_155, x_152);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
lean_dec(x_159);
x_160 = lean_box(0);
lean_ctor_set_tag(x_157, 1);
lean_ctor_set(x_157, 0, x_160);
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_updateToolchain___elam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
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
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_2(x_3, x_2, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
x_14 = lean_box(1);
x_15 = l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_18 = lean_unbox(x_14);
lean_inc(x_4);
x_19 = l_Lake_loadDepPackage(x_4, x_13, x_1, x_18, x_5, x_17, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_51; uint8_t x_52; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_51 = lean_array_get_size(x_23);
x_52 = lean_nat_dec_lt(x_16, x_51);
if (x_52 == 0)
{
lean_dec(x_51);
lean_dec(x_23);
x_24 = x_6;
x_25 = x_21;
goto block_50;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_51, x_51);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec(x_23);
x_24 = x_6;
x_25 = x_21;
goto block_50;
}
else
{
lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0___boxed), 4, 0);
x_55 = lean_box(0);
x_56 = 0;
x_57 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_58 = l_Array_foldlMUnsafe_fold___redArg(x_15, x_54, x_23, x_56, x_57, x_55);
lean_inc(x_7);
x_59 = lean_apply_2(x_58, x_7, x_21);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_24 = x_6;
x_25 = x_60;
goto block_50;
}
else
{
uint8_t x_61; 
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_59);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
block_50:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_inc(x_7);
lean_inc(x_26);
x_27 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_2, x_3, x_4, x_26, x_7, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_26, x_24, x_7, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_22);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_29, 0, x_35);
return x_29;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
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
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_22);
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
lean_dec(x_22);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_7);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_19);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_19, 1);
x_67 = lean_ctor_get(x_19, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_20, 1);
lean_inc(x_68);
lean_dec(x_20);
x_69 = lean_array_get_size(x_68);
x_70 = lean_nat_dec_lt(x_16, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_7);
x_71 = lean_box(0);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_71);
return x_19;
}
else
{
uint8_t x_72; 
lean_free_object(x_19);
x_72 = lean_nat_dec_le(x_69, x_69);
if (x_72 == 0)
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_7);
x_9 = x_66;
goto block_12;
}
else
{
lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0___boxed), 4, 0);
x_74 = lean_box(0);
x_75 = 0;
x_76 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_77 = l_Array_foldlMUnsafe_fold___redArg(x_15, x_73, x_68, x_75, x_76, x_74);
x_78 = lean_apply_2(x_77, x_7, x_66);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_9 = x_79;
goto block_12;
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_78);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_19, 1);
lean_inc(x_84);
lean_dec(x_19);
x_85 = lean_ctor_get(x_20, 1);
lean_inc(x_85);
lean_dec(x_20);
x_86 = lean_array_get_size(x_85);
x_87 = lean_nat_dec_lt(x_16, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_7);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
return x_89;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_86, x_86);
if (x_90 == 0)
{
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_7);
x_9 = x_84;
goto block_12;
}
else
{
lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0___boxed), 4, 0);
x_92 = lean_box(0);
x_93 = 0;
x_94 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_95 = l_Array_foldlMUnsafe_fold___redArg(x_15, x_91, x_85, x_93, x_94, x_92);
x_96 = lean_apply_2(x_95, x_7, x_84);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_9 = x_97;
goto block_12;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
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
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; 
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_4);
x_12 = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(x_4, x_2, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
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
x_17 = lean_ctor_get(x_3, 4);
lean_inc(x_17);
x_18 = lean_box(1);
x_19 = l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_22 = lean_unbox(x_18);
lean_inc(x_15);
x_23 = l_Lake_loadDepPackage(x_15, x_17, x_1, x_22, x_4, x_21, x_14);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_55; uint8_t x_56; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_55 = lean_array_get_size(x_27);
x_56 = lean_nat_dec_lt(x_20, x_55);
if (x_56 == 0)
{
lean_dec(x_55);
lean_dec(x_27);
x_28 = x_16;
x_29 = x_25;
goto block_54;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_55, x_55);
if (x_57 == 0)
{
lean_dec(x_55);
lean_dec(x_27);
x_28 = x_16;
x_29 = x_25;
goto block_54;
}
else
{
lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; 
x_58 = l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep___closed__0;
x_59 = lean_box(0);
x_60 = 0;
x_61 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_62 = l_Array_foldlMUnsafe_fold___redArg(x_19, x_58, x_27, x_60, x_61, x_59);
lean_inc(x_6);
x_63 = lean_apply_2(x_62, x_6, x_25);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_28 = x_16;
x_29 = x_64;
goto block_54;
}
else
{
uint8_t x_65; 
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
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
}
block_54:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_inc(x_6);
lean_inc(x_30);
x_31 = l___private_Lake_Load_Resolve_0__Lake_validateDep(x_2, x_3, x_15, x_30, x_6, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(x_30, x_28, x_6, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_26);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
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
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_26);
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
return x_33;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_6);
x_50 = !lean_is_exclusive(x_31);
if (x_50 == 0)
{
return x_31;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_31, 0);
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_31);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_23);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_23, 1);
x_71 = lean_ctor_get(x_23, 0);
lean_dec(x_71);
x_72 = lean_ctor_get(x_24, 1);
lean_inc(x_72);
lean_dec(x_24);
x_73 = lean_array_get_size(x_72);
x_74 = lean_nat_dec_lt(x_20, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_6);
x_75 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_75);
return x_23;
}
else
{
uint8_t x_76; 
lean_free_object(x_23);
x_76 = lean_nat_dec_le(x_73, x_73);
if (x_76 == 0)
{
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_6);
x_8 = x_70;
goto block_11;
}
else
{
lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; 
x_77 = l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep___closed__0;
x_78 = lean_box(0);
x_79 = 0;
x_80 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_81 = l_Array_foldlMUnsafe_fold___redArg(x_19, x_77, x_72, x_79, x_80, x_78);
x_82 = lean_apply_2(x_81, x_6, x_70);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_8 = x_83;
goto block_11;
}
else
{
uint8_t x_84; 
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
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_23, 1);
lean_inc(x_88);
lean_dec(x_23);
x_89 = lean_ctor_get(x_24, 1);
lean_inc(x_89);
lean_dec(x_24);
x_90 = lean_array_get_size(x_89);
x_91 = lean_nat_dec_lt(x_20, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_6);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_88);
return x_93;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_le(x_90, x_90);
if (x_94 == 0)
{
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_6);
x_8 = x_88;
goto block_11;
}
else
{
lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; 
x_95 = l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep___closed__0;
x_96 = lean_box(0);
x_97 = 0;
x_98 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_99 = l_Array_foldlMUnsafe_fold___redArg(x_19, x_95, x_89, x_97, x_98, x_96);
x_100 = lean_apply_2(x_99, x_6, x_88);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_8 = x_101;
goto block_11;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
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
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_12);
if (x_106 == 0)
{
return x_12;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_12, 0);
x_108 = lean_ctor_get(x_12, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_12);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateDep___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_name_eq(x_7, x_9);
x_11 = l_instDecidableNot___redArg(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_76; lean_object* x_77; lean_object* x_90; uint8_t x_91; 
x_14 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
x_90 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__6;
x_91 = lean_name_eq(x_9, x_90);
if (x_91 == 0)
{
x_76 = x_1;
x_77 = x_6;
goto block_89;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_4, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 4);
lean_inc(x_93);
lean_dec(x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_dec(x_93);
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_93, 2);
lean_inc(x_105);
lean_dec(x_93);
if (lean_obj_tag(x_105) == 0)
{
goto block_104;
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__8;
x_109 = l_String_quote(x_107);
lean_dec(x_107);
lean_ctor_set_tag(x_105, 3);
lean_ctor_set(x_105, 0, x_109);
x_110 = lean_unsigned_to_nat(120u);
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_format_pretty(x_105, x_110, x_111, x_111);
x_113 = lean_string_append(x_108, x_112);
lean_dec(x_112);
x_94 = x_113;
goto block_102;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_114 = lean_ctor_get(x_105, 0);
lean_inc(x_114);
lean_dec(x_105);
x_115 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__8;
x_116 = l_String_quote(x_114);
lean_dec(x_114);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_unsigned_to_nat(120u);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_format_pretty(x_117, x_118, x_119, x_119);
x_121 = lean_string_append(x_115, x_120);
lean_dec(x_120);
x_94 = x_121;
goto block_102;
}
}
}
block_102:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
lean_inc(x_7);
x_95 = l_Lean_Name_toString(x_7, x_91, x_14);
x_96 = l_Lake_stdMismatchError(x_95, x_94);
lean_dec(x_94);
lean_dec(x_95);
x_97 = lean_box(3);
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
x_99 = lean_unbox(x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_99);
lean_inc(x_1);
x_100 = lean_apply_2(x_1, x_98, x_6);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_76 = x_1;
x_77 = x_101;
goto block_89;
}
block_104:
{
lean_object* x_103; 
x_103 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__7;
x_94 = x_103;
goto block_102;
}
}
block_39:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_Name_toString(x_17, x_11, x_14);
x_19 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Name_toString(x_7, x_11, x_14);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lean_Name_toString(x_9, x_11, x_14);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_box(3);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = lean_apply_2(x_15, x_30, x_16);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
block_60:
{
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
lean_inc(x_9);
x_46 = l_Lean_Name_toString(x_9, x_40, x_14);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_8);
lean_dec(x_8);
x_51 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__4;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_io_error_to_string(x_44);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_55 = lean_box(3);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_unbox(x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
lean_inc(x_41);
x_58 = lean_apply_2(x_41, x_56, x_43);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_15 = x_41;
x_16 = x_59;
goto block_39;
}
else
{
lean_dec(x_42);
lean_dec(x_8);
x_15 = x_41;
x_16 = x_43;
goto block_39;
}
}
block_75:
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_array_get_size(x_62);
x_68 = lean_nat_dec_lt(x_64, x_67);
if (x_68 == 0)
{
lean_dec(x_67);
lean_dec(x_62);
x_40 = x_61;
x_41 = x_63;
x_42 = x_65;
x_43 = x_66;
goto block_60;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_67, x_67);
if (x_69 == 0)
{
lean_dec(x_67);
lean_dec(x_62);
x_40 = x_61;
x_41 = x_63;
x_42 = x_65;
x_43 = x_66;
goto block_60;
}
else
{
lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = 0;
x_72 = lean_usize_of_nat(x_67);
lean_dec(x_67);
lean_inc(x_63);
x_73 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_62, x_71, x_72, x_70, x_63, x_66);
lean_dec(x_62);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_40 = x_61;
x_41 = x_63;
x_42 = x_65;
x_43 = x_74;
goto block_60;
}
}
}
block_89:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_4, 2);
lean_inc(x_78);
lean_dec(x_4);
x_79 = lean_ctor_get(x_78, 4);
lean_inc(x_79);
lean_dec(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_dec(x_79);
lean_dec(x_8);
x_15 = x_76;
x_16 = x_77;
goto block_39;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_79);
x_80 = lean_unsigned_to_nat(0u);
x_81 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_82 = l_IO_FS_removeDirAll(x_8, x_77);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_83);
x_61 = x_11;
x_62 = x_81;
x_63 = x_76;
x_64 = x_80;
x_65 = x_85;
x_66 = x_84;
goto block_75;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_dec(x_82);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_86);
x_61 = x_11;
x_62 = x_81;
x_63 = x_76;
x_64 = x_80;
x_65 = x_88;
x_66 = x_87;
goto block_75;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_78; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 6);
lean_inc(x_7);
x_8 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
x_9 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___elam__1___boxed), 6, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = l_Lake_joinRelative(x_6, x_7);
lean_dec(x_7);
x_67 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
lean_inc(x_10);
x_78 = l_Lake_Manifest_load(x_10, x_4);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_79);
x_68 = x_81;
x_69 = x_80;
goto block_77;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_dec(x_78);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_82);
x_68 = x_84;
x_69 = x_83;
goto block_77;
}
block_66:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 11)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_14);
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Name_toString(x_5, x_16, x_8);
x_18 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_10);
lean_dec(x_10);
x_21 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_box(2);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_25);
x_26 = lean_apply_2(x_1, x_24, x_13);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_12);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_10);
x_34 = lean_box(1);
x_35 = lean_unbox(x_34);
x_36 = l_Lean_Name_toString(x_5, x_35, x_8);
x_37 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_io_error_to_string(x_14);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
x_41 = lean_box(2);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_43);
x_44 = lean_apply_2(x_1, x_42, x_13);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_12);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_12);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_5);
x_52 = lean_ctor_get(x_11, 0);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_53);
x_56 = lean_box(0);
x_57 = lean_nat_dec_lt(x_54, x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_9);
lean_dec(x_1);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_12);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_13);
return x_59;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_le(x_55, x_55);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_9);
lean_dec(x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_12);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_13);
return x_62;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_65 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(x_9, x_53, x_63, x_64, x_56, x_12, x_1, x_13);
lean_dec(x_53);
return x_65;
}
}
}
}
block_77:
{
uint8_t x_70; 
x_70 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6;
if (x_70 == 0)
{
x_11 = x_68;
x_12 = x_3;
x_13 = x_69;
goto block_66;
}
else
{
uint8_t x_71; 
x_71 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7;
if (x_71 == 0)
{
x_11 = x_68;
x_12 = x_3;
x_13 = x_69;
goto block_66;
}
else
{
lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_box(0);
x_73 = 0;
x_74 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8;
lean_inc(x_1);
x_75 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_67, x_73, x_74, x_72, x_1, x_69);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_11 = x_68;
x_12 = x_3;
x_13 = x_76;
goto block_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_6);
x_10 = lean_apply_4(x_1, x_5, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
x_7 = x_12;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 4);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
lean_inc(x_5);
lean_inc(x_15);
x_19 = l_Lake_loadDepPackage(x_15, x_16, x_1, x_2, x_5, x_18, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_57; uint8_t x_58; 
lean_dec(x_4);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_57 = lean_array_get_size(x_23);
x_58 = lean_nat_dec_lt(x_17, x_57);
if (x_58 == 0)
{
lean_dec(x_57);
lean_dec(x_23);
lean_dec(x_3);
x_25 = x_22;
x_26 = x_7;
x_27 = x_21;
goto block_56;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_57, x_57);
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_23);
lean_dec(x_3);
x_25 = x_22;
x_26 = x_7;
x_27 = x_21;
goto block_56;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
x_60 = lean_box(0);
x_61 = 0;
x_62 = lean_usize_of_nat(x_57);
lean_dec(x_57);
lean_inc(x_8);
x_63 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_3, x_23, x_61, x_62, x_60, x_8, x_21);
lean_dec(x_23);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_25 = x_22;
x_26 = x_7;
x_27 = x_64;
goto block_56;
}
else
{
uint8_t x_65; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
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
}
block_56:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
lean_inc(x_28);
lean_inc(x_8);
x_30 = l___private_Lake_Load_Resolve_0__Lake_validateDep___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__0(x_8, x_24, x_14, x_15, x_28, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_28);
x_32 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__1(x_8, x_28, x_26, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = l_Lake_Workspace_addPackage(x_28, x_29);
lean_ctor_set(x_34, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_Lake_Workspace_addPackage(x_28, x_29);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_32, 0, x_40);
return x_32;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
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
x_45 = l_Lake_Workspace_addPackage(x_28, x_29);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_29);
lean_dec(x_28);
x_48 = !lean_is_exclusive(x_32);
if (x_48 == 0)
{
return x_32;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_32, 0);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_32);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_8);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
return x_30;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_30, 0);
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_30);
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
uint8_t x_69; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_19);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_19, 1);
x_71 = lean_ctor_get(x_19, 0);
lean_dec(x_71);
x_72 = lean_ctor_get(x_20, 1);
lean_inc(x_72);
lean_dec(x_20);
x_73 = lean_array_get_size(x_72);
x_74 = lean_nat_dec_lt(x_17, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_8);
lean_dec(x_4);
x_75 = lean_box(0);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_75);
return x_19;
}
else
{
uint8_t x_76; 
lean_free_object(x_19);
x_76 = lean_nat_dec_le(x_73, x_73);
if (x_76 == 0)
{
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_8);
lean_dec(x_4);
x_10 = x_70;
goto block_13;
}
else
{
lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; 
x_77 = lean_box(0);
x_78 = 0;
x_79 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_80 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_4, x_72, x_78, x_79, x_77, x_8, x_70);
lean_dec(x_72);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_10 = x_81;
goto block_13;
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
return x_80;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_80, 0);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_80);
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
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_19, 1);
lean_inc(x_86);
lean_dec(x_19);
x_87 = lean_ctor_get(x_20, 1);
lean_inc(x_87);
lean_dec(x_20);
x_88 = lean_array_get_size(x_87);
x_89 = lean_nat_dec_lt(x_17, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_4);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_86);
return x_91;
}
else
{
uint8_t x_92; 
x_92 = lean_nat_dec_le(x_88, x_88);
if (x_92 == 0)
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_4);
x_10 = x_86;
goto block_13;
}
else
{
lean_object* x_93; size_t x_94; size_t x_95; lean_object* x_96; 
x_93 = lean_box(0);
x_94 = 0;
x_95 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_96 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_4, x_87, x_94, x_95, x_93, x_8, x_86);
lean_dec(x_87);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_10 = x_97;
goto block_13;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
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
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___Lake_Workspace_updateAndMaterializeCore___elam__3_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_5, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_79; uint8_t x_80; 
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
lean_dec(x_3);
x_79 = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0;
x_80 = lean_string_dec_eq(x_27, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = l_Lake_joinRelative(x_27, x_79);
x_28 = x_81;
goto block_78;
}
else
{
x_28 = x_27;
goto block_78;
}
block_78:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_name_eq(x_26, x_32);
lean_dec(x_32);
lean_dec(x_26);
x_36 = l_instDecidableNot___redArg(x_35);
x_37 = l_System_FilePath_normalize(x_34);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_40 = l_Lake_Dependency_materialize(x_4, x_36, x_31, x_33, x_37, x_28, x_39, x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_38, x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_1);
x_11 = x_43;
x_12 = x_5;
x_13 = x_42;
goto block_19;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_1);
x_11 = x_43;
x_12 = x_5;
x_13 = x_42;
goto block_19;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_box(0);
x_49 = 0;
x_50 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_51 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_44, x_49, x_50, x_48, x_1, x_42);
lean_dec(x_44);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_11 = x_43;
x_12 = x_5;
x_13 = x_52;
goto block_19;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_40, 1);
x_55 = lean_ctor_get(x_40, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_dec(x_41);
x_57 = lean_array_get_size(x_56);
x_58 = lean_nat_dec_lt(x_38, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_1);
x_59 = lean_box(0);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_59);
return x_40;
}
else
{
uint8_t x_60; 
lean_free_object(x_40);
x_60 = lean_nat_dec_le(x_57, x_57);
if (x_60 == 0)
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_1);
x_7 = x_54;
goto block_10;
}
else
{
lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_box(0);
x_62 = 0;
x_63 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_64 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_56, x_62, x_63, x_61, x_1, x_54);
lean_dec(x_56);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_7 = x_65;
goto block_10;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_40, 1);
lean_inc(x_66);
lean_dec(x_40);
x_67 = lean_ctor_get(x_41, 1);
lean_inc(x_67);
lean_dec(x_41);
x_68 = lean_array_get_size(x_67);
x_69 = lean_nat_dec_lt(x_38, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_68, x_68);
if (x_72 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_1);
x_7 = x_66;
goto block_10;
}
else
{
lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_box(0);
x_74 = 0;
x_75 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_76 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_67, x_74, x_75, x_73, x_1, x_66);
lean_dec(x_67);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_7 = x_77;
goto block_10;
}
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_ctor_get(x_2, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_25, 0);
lean_inc(x_84);
lean_dec(x_25);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_dec(x_2);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec(x_83);
x_88 = l_System_FilePath_normalize(x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_91 = l_Lake_PackageEntry_materialize(x_84, x_85, x_86, x_88, x_90, x_6);
lean_dec(x_85);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_102; uint8_t x_103; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
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
x_102 = lean_array_get_size(x_96);
x_103 = lean_nat_dec_lt(x_89, x_102);
if (x_103 == 0)
{
lean_dec(x_102);
lean_dec(x_96);
lean_dec(x_1);
x_98 = x_93;
goto block_101;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_102, x_102);
if (x_104 == 0)
{
lean_dec(x_102);
lean_dec(x_96);
lean_dec(x_1);
x_98 = x_93;
goto block_101;
}
else
{
lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_box(0);
x_106 = 0;
x_107 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_108 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_96, x_106, x_107, x_105, x_1, x_93);
lean_dec(x_96);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_98 = x_109;
goto block_101;
}
}
block_101:
{
lean_object* x_99; lean_object* x_100; 
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_5);
if (lean_is_scalar(x_94)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_94;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
uint8_t x_110; 
lean_dec(x_5);
x_110 = !lean_is_exclusive(x_91);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_91, 1);
x_112 = lean_ctor_get(x_91, 0);
lean_dec(x_112);
x_113 = lean_ctor_get(x_92, 1);
lean_inc(x_113);
lean_dec(x_92);
x_114 = lean_array_get_size(x_113);
x_115 = lean_nat_dec_lt(x_89, x_114);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_1);
x_116 = lean_box(0);
lean_ctor_set_tag(x_91, 1);
lean_ctor_set(x_91, 0, x_116);
return x_91;
}
else
{
uint8_t x_117; 
lean_free_object(x_91);
x_117 = lean_nat_dec_le(x_114, x_114);
if (x_117 == 0)
{
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_1);
x_20 = x_111;
goto block_23;
}
else
{
lean_object* x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_box(0);
x_119 = 0;
x_120 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_121 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_113, x_119, x_120, x_118, x_1, x_111);
lean_dec(x_113);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_20 = x_122;
goto block_23;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_ctor_get(x_91, 1);
lean_inc(x_123);
lean_dec(x_91);
x_124 = lean_ctor_get(x_92, 1);
lean_inc(x_124);
lean_dec(x_92);
x_125 = lean_array_get_size(x_124);
x_126 = lean_nat_dec_lt(x_89, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_1);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_123);
return x_128;
}
else
{
uint8_t x_129; 
x_129 = lean_nat_dec_le(x_125, x_125);
if (x_129 == 0)
{
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_1);
x_20 = x_123;
goto block_23;
}
else
{
lean_object* x_130; size_t x_131; size_t x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_box(0);
x_131 = 0;
x_132 = lean_usize_of_nat(x_125);
lean_dec(x_125);
x_133 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_124, x_131, x_132, x_130, x_1, x_123);
lean_dec(x_124);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_20 = x_134;
goto block_23;
}
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_12, x_15, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_6);
x_12 = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___Lake_Workspace_updateAndMaterializeCore___elam__3_spec__0(x_6, x_4, x_2, x_3, x_5, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
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
x_17 = lean_ctor_get(x_3, 4);
lean_inc(x_17);
x_18 = lean_box(1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_21 = lean_unbox(x_18);
lean_inc(x_15);
x_22 = l_Lake_loadDepPackage(x_15, x_17, x_1, x_21, x_4, x_20, x_14);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_54; uint8_t x_55; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_54 = lean_array_get_size(x_26);
x_55 = lean_nat_dec_lt(x_19, x_54);
if (x_55 == 0)
{
lean_dec(x_54);
lean_dec(x_26);
x_27 = x_16;
x_28 = x_24;
goto block_53;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_54, x_54);
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec(x_26);
x_27 = x_16;
x_28 = x_24;
goto block_53;
}
else
{
lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_box(0);
x_58 = 0;
x_59 = lean_usize_of_nat(x_54);
lean_dec(x_54);
lean_inc(x_6);
x_60 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_26, x_58, x_59, x_57, x_6, x_24);
lean_dec(x_26);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_27 = x_16;
x_28 = x_61;
goto block_53;
}
}
block_53:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_inc(x_29);
lean_inc(x_6);
x_30 = l___private_Lake_Load_Resolve_0__Lake_validateDep___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__0(x_6, x_2, x_3, x_15, x_29, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__1(x_6, x_29, x_27, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_25);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_32, 0, x_38);
return x_32;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
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
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_25);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_25);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
return x_30;
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
return x_52;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_22);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_22, 1);
x_64 = lean_ctor_get(x_22, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_23, 1);
lean_inc(x_65);
lean_dec(x_23);
x_66 = lean_array_get_size(x_65);
x_67 = lean_nat_dec_lt(x_19, x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
x_68 = lean_box(0);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_68);
return x_22;
}
else
{
uint8_t x_69; 
lean_free_object(x_22);
x_69 = lean_nat_dec_le(x_66, x_66);
if (x_69 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
x_8 = x_63;
goto block_11;
}
else
{
lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = 0;
x_72 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_73 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_65, x_71, x_72, x_70, x_6, x_63);
lean_dec(x_65);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_8 = x_74;
goto block_11;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_22, 1);
lean_inc(x_75);
lean_dec(x_22);
x_76 = lean_ctor_get(x_23, 1);
lean_inc(x_76);
lean_dec(x_23);
x_77 = lean_array_get_size(x_76);
x_78 = lean_nat_dec_lt(x_19, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_6);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_77, x_77);
if (x_81 == 0)
{
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_6);
x_8 = x_75;
goto block_11;
}
else
{
lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_box(0);
x_83 = 0;
x_84 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_85 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_76, x_83, x_84, x_82, x_6, x_75);
lean_dec(x_76);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_8 = x_86;
goto block_11;
}
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_12);
if (x_87 == 0)
{
return x_12;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_12, 0);
x_89 = lean_ctor_get(x_12, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_12);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___lam__0(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = 1;
x_14 = lean_usize_add(x_1, x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0(x_2, x_3, x_4, x_14, x_5, x_11, x_6, x_12, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_box_usize(x_4);
x_15 = lean_box_usize(x_5);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_16 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___lam__0___boxed), 10, 6);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_15);
lean_closure_set(x_16, 5, x_7);
x_17 = lean_array_uget(x_3, x_4);
lean_dec(x_3);
x_18 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___lam__1), 7, 4);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_7);
lean_closure_set(x_18, 3, x_8);
x_19 = lean_apply_7(x_13, lean_box(0), lean_box(0), x_18, x_16, x_9, x_10, x_11);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_6);
x_24 = lean_apply_5(x_23, lean_box(0), x_1, x_9, x_10, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_8);
x_28 = lean_apply_5(x_26, lean_box(0), x_27, x_9, x_10, x_11);
return x_28;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14, x_9, x_15, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_3(x_1, x_2, x_3, x_8);
x_13 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_12, x_5, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_6(x_1, x_7, x_2, x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_1);
x_8 = lean_apply_5(x_2, lean_box(0), x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_name_eq(x_16, x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_18 = lean_box(0);
lean_ctor_set(x_9, 0, x_18);
x_19 = lean_apply_2(x_3, lean_box(0), x_9);
x_20 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_19, x_5, x_10, x_11, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_9);
lean_dec(x_5);
x_21 = l_Lean_Name_toString(x_16, x_17, x_6);
x_22 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_apply_2(x_7, lean_box(0), x_23);
x_25 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__5), 6, 2);
lean_closure_set(x_25, 0, x_14);
lean_closure_set(x_25, 1, x_3);
lean_inc(x_4);
x_26 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_24, x_25);
x_27 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_26, x_8, x_10, x_11, x_12);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_name_eq(x_29, x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_apply_2(x_3, lean_box(0), x_32);
x_34 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_33, x_5, x_10, x_11, x_12);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
x_35 = l_Lean_Name_toString(x_29, x_30, x_6);
x_36 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_apply_2(x_7, lean_box(0), x_37);
x_39 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__5), 6, 2);
lean_closure_set(x_39, 0, x_28);
lean_closure_set(x_39, 1, x_3);
lean_inc(x_4);
x_40 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_38, x_39);
x_41 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_40, x_8, x_10, x_11, x_12);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_15, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__4___boxed), 12, 8);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_16);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_7);
lean_closure_set(x_19, 7, x_8);
x_20 = lean_box(0);
lean_ctor_set(x_9, 0, x_20);
x_21 = lean_apply_2(x_18, lean_box(0), x_9);
x_22 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_21, x_19, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_box(0);
lean_ctor_set(x_9, 0, x_24);
x_25 = lean_apply_5(x_23, lean_box(0), x_9, x_10, x_11, x_12);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_ctor_get(x_26, 4);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_28, x_29);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_31);
x_32 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__4___boxed), 12, 8);
lean_closure_set(x_32, 0, x_3);
lean_closure_set(x_32, 1, x_29);
lean_closure_set(x_32, 2, x_31);
lean_closure_set(x_32, 3, x_4);
lean_closure_set(x_32, 4, x_5);
lean_closure_set(x_32, 5, x_6);
lean_closure_set(x_32, 6, x_7);
lean_closure_set(x_32, 7, x_8);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
x_35 = lean_apply_2(x_31, lean_box(0), x_34);
x_36 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_35, x_32, x_10, x_11, x_12);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
x_40 = lean_apply_5(x_37, lean_box(0), x_39, x_10, x_11, x_12);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, lean_box(0), x_2, x_3, x_4, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_5(x_1, lean_box(0), x_10, x_3, x_4, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, lean_box(0), x_2, x_3, x_4, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_5(x_1, lean_box(0), x_10, x_3, x_4, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__7), 5, 1);
lean_closure_set(x_9, 0, x_8);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__8), 5, 1);
lean_closure_set(x_10, 0, x_8);
lean_inc(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_apply_2(x_8, lean_box(0), x_11);
lean_inc(x_3);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_10);
lean_inc(x_3);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_13, x_9);
x_15 = lean_apply_7(x_3, lean_box(0), lean_box(0), x_14, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_7, x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_box(x_15);
x_19 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = 1;
x_21 = lean_usize_sub(x_7, x_20);
x_22 = lean_box_usize(x_21);
x_23 = lean_box_usize(x_8);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__1___boxed), 13, 9);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
lean_closure_set(x_24, 6, x_22);
lean_closure_set(x_24, 7, x_23);
lean_closure_set(x_24, 8, x_10);
x_25 = lean_array_uget(x_6, x_21);
lean_dec(x_6);
lean_inc(x_17);
lean_inc(x_25);
lean_inc(x_3);
x_26 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__2___boxed), 11, 5);
lean_closure_set(x_26, 0, x_2);
lean_closure_set(x_26, 1, x_3);
lean_closure_set(x_26, 2, x_25);
lean_closure_set(x_26, 3, x_17);
lean_closure_set(x_26, 4, x_4);
x_27 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__3), 6, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_10);
lean_inc(x_27);
lean_inc(x_17);
lean_inc(x_16);
x_28 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__6), 12, 8);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_16);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_17);
lean_closure_set(x_28, 4, x_27);
lean_closure_set(x_28, 5, x_19);
lean_closure_set(x_28, 6, x_5);
lean_closure_set(x_28, 7, x_27);
lean_inc(x_17);
x_29 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__9), 7, 4);
lean_closure_set(x_29, 0, x_16);
lean_closure_set(x_29, 1, x_11);
lean_closure_set(x_29, 2, x_17);
lean_closure_set(x_29, 3, x_28);
x_30 = lean_apply_7(x_17, lean_box(0), lean_box(0), x_29, x_24, x_12, x_13, x_14);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
x_35 = lean_apply_5(x_34, lean_box(0), x_1, x_12, x_13, x_14);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_11);
x_39 = lean_apply_5(x_37, lean_box(0), x_38, x_12, x_13, x_14);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_7, x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_box(x_15);
x_19 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = 1;
x_21 = lean_usize_sub(x_7, x_20);
x_22 = lean_box_usize(x_21);
x_23 = lean_box_usize(x_8);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__1___boxed), 13, 9);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
lean_closure_set(x_24, 6, x_22);
lean_closure_set(x_24, 7, x_23);
lean_closure_set(x_24, 8, x_10);
x_25 = lean_array_uget(x_6, x_21);
lean_dec(x_6);
lean_inc(x_17);
lean_inc(x_25);
lean_inc(x_3);
x_26 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__2___boxed), 11, 5);
lean_closure_set(x_26, 0, x_2);
lean_closure_set(x_26, 1, x_3);
lean_closure_set(x_26, 2, x_25);
lean_closure_set(x_26, 3, x_17);
lean_closure_set(x_26, 4, x_4);
x_27 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__3), 6, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_10);
lean_inc(x_27);
lean_inc(x_17);
lean_inc(x_16);
x_28 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__6), 12, 8);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_16);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_17);
lean_closure_set(x_28, 4, x_27);
lean_closure_set(x_28, 5, x_19);
lean_closure_set(x_28, 6, x_5);
lean_closure_set(x_28, 7, x_27);
lean_inc(x_17);
x_29 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__9), 7, 4);
lean_closure_set(x_29, 0, x_16);
lean_closure_set(x_29, 1, x_11);
lean_closure_set(x_29, 2, x_17);
lean_closure_set(x_29, 3, x_28);
x_30 = lean_apply_7(x_17, lean_box(0), lean_box(0), x_29, x_24, x_12, x_13, x_14);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
x_35 = lean_apply_5(x_34, lean_box(0), x_1, x_12, x_13, x_14);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_11);
x_39 = lean_apply_5(x_37, lean_box(0), x_38, x_12, x_13, x_14);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_box(0);
x_10 = l_Lake_Workspace_addPackage(x_7, x_8);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_9);
x_11 = lean_apply_5(x_1, lean_box(0), x_2, x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = l_Lake_Workspace_addPackage(x_12, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_apply_5(x_1, lean_box(0), x_16, x_3, x_4, x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_13);
x_15 = lean_box(0);
x_16 = lean_nat_dec_lt(x_1, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_6, 0, x_15);
x_17 = lean_apply_5(x_2, lean_box(0), x_6, x_7, x_8, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_6, 0, x_15);
x_19 = lean_apply_5(x_2, lean_box(0), x_6, x_7, x_8, x_9);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_free_object(x_6);
lean_dec(x_2);
x_20 = lean_usize_of_nat(x_1);
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0(x_3, x_4, x_13, x_20, x_21, x_15, x_5, x_12, x_7, x_8, x_9);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_ctor_get(x_23, 3);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_get_size(x_25);
x_27 = lean_box(0);
x_28 = lean_nat_dec_lt(x_1, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_apply_5(x_2, lean_box(0), x_29, x_7, x_8, x_9);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_26, x_26);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_24);
x_33 = lean_apply_5(x_2, lean_box(0), x_32, x_7, x_8, x_9);
return x_33;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
lean_dec(x_2);
x_34 = lean_usize_of_nat(x_1);
x_35 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_36 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0(x_3, x_4, x_25, x_34, x_35, x_27, x_5, x_24, x_7, x_8, x_9);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, lean_box(0), x_2, x_3, x_4, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_5(x_1, lean_box(0), x_10, x_3, x_4, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, lean_box(0), x_2, x_3, x_4, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_5(x_1, lean_box(0), x_10, x_3, x_4, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__2), 5, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__3), 5, 1);
lean_closure_set(x_12, 0, x_1);
lean_inc(x_9);
lean_ctor_set(x_4, 0, x_9);
x_13 = lean_apply_2(x_1, lean_box(0), x_4);
lean_inc(x_2);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_13, x_12);
lean_inc(x_2);
x_15 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_14, x_11);
x_16 = lean_apply_7(x_2, lean_box(0), lean_box(0), x_15, x_3, x_5, x_6, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__2), 5, 1);
lean_closure_set(x_18, 0, x_1);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__3), 5, 1);
lean_closure_set(x_19, 0, x_1);
lean_inc(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_apply_2(x_1, lean_box(0), x_20);
lean_inc(x_2);
x_22 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_21, x_19);
lean_inc(x_2);
x_23 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_22, x_18);
x_24 = lean_apply_7(x_2, lean_box(0), lean_box(0), x_23, x_3, x_5, x_6, x_7);
return x_24;
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__5___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 9);
lean_inc(x_18);
x_19 = lean_array_get_size(x_17);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__1___boxed), 9, 5);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_inc(x_6);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__4), 7, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_20);
x_22 = lean_array_get_size(x_18);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_23, x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_10, 0, x_24);
x_26 = lean_apply_2(x_2, lean_box(0), x_10);
x_27 = lean_apply_7(x_6, lean_box(0), lean_box(0), x_26, x_21, x_11, x_12, x_13);
return x_27;
}
else
{
size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_10);
lean_dec(x_2);
x_28 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_29 = lean_box_usize(x_28);
x_30 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__5___boxed__const__1;
x_31 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1___boxed), 14, 11);
lean_closure_set(x_31, 0, x_3);
lean_closure_set(x_31, 1, x_7);
lean_closure_set(x_31, 2, x_1);
lean_closure_set(x_31, 3, x_8);
lean_closure_set(x_31, 4, x_9);
lean_closure_set(x_31, 5, x_18);
lean_closure_set(x_31, 6, x_29);
lean_closure_set(x_31, 7, x_30);
lean_closure_set(x_31, 8, x_24);
lean_closure_set(x_31, 9, x_5);
lean_closure_set(x_31, 10, x_16);
x_32 = lean_apply_7(x_6, lean_box(0), lean_box(0), x_31, x_21, x_11, x_12, x_13);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_ctor_get(x_33, 3);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_1, 9);
lean_inc(x_36);
x_37 = lean_array_get_size(x_35);
lean_dec(x_35);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_38 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__1___boxed), 9, 5);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_2);
lean_closure_set(x_38, 2, x_3);
lean_closure_set(x_38, 3, x_4);
lean_closure_set(x_38, 4, x_5);
lean_inc(x_6);
lean_inc(x_2);
x_39 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__4), 7, 3);
lean_closure_set(x_39, 0, x_2);
lean_closure_set(x_39, 1, x_6);
lean_closure_set(x_39, 2, x_38);
x_40 = lean_array_get_size(x_36);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_box(0);
x_43 = lean_nat_dec_lt(x_41, x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_34);
x_45 = lean_apply_2(x_2, lean_box(0), x_44);
x_46 = lean_apply_7(x_6, lean_box(0), lean_box(0), x_45, x_39, x_11, x_12, x_13);
return x_46;
}
else
{
size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_47 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_48 = lean_box_usize(x_47);
x_49 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__5___boxed__const__1;
x_50 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1___boxed), 14, 11);
lean_closure_set(x_50, 0, x_3);
lean_closure_set(x_50, 1, x_7);
lean_closure_set(x_50, 2, x_1);
lean_closure_set(x_50, 3, x_8);
lean_closure_set(x_50, 4, x_9);
lean_closure_set(x_50, 5, x_36);
lean_closure_set(x_50, 6, x_48);
lean_closure_set(x_50, 7, x_49);
lean_closure_set(x_50, 8, x_42);
lean_closure_set(x_50, 9, x_5);
lean_closure_set(x_50, 10, x_34);
x_51 = lean_apply_7(x_6, lean_box(0), lean_box(0), x_50, x_39, x_11, x_12, x_13);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__0), 5, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc(x_12);
lean_inc(x_1);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__5), 13, 9);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_6);
lean_closure_set(x_15, 5, x_12);
lean_closure_set(x_15, 6, x_3);
lean_closure_set(x_15, 7, x_14);
lean_closure_set(x_15, 8, x_2);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
lean_inc(x_13);
x_19 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__2), 5, 1);
lean_closure_set(x_19, 0, x_13);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__3), 5, 1);
lean_closure_set(x_20, 0, x_13);
lean_inc(x_7);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_7);
x_21 = lean_apply_2(x_13, lean_box(0), x_1);
lean_inc(x_12);
x_22 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_21, x_20);
lean_inc(x_12);
x_23 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_22, x_19);
x_24 = lean_apply_7(x_12, lean_box(0), lean_box(0), x_23, x_15, x_8, x_9, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
lean_inc(x_13);
x_25 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__2), 5, 1);
lean_closure_set(x_25, 0, x_13);
lean_inc(x_13);
x_26 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__3), 5, 1);
lean_closure_set(x_26, 0, x_13);
lean_inc(x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_apply_2(x_13, lean_box(0), x_27);
lean_inc(x_12);
x_29 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_28, x_26);
lean_inc(x_12);
x_30 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_29, x_25);
x_31 = lean_apply_7(x_12, lean_box(0), lean_box(0), x_30, x_15, x_8, x_9, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(x_1, x_2, x_3, x_5, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": updating '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' with ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
lean_inc(x_3);
x_12 = l_Lean_Name_toString(x_9, x_2, x_3);
x_13 = l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__0;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lean_Name_toString(x_10, x_2, x_3);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Lean_NameMap_toJson___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_472__spec__0(x_11);
x_20 = lean_unsigned_to_nat(80u);
x_21 = l_Lean_Json_pretty(x_19, x_20);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_25);
lean_inc(x_7);
x_26 = lean_apply_2(x_7, x_24, x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___Lake_Workspace_updateAndMaterializeCore___elam__3_spec__0(x_7, x_4, x_1, x_5, x_6, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_7);
x_13 = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___Lake_Workspace_updateAndMaterializeCore___elam__3_spec__0(x_7, x_5, x_3, x_4, x_6, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_4, 4);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
lean_inc(x_16);
x_21 = l_Lake_loadDepPackage(x_16, x_18, x_1, x_2, x_5, x_20, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_53; uint8_t x_54; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_53 = lean_array_get_size(x_25);
x_54 = lean_nat_dec_lt(x_19, x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_25);
x_26 = x_17;
x_27 = x_23;
goto block_52;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_53, x_53);
if (x_55 == 0)
{
lean_dec(x_53);
lean_dec(x_25);
x_26 = x_17;
x_27 = x_23;
goto block_52;
}
else
{
lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_box(0);
x_57 = 0;
x_58 = lean_usize_of_nat(x_53);
lean_dec(x_53);
lean_inc(x_7);
x_59 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_25, x_57, x_58, x_56, x_7, x_23);
lean_dec(x_25);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_26 = x_17;
x_27 = x_60;
goto block_52;
}
}
block_52:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_inc(x_28);
lean_inc(x_7);
x_29 = l___private_Lake_Load_Resolve_0__Lake_validateDep___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__0(x_7, x_3, x_4, x_16, x_28, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__1(x_7, x_28, x_26, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_24);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_31, 0, x_37);
return x_31;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
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
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_24);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
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
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_7);
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
return x_29;
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
return x_51;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_21);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_21, 1);
x_63 = lean_ctor_get(x_21, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
lean_dec(x_22);
x_65 = lean_array_get_size(x_64);
x_66 = lean_nat_dec_lt(x_19, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_7);
x_67 = lean_box(0);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_67);
return x_21;
}
else
{
uint8_t x_68; 
lean_free_object(x_21);
x_68 = lean_nat_dec_le(x_65, x_65);
if (x_68 == 0)
{
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_7);
x_9 = x_62;
goto block_12;
}
else
{
lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_box(0);
x_70 = 0;
x_71 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_72 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_64, x_70, x_71, x_69, x_7, x_62);
lean_dec(x_64);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_9 = x_73;
goto block_12;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_21, 1);
lean_inc(x_74);
lean_dec(x_21);
x_75 = lean_ctor_get(x_22, 1);
lean_inc(x_75);
lean_dec(x_22);
x_76 = lean_array_get_size(x_75);
x_77 = lean_nat_dec_lt(x_19, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_7);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_76, x_76);
if (x_80 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_7);
x_9 = x_74;
goto block_12;
}
else
{
lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_box(0);
x_82 = 0;
x_83 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_84 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_75, x_82, x_83, x_81, x_7, x_74);
lean_dec(x_75);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_9 = x_85;
goto block_12;
}
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_13);
if (x_86 == 0)
{
return x_13;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_13, 0);
x_88 = lean_ctor_get(x_13, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_13);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14, x_9, x_15, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_box(3);
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_6);
x_7 = lean_apply_2(x_2, x_5, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_name_eq(x_16, x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_18 = lean_box(0);
lean_ctor_set(x_9, 0, x_18);
x_19 = lean_apply_2(x_3, lean_box(0), x_9);
x_20 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_19, x_5, x_10, x_11, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_9);
lean_dec(x_5);
x_21 = l_Lean_Name_toString(x_16, x_17, x_6);
x_22 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__4), 3, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_apply_2(x_7, lean_box(0), x_24);
x_26 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__5), 6, 2);
lean_closure_set(x_26, 0, x_14);
lean_closure_set(x_26, 1, x_3);
lean_inc(x_4);
x_27 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_25, x_26);
x_28 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_27, x_8, x_10, x_11, x_12);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_dec(x_9);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_name_eq(x_30, x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = lean_apply_2(x_3, lean_box(0), x_33);
x_35 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_34, x_5, x_10, x_11, x_12);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_5);
x_36 = l_Lean_Name_toString(x_30, x_31, x_6);
x_37 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__4), 3, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_apply_2(x_7, lean_box(0), x_39);
x_41 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__5), 6, 2);
lean_closure_set(x_41, 0, x_29);
lean_closure_set(x_41, 1, x_3);
lean_inc(x_4);
x_42 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_40, x_41);
x_43 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_42, x_8, x_10, x_11, x_12);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_15, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__2___boxed), 12, 8);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_16);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_7);
lean_closure_set(x_19, 7, x_8);
x_20 = lean_box(0);
lean_ctor_set(x_9, 0, x_20);
x_21 = lean_apply_2(x_18, lean_box(0), x_9);
x_22 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_21, x_19, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_box(0);
lean_ctor_set(x_9, 0, x_24);
x_25 = lean_apply_5(x_23, lean_box(0), x_9, x_10, x_11, x_12);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_ctor_get(x_26, 4);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_28, x_29);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_31);
x_32 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__2___boxed), 12, 8);
lean_closure_set(x_32, 0, x_3);
lean_closure_set(x_32, 1, x_29);
lean_closure_set(x_32, 2, x_31);
lean_closure_set(x_32, 3, x_4);
lean_closure_set(x_32, 4, x_5);
lean_closure_set(x_32, 5, x_6);
lean_closure_set(x_32, 6, x_7);
lean_closure_set(x_32, 7, x_8);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
x_35 = lean_apply_2(x_31, lean_box(0), x_34);
x_36 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_35, x_32, x_10, x_11, x_12);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
x_40 = lean_apply_5(x_37, lean_box(0), x_39, x_10, x_11, x_12);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_7, x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_box(x_15);
x_19 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = 1;
x_21 = lean_usize_sub(x_7, x_20);
x_22 = lean_box_usize(x_21);
x_23 = lean_box_usize(x_8);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__1___boxed), 13, 9);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
lean_closure_set(x_24, 6, x_22);
lean_closure_set(x_24, 7, x_23);
lean_closure_set(x_24, 8, x_10);
x_25 = lean_array_uget(x_6, x_21);
lean_dec(x_6);
lean_inc(x_17);
lean_inc(x_25);
lean_inc(x_3);
x_26 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__2___boxed), 11, 5);
lean_closure_set(x_26, 0, x_2);
lean_closure_set(x_26, 1, x_3);
lean_closure_set(x_26, 2, x_25);
lean_closure_set(x_26, 3, x_17);
lean_closure_set(x_26, 4, x_4);
x_27 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__3), 6, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_10);
lean_inc(x_27);
lean_inc(x_17);
lean_inc(x_16);
x_28 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__0), 12, 8);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_16);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_17);
lean_closure_set(x_28, 4, x_27);
lean_closure_set(x_28, 5, x_19);
lean_closure_set(x_28, 6, x_5);
lean_closure_set(x_28, 7, x_27);
lean_inc(x_17);
x_29 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__9), 7, 4);
lean_closure_set(x_29, 0, x_16);
lean_closure_set(x_29, 1, x_11);
lean_closure_set(x_29, 2, x_17);
lean_closure_set(x_29, 3, x_28);
x_30 = lean_apply_7(x_17, lean_box(0), lean_box(0), x_29, x_24, x_12, x_13, x_14);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
x_35 = lean_apply_5(x_34, lean_box(0), x_1, x_12, x_13, x_14);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_11);
x_39 = lean_apply_5(x_37, lean_box(0), x_38, x_12, x_13, x_14);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_7, x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_box(x_15);
x_19 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = 1;
x_21 = lean_usize_sub(x_7, x_20);
x_22 = lean_box_usize(x_21);
x_23 = lean_box_usize(x_8);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__1___boxed), 13, 9);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
lean_closure_set(x_24, 6, x_22);
lean_closure_set(x_24, 7, x_23);
lean_closure_set(x_24, 8, x_10);
x_25 = lean_array_uget(x_6, x_21);
lean_dec(x_6);
lean_inc(x_17);
lean_inc(x_25);
lean_inc(x_3);
x_26 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__2___boxed), 11, 5);
lean_closure_set(x_26, 0, x_2);
lean_closure_set(x_26, 1, x_3);
lean_closure_set(x_26, 2, x_25);
lean_closure_set(x_26, 3, x_17);
lean_closure_set(x_26, 4, x_4);
x_27 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__3), 6, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_10);
lean_inc(x_27);
lean_inc(x_17);
lean_inc(x_16);
x_28 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__0), 12, 8);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_16);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_17);
lean_closure_set(x_28, 4, x_27);
lean_closure_set(x_28, 5, x_19);
lean_closure_set(x_28, 6, x_5);
lean_closure_set(x_28, 7, x_27);
lean_inc(x_17);
x_29 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__9), 7, 4);
lean_closure_set(x_29, 0, x_16);
lean_closure_set(x_29, 1, x_11);
lean_closure_set(x_29, 2, x_17);
lean_closure_set(x_29, 3, x_28);
x_30 = lean_apply_7(x_17, lean_box(0), lean_box(0), x_29, x_24, x_12, x_13, x_14);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
x_35 = lean_apply_5(x_34, lean_box(0), x_1, x_12, x_13, x_14);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_11);
x_39 = lean_apply_5(x_37, lean_box(0), x_38, x_12, x_13, x_14);
return x_39;
}
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0___lam__5___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 9);
lean_inc(x_18);
x_19 = lean_array_get_size(x_17);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__1___boxed), 9, 5);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_inc(x_6);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__4), 7, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_20);
x_22 = lean_array_get_size(x_18);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_23, x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_10, 0, x_24);
x_26 = lean_apply_2(x_2, lean_box(0), x_10);
x_27 = lean_apply_7(x_6, lean_box(0), lean_box(0), x_26, x_21, x_11, x_12, x_13);
return x_27;
}
else
{
size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_10);
lean_dec(x_2);
x_28 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_29 = lean_box_usize(x_28);
x_30 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0___lam__5___boxed__const__1;
x_31 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0___boxed), 14, 11);
lean_closure_set(x_31, 0, x_3);
lean_closure_set(x_31, 1, x_7);
lean_closure_set(x_31, 2, x_1);
lean_closure_set(x_31, 3, x_8);
lean_closure_set(x_31, 4, x_9);
lean_closure_set(x_31, 5, x_18);
lean_closure_set(x_31, 6, x_29);
lean_closure_set(x_31, 7, x_30);
lean_closure_set(x_31, 8, x_24);
lean_closure_set(x_31, 9, x_5);
lean_closure_set(x_31, 10, x_16);
x_32 = lean_apply_7(x_6, lean_box(0), lean_box(0), x_31, x_21, x_11, x_12, x_13);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_ctor_get(x_33, 3);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_1, 9);
lean_inc(x_36);
x_37 = lean_array_get_size(x_35);
lean_dec(x_35);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_38 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__1___boxed), 9, 5);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_2);
lean_closure_set(x_38, 2, x_3);
lean_closure_set(x_38, 3, x_4);
lean_closure_set(x_38, 4, x_5);
lean_inc(x_6);
lean_inc(x_2);
x_39 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__4), 7, 3);
lean_closure_set(x_39, 0, x_2);
lean_closure_set(x_39, 1, x_6);
lean_closure_set(x_39, 2, x_38);
x_40 = lean_array_get_size(x_36);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_box(0);
x_43 = lean_nat_dec_lt(x_41, x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_34);
x_45 = lean_apply_2(x_2, lean_box(0), x_44);
x_46 = lean_apply_7(x_6, lean_box(0), lean_box(0), x_45, x_39, x_11, x_12, x_13);
return x_46;
}
else
{
size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_47 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_48 = lean_box_usize(x_47);
x_49 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0___lam__5___boxed__const__1;
x_50 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0___boxed), 14, 11);
lean_closure_set(x_50, 0, x_3);
lean_closure_set(x_50, 1, x_7);
lean_closure_set(x_50, 2, x_1);
lean_closure_set(x_50, 3, x_8);
lean_closure_set(x_50, 4, x_9);
lean_closure_set(x_50, 5, x_36);
lean_closure_set(x_50, 6, x_48);
lean_closure_set(x_50, 7, x_49);
lean_closure_set(x_50, 8, x_42);
lean_closure_set(x_50, 9, x_5);
lean_closure_set(x_50, 10, x_34);
x_51 = lean_apply_7(x_6, lean_box(0), lean_box(0), x_50, x_39, x_11, x_12, x_13);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__0), 5, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc(x_12);
lean_inc(x_1);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0___lam__5), 13, 9);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_6);
lean_closure_set(x_15, 5, x_12);
lean_closure_set(x_15, 6, x_3);
lean_closure_set(x_15, 7, x_14);
lean_closure_set(x_15, 8, x_2);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
lean_inc(x_13);
x_19 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__2), 5, 1);
lean_closure_set(x_19, 0, x_13);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__3), 5, 1);
lean_closure_set(x_20, 0, x_13);
lean_inc(x_7);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_7);
x_21 = lean_apply_2(x_13, lean_box(0), x_1);
lean_inc(x_12);
x_22 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_21, x_20);
lean_inc(x_12);
x_23 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_22, x_19);
x_24 = lean_apply_7(x_12, lean_box(0), lean_box(0), x_23, x_15, x_8, x_9, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
lean_inc(x_13);
x_25 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__2), 5, 1);
lean_closure_set(x_25, 0, x_13);
lean_inc(x_13);
x_26 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__3), 5, 1);
lean_closure_set(x_26, 0, x_13);
lean_inc(x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_apply_2(x_13, lean_box(0), x_27);
lean_inc(x_12);
x_29 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_28, x_26);
lean_inc(x_12);
x_30 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_29, x_25);
x_31 = lean_apply_7(x_12, lean_box(0), lean_box(0), x_30, x_15, x_8, x_9, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0(x_1, x_2, x_3, x_5, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_List_reverse___redArg(x_6);
x_9 = l_List_reverse___redArg(x_7);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = l_List_reverse___redArg(x_10);
x_13 = l_List_reverse___redArg(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_25; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_17 = x_3;
} else {
 lean_dec_ref(x_3);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_20 = x_4;
} else {
 lean_dec_ref(x_4);
 x_20 = lean_box(0);
}
x_25 = lean_name_eq(x_15, x_1);
if (x_25 == 0)
{
if (x_2 == 0)
{
goto block_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
x_3 = x_16;
x_4 = x_27;
goto _start;
}
}
else
{
goto block_24;
}
block_24:
{
lean_object* x_21; lean_object* x_22; 
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_3 = x_16;
x_4 = x_22;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___lam__0___boxed), 1, 0);
x_8 = l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___closed__0;
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_5, x_10, x_7);
x_12 = lean_string_append(x_8, x_11);
lean_dec(x_11);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___lam__0___boxed), 1, 0);
x_17 = l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___closed__0;
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Name_toString(x_14, x_19, x_16);
x_21 = lean_string_append(x_17, x_20);
lean_dec(x_20);
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
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_stdMismatchError___closed__5;
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5(x_1, x_3);
x_5 = l_String_intercalate(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_box(3);
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_6);
x_7 = lean_apply_2(x_2, x_5, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_1);
x_8 = lean_apply_5(x_2, lean_box(0), x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lake_depCycleError___redArg___closed__0;
x_12 = l_Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg___lam__0), 3, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
x_16 = lean_alloc_closure((void*)(l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg___lam__1), 6, 2);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_10);
x_17 = lean_apply_7(x_9, lean_box(0), lean_box(0), x_15, x_16, x_5, x_6, x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg(x_1, x_2, x_3, x_4, x_6, x_5, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__0___boxed), 11, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_11);
x_14 = lean_apply_7(x_1, x_5, x_13, x_6, x_12, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
x_15 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_1, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_13);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__1), 10, 6);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_6);
lean_closure_set(x_17, 5, x_16);
lean_ctor_set(x_8, 0, x_16);
x_18 = lean_apply_2(x_7, lean_box(0), x_8);
x_19 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_18, x_17, x_9, x_10, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
x_22 = l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(x_1, x_15, x_13, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_dec(x_25);
lean_inc(x_1);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_20);
x_27 = l_List_appendTR___redArg(x_22, x_26);
x_28 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg(x_3, x_5, x_27, x_14, x_9, x_10, x_11);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
lean_inc(x_1);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_20);
x_32 = l_List_appendTR___redArg(x_30, x_31);
x_33 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg(x_3, x_5, x_32, x_14, x_9, x_10, x_11);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_1, x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_34);
lean_inc(x_37);
lean_inc(x_4);
x_38 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__1), 10, 6);
lean_closure_set(x_38, 0, x_2);
lean_closure_set(x_38, 1, x_3);
lean_closure_set(x_38, 2, x_4);
lean_closure_set(x_38, 3, x_5);
lean_closure_set(x_38, 4, x_6);
lean_closure_set(x_38, 5, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_35);
x_40 = lean_apply_2(x_7, lean_box(0), x_39);
x_41 = lean_apply_7(x_4, lean_box(0), lean_box(0), x_40, x_38, x_9, x_10, x_11);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
x_44 = l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(x_1, x_36, x_34, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_42);
x_49 = l_List_appendTR___redArg(x_47, x_48);
x_50 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___redArg(x_3, x_5, x_49, x_35, x_9, x_10, x_11);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__2), 11, 7);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_13);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
x_18 = lean_apply_2(x_13, lean_box(0), x_2);
x_19 = lean_apply_7(x_3, lean_box(0), lean_box(0), x_18, x_14, x_8, x_9, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_apply_2(x_13, lean_box(0), x_20);
x_22 = lean_apply_7(x_3, lean_box(0), lean_box(0), x_21, x_14, x_8, x_9, x_10);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__2), 11, 7);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_13);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
x_18 = lean_apply_2(x_13, lean_box(0), x_2);
x_19 = lean_apply_7(x_3, lean_box(0), lean_box(0), x_18, x_14, x_8, x_9, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_apply_2(x_13, lean_box(0), x_20);
x_22 = lean_apply_7(x_3, lean_box(0), lean_box(0), x_21, x_14, x_8, x_9, x_10);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8___redArg(x_1, x_2, x_3, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_5(x_1, lean_box(0), x_6, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadErrorLoggerIO___lam__0), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4___closed__0;
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, lean_box(0));
lean_closure_set(x_15, 2, x_1);
x_16 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4___lam__0), 5, 1);
lean_closure_set(x_17, 0, x_12);
lean_inc(x_11);
x_18 = lean_alloc_closure((void*)(l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8___boxed), 12, 9);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_16);
lean_closure_set(x_18, 4, x_2);
lean_closure_set(x_18, 5, lean_box(0));
lean_closure_set(x_18, 6, x_5);
lean_closure_set(x_18, 7, x_6);
lean_closure_set(x_18, 8, x_4);
x_19 = lean_apply_7(x_11, lean_box(0), lean_box(0), x_18, x_17, x_7, x_8, x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(x_3);
x_13 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__6___boxed), 8, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_1);
lean_inc(x_4);
x_16 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0), 10, 3);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_13);
x_17 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4(x_4, x_1, x_16, x_5, x_6, x_15, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___Lake_Workspace_updateAndMaterializeCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_197; 
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
lean_dec(x_2);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 6);
lean_inc(x_65);
lean_dec(x_61);
lean_inc(x_3);
x_120 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__2___boxed), 6, 1);
lean_closure_set(x_120, 0, x_3);
x_121 = lean_box(0);
x_122 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1;
x_123 = lean_unbox(x_121);
x_124 = l_Lean_Name_toString(x_62, x_123, x_122);
lean_inc(x_63);
x_185 = l_Lake_joinRelative(x_63, x_65);
lean_dec(x_65);
x_186 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_197 = l_Lake_Manifest_load(x_185, x_5);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_198);
x_187 = x_200;
x_188 = x_199;
goto block_196;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_197, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_203, 0, x_201);
x_187 = x_203;
x_188 = x_202;
goto block_196;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
block_33:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0;
x_18 = lean_io_error_to_string(x_16);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_box(3);
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
x_23 = lean_apply_2(x_12, x_21, x_15);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
lean_dec(x_12);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_14);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_15);
return x_32;
}
}
block_48:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_array_get_size(x_36);
x_41 = lean_nat_dec_lt(x_35, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_36);
x_12 = x_37;
x_13 = x_38;
x_14 = x_34;
x_15 = x_39;
goto block_33;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_40, x_40);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_36);
x_12 = x_37;
x_13 = x_38;
x_14 = x_34;
x_15 = x_39;
goto block_33;
}
else
{
lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_box(0);
x_44 = 0;
x_45 = lean_usize_of_nat(x_40);
lean_dec(x_40);
lean_inc(x_37);
x_46 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_36, x_44, x_45, x_43, x_37, x_39);
lean_dec(x_36);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_12 = x_37;
x_13 = x_38;
x_14 = x_34;
x_15 = x_47;
goto block_33;
}
}
}
block_60:
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
x_34 = x_49;
x_35 = x_50;
x_36 = x_51;
x_37 = x_52;
x_38 = x_56;
x_39 = x_55;
goto block_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_34 = x_49;
x_35 = x_50;
x_36 = x_51;
x_37 = x_52;
x_38 = x_59;
x_39 = x_58;
goto block_48;
}
}
block_95:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
lean_dec(x_64);
x_73 = l_System_FilePath_normalize(x_67);
x_74 = l_System_FilePath_normalize(x_72);
lean_inc(x_74);
x_75 = l_System_FilePath_normalize(x_74);
x_76 = lean_string_dec_eq(x_73, x_75);
lean_dec(x_75);
lean_dec(x_73);
if (x_76 == 0)
{
if (x_69 == 0)
{
lean_dec(x_74);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_63);
x_6 = x_70;
x_7 = x_71;
goto block_11;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_77 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1;
x_78 = lean_string_append(x_77, x_66);
x_79 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2;
x_80 = lean_string_append(x_78, x_79);
x_81 = l_Lake_joinRelative(x_63, x_74);
lean_dec(x_74);
x_82 = lean_string_append(x_80, x_81);
x_83 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_box(1);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_87);
lean_inc(x_68);
x_88 = lean_apply_2(x_68, x_86, x_71);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_unsigned_to_nat(0u);
x_91 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_92 = l_Lake_createParentDirs(x_81, x_89);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_io_rename(x_66, x_81, x_93);
lean_dec(x_81);
lean_dec(x_66);
x_49 = x_70;
x_50 = x_90;
x_51 = x_91;
x_52 = x_68;
x_53 = x_94;
goto block_60;
}
else
{
lean_dec(x_81);
lean_dec(x_66);
x_49 = x_70;
x_50 = x_90;
x_51 = x_91;
x_52 = x_68;
x_53 = x_92;
goto block_60;
}
}
}
else
{
lean_dec(x_74);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_63);
x_6 = x_70;
x_7 = x_71;
goto block_11;
}
}
block_119:
{
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
lean_dec(x_64);
lean_dec(x_63);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_103 = lean_ctor_get(x_96, 0);
lean_inc(x_103);
lean_dec(x_96);
lean_inc(x_63);
x_104 = l_Lake_joinRelative(x_63, x_103);
x_105 = l_System_FilePath_pathExists(x_104, x_99);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_109 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6;
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = lean_unbox(x_106);
lean_dec(x_106);
x_66 = x_104;
x_67 = x_103;
x_68 = x_98;
x_69 = x_110;
x_70 = x_97;
x_71 = x_107;
goto block_95;
}
else
{
uint8_t x_111; 
x_111 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7;
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = lean_unbox(x_106);
lean_dec(x_106);
x_66 = x_104;
x_67 = x_103;
x_68 = x_98;
x_69 = x_112;
x_70 = x_97;
x_71 = x_107;
goto block_95;
}
else
{
lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_113 = lean_box(0);
x_114 = 0;
x_115 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8;
lean_inc(x_98);
x_116 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_108, x_114, x_115, x_113, x_98, x_107);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_unbox(x_106);
lean_dec(x_106);
x_66 = x_104;
x_67 = x_103;
x_68 = x_98;
x_69 = x_118;
x_70 = x_97;
x_71 = x_117;
goto block_95;
}
}
}
}
block_184:
{
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_128; 
lean_dec(x_120);
lean_dec(x_64);
lean_dec(x_63);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
lean_dec(x_125);
if (lean_obj_tag(x_128) == 11)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_128);
lean_dec(x_3);
x_129 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9;
x_130 = lean_string_append(x_124, x_129);
x_131 = lean_box(1);
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
x_133 = lean_unbox(x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_133);
x_134 = lean_apply_2(x_1, x_132, x_127);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_126);
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
lean_ctor_set(x_140, 1, x_126);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; uint8_t x_150; 
x_142 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10;
x_143 = lean_string_append(x_124, x_142);
x_144 = lean_io_error_to_string(x_128);
x_145 = lean_string_append(x_143, x_144);
lean_dec(x_144);
x_146 = lean_box(2);
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_145);
x_148 = lean_unbox(x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_148);
x_149 = lean_apply_2(x_1, x_147, x_127);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_126);
lean_ctor_set(x_149, 0, x_152);
return x_149;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_149, 0);
x_154 = lean_ctor_get(x_149, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_149);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_126);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_3);
x_157 = lean_io_error_to_string(x_128);
x_158 = lean_box(3);
x_159 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_159, 0, x_157);
x_160 = lean_unbox(x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_160);
x_161 = lean_apply_2(x_1, x_159, x_127);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_161, 0);
lean_dec(x_163);
x_164 = lean_box(0);
lean_ctor_set_tag(x_161, 1);
lean_ctor_set(x_161, 0, x_164);
return x_161;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
lean_dec(x_161);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
}
else
{
lean_dec(x_124);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_120);
x_168 = lean_ctor_get(x_125, 0);
lean_inc(x_168);
lean_dec(x_125);
x_169 = lean_ctor_get(x_168, 2);
lean_inc(x_169);
lean_dec(x_168);
x_96 = x_169;
x_97 = x_126;
x_98 = x_1;
x_99 = x_127;
goto block_119;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_3);
x_170 = lean_ctor_get(x_125, 0);
lean_inc(x_170);
lean_dec(x_125);
x_171 = lean_ctor_get(x_170, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 3);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_array_get_size(x_172);
x_175 = lean_nat_dec_lt(x_173, x_174);
if (x_175 == 0)
{
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_120);
x_96 = x_171;
x_97 = x_126;
x_98 = x_1;
x_99 = x_127;
goto block_119;
}
else
{
uint8_t x_176; 
x_176 = lean_nat_dec_le(x_174, x_174);
if (x_176 == 0)
{
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_120);
x_96 = x_171;
x_97 = x_126;
x_98 = x_1;
x_99 = x_127;
goto block_119;
}
else
{
lean_object* x_177; size_t x_178; size_t x_179; lean_object* x_180; 
x_177 = lean_box(0);
x_178 = 0;
x_179 = lean_usize_of_nat(x_174);
lean_dec(x_174);
lean_inc(x_1);
x_180 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(x_120, x_172, x_178, x_179, x_177, x_126, x_1, x_127);
lean_dec(x_172);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_96 = x_171;
x_97 = x_183;
x_98 = x_1;
x_99 = x_182;
goto block_119;
}
else
{
lean_dec(x_171);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_1);
return x_180;
}
}
}
}
}
}
block_196:
{
uint8_t x_189; 
x_189 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6;
if (x_189 == 0)
{
x_125 = x_187;
x_126 = x_4;
x_127 = x_188;
goto block_184;
}
else
{
uint8_t x_190; 
x_190 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7;
if (x_190 == 0)
{
x_125 = x_187;
x_126 = x_4;
x_127 = x_188;
goto block_184;
}
else
{
lean_object* x_191; size_t x_192; size_t x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_box(0);
x_192 = 0;
x_193 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8;
lean_inc(x_1);
x_194 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(x_186, x_192, x_193, x_191, x_1, x_188);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_125 = x_187;
x_126 = x_4;
x_127 = x_195;
goto block_184;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_4, x_5);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_7, 4);
lean_inc(x_12);
x_13 = 1;
x_14 = lean_usize_sub(x_4, x_13);
x_15 = lean_array_uget(x_3, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_12, x_16);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_name_eq(x_18, x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_inc(x_2);
lean_inc(x_9);
lean_inc(x_1);
x_20 = lean_apply_6(x_2, x_1, x_15, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_27 = lean_box(0);
x_28 = l_Lake_Workspace_addPackage(x_25, x_26);
x_4 = x_14;
x_6 = x_27;
x_7 = x_28;
x_8 = x_24;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(x_11);
x_35 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = l_Lean_Name_toString(x_18, x_19, x_35);
x_37 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_box(3);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_unbox(x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_41);
x_42 = lean_apply_2(x_9, x_40, x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_49 = lean_box(0);
x_4 = x_14;
x_6 = x_49;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_6);
lean_ctor_set(x_51, 1, x_7);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_8);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_10);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_8, 4);
lean_inc(x_13);
x_14 = 1;
x_15 = lean_usize_sub(x_4, x_14);
x_16 = lean_array_uget(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_13, x_17);
lean_dec(x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_name_eq(x_19, x_17);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_1);
x_21 = lean_apply_6(x_2, x_1, x_16, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
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
x_28 = lean_box(0);
x_29 = l_Lake_Workspace_addPackage(x_26, x_27);
x_30 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2___redArg(x_1, x_2, x_3, x_15, x_5, x_28, x_29, x_25, x_10, x_24);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
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
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(x_12);
x_36 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = l_Lean_Name_toString(x_19, x_20, x_36);
x_38 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_box(3);
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_unbox(x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_42);
x_43 = lean_apply_2(x_10, x_41, x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_50 = lean_box(0);
x_51 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2___redArg(x_1, x_2, x_3, x_15, x_5, x_50, x_8, x_9, x_10, x_11);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_6);
lean_ctor_set(x_52, 1, x_8);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_9);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_11);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_box(0);
x_14 = lean_nat_dec_lt(x_1, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_free_object(x_4);
x_20 = lean_usize_of_nat(x_1);
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__1(x_2, x_11, x_20, x_21, x_13, x_3, x_9, x_5, x_6, x_7);
lean_dec(x_11);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
x_25 = lean_array_get_size(x_24);
x_26 = lean_box(0);
x_27 = lean_nat_dec_lt(x_1, x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_25, x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = lean_usize_of_nat(x_1);
x_36 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_37 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__1(x_2, x_24, x_35, x_36, x_26, x_3, x_23, x_5, x_6, x_7);
lean_dec(x_24);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 9);
lean_inc(x_10);
x_11 = lean_array_get_size(x_9);
x_12 = lean_array_get_size(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_box(0);
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_13, x_12);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_nat_dec_lt(x_11, x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
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
x_21 = lean_nat_dec_le(x_11, x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
else
{
size_t x_25; lean_object* x_26; 
x_25 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_26 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__1(x_2, x_9, x_25, x_25, x_14, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_26;
}
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
lean_dec(x_9);
x_27 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_28 = 0;
lean_inc(x_7);
x_29 = l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2(x_3, x_1, x_10, x_27, x_28, x_14, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1___lam__0(x_11, x_2, x_4, x_32, x_33, x_7, x_31);
lean_dec(x_11);
return x_34;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_29;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
x_35 = lean_nat_dec_lt(x_13, x_12);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_5);
x_37 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1___lam__0(x_11, x_2, x_4, x_36, x_6, x_7, x_8);
lean_dec(x_11);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_39 = 0;
lean_inc(x_7);
x_40 = l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2(x_3, x_1, x_10, x_38, x_39, x_14, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1___lam__0(x_11, x_2, x_4, x_43, x_44, x_7, x_42);
lean_dec(x_11);
return x_45;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lake_depCycleError___redArg___closed__0;
x_5 = l_Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5(x_1);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = lean_box(3);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_apply_2(x_2, x_8, x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(x_2, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg(x_1, x_3, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_8, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_3);
lean_inc(x_10);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_apply_7(x_1, x_2, x_11, x_10, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
x_15 = l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(x_8, x_9, x_3, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
lean_inc(x_8);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_17);
lean_ctor_set(x_15, 0, x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_13);
x_20 = l_List_appendTR___redArg(x_15, x_19);
x_21 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(x_20, x_6, x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_inc(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_13);
x_25 = l_List_appendTR___redArg(x_23, x_24);
x_26 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(x_25, x_6, x_7);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_8, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_3);
lean_inc(x_10);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_apply_7(x_1, x_2, x_11, x_10, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
x_15 = l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(x_8, x_9, x_3, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
lean_inc(x_8);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_17);
lean_ctor_set(x_15, 0, x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_13);
x_20 = l_List_appendTR___redArg(x_15, x_19);
x_21 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(x_20, x_6, x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_inc(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_13);
x_25 = l_List_appendTR___redArg(x_23, x_24);
x_26 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(x_25, x_6, x_7);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7___redArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7___redArg(x_1, x_3, x_4, x_2, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Workspace_updateAndMaterializeCore_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_4, x_3);
lean_inc(x_1);
lean_inc(x_6);
x_12 = lean_apply_4(x_1, x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
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
x_17 = lean_box(0);
x_18 = lean_array_uset(x_4, x_3, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_18, x_3, x_15);
x_3 = x_20;
x_4 = x_21;
x_5 = x_16;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg(x_1, x_3, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_8, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_3);
lean_inc(x_10);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1(x_1, x_11, x_2, x_10, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
x_15 = l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(x_8, x_9, x_3, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
lean_inc(x_8);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_17);
lean_ctor_set(x_15, 0, x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_13);
x_20 = l_List_appendTR___redArg(x_15, x_19);
x_21 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(x_20, x_6, x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_inc(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_13);
x_25 = l_List_appendTR___redArg(x_23, x_24);
x_26 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(x_25, x_6, x_7);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_8, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_3);
lean_inc(x_10);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1(x_1, x_11, x_2, x_10, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
x_15 = l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(x_8, x_9, x_3, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
lean_inc(x_8);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_17);
lean_ctor_set(x_15, 0, x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_13);
x_20 = l_List_appendTR___redArg(x_15, x_19);
x_21 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(x_20, x_6, x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_inc(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_13);
x_25 = l_List_appendTR___redArg(x_23, x_24);
x_26 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___redArg(x_25, x_6, x_7);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11___redArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11___redArg(x_1, x_3, x_4, x_2, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(x_2);
x_11 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__6___boxed), 8, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11(x_11, x_3, x_4, x_13, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___at___Lake_Workspace_updateAndMaterializeCore_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
lean_dec(x_2);
x_165 = lean_ctor_get(x_16, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_16, 1);
lean_inc(x_166);
lean_dec(x_16);
x_167 = l_Lake_Workspace_updateToolchain___elam__0___closed__0;
lean_inc(x_166);
x_168 = l_System_FilePath_join(x_166, x_167);
x_169 = l_Lake_ToolchainVer_ofFile_x3f(x_168, x_4);
lean_dec(x_168);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = lean_ctor_get(x_169, 1);
x_173 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
x_174 = lean_unsigned_to_nat(0u);
x_219 = l_Lake_Workspace_updateToolchain___closed__21;
x_220 = lean_array_get_size(x_3);
x_221 = lean_nat_dec_lt(x_174, x_220);
if (x_221 == 0)
{
lean_dec(x_220);
lean_free_object(x_169);
lean_inc(x_171);
x_185 = x_165;
x_186 = x_171;
x_187 = x_219;
x_188 = x_172;
goto block_218;
}
else
{
uint8_t x_222; 
x_222 = lean_nat_dec_le(x_220, x_220);
if (x_222 == 0)
{
lean_dec(x_220);
lean_free_object(x_169);
lean_inc(x_171);
x_185 = x_165;
x_186 = x_171;
x_187 = x_219;
x_188 = x_172;
goto block_218;
}
else
{
lean_object* x_223; lean_object* x_224; size_t x_225; size_t x_226; lean_object* x_227; 
lean_inc(x_171);
lean_ctor_set(x_169, 1, x_219);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_165);
lean_ctor_set(x_223, 1, x_169);
lean_inc(x_166);
x_224 = lean_alloc_closure((void*)(l_Lake_Workspace_updateToolchain___elam__0___boxed), 5, 1);
lean_closure_set(x_224, 0, x_166);
x_225 = 0;
x_226 = lean_usize_of_nat(x_220);
lean_dec(x_220);
lean_inc(x_1);
x_227 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__1(x_224, x_3, x_225, x_226, x_223, x_1, x_172);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_ctor_get(x_229, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_229, 1);
lean_inc(x_233);
lean_dec(x_229);
x_185 = x_231;
x_186 = x_232;
x_187 = x_233;
x_188 = x_230;
goto block_218;
}
else
{
uint8_t x_234; 
lean_dec(x_171);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_227);
if (x_234 == 0)
{
return x_227;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_227, 0);
x_236 = lean_ctor_get(x_227, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_227);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
block_184:
{
uint8_t x_179; 
x_179 = lean_nat_dec_lt(x_174, x_176);
if (x_179 == 0)
{
lean_dec(x_177);
lean_dec(x_176);
x_5 = x_175;
x_6 = x_178;
goto block_15;
}
else
{
uint8_t x_180; 
x_180 = lean_nat_dec_le(x_176, x_176);
if (x_180 == 0)
{
lean_dec(x_177);
lean_dec(x_176);
x_5 = x_175;
x_6 = x_178;
goto block_15;
}
else
{
size_t x_181; size_t x_182; lean_object* x_183; 
x_181 = 0;
x_182 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_183 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0(x_173, x_177, x_181, x_182, x_178);
lean_dec(x_177);
x_5 = x_175;
x_6 = x_183;
goto block_15;
}
}
}
block_218:
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_array_get_size(x_187);
x_190 = lean_nat_dec_lt(x_174, x_189);
if (x_190 == 0)
{
lean_dec(x_189);
lean_dec(x_187);
lean_dec(x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_dec(x_171);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
x_191 = l_Lake_Workspace_updateToolchain___closed__16;
x_192 = lean_apply_2(x_1, x_191, x_188);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
return x_192;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_192);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_186, 0);
lean_inc(x_197);
lean_dec(x_186);
x_198 = l_Lake_joinRelative(x_166, x_167);
if (lean_obj_tag(x_171) == 0)
{
x_19 = x_198;
x_20 = x_188;
x_21 = x_197;
x_22 = x_190;
goto block_164;
}
else
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_171, 0);
lean_inc(x_199);
lean_dec(x_171);
x_200 = l_Lake_decEqToolchainVer____x40_Lake_Util_Version___hyg_1773_(x_199, x_197);
lean_dec(x_199);
if (x_200 == 0)
{
x_19 = x_198;
x_20 = x_188;
x_21 = x_197;
x_22 = x_200;
goto block_164;
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_18);
lean_dec(x_17);
x_201 = l_Lake_Workspace_updateToolchain___closed__18;
x_202 = lean_apply_2(x_1, x_201, x_188);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_202, 0);
lean_dec(x_204);
x_205 = lean_box(0);
lean_ctor_set(x_202, 0, x_205);
return x_202;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
lean_dec(x_202);
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
}
}
else
{
lean_dec(x_171);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_209; 
lean_dec(x_185);
x_209 = l_Lake_Workspace_updateToolchain___closed__19;
x_175 = x_188;
x_176 = x_189;
x_177 = x_187;
x_178 = x_209;
goto block_184;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_186, 0);
lean_inc(x_210);
lean_dec(x_186);
x_211 = l_Lake_Workspace_updateToolchain___closed__20;
x_212 = l_Lake_ToolchainVer_toString(x_210);
x_213 = lean_string_append(x_211, x_212);
lean_dec(x_212);
x_214 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__1;
x_215 = lean_string_append(x_213, x_214);
x_216 = l_Lean_Name_toString(x_185, x_190, x_173);
x_217 = lean_string_append(x_215, x_216);
lean_dec(x_216);
x_175 = x_188;
x_176 = x_189;
x_177 = x_187;
x_178 = x_217;
goto block_184;
}
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_238 = lean_ctor_get(x_169, 0);
x_239 = lean_ctor_get(x_169, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_169);
x_240 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
x_241 = lean_unsigned_to_nat(0u);
x_284 = l_Lake_Workspace_updateToolchain___closed__21;
x_285 = lean_array_get_size(x_3);
x_286 = lean_nat_dec_lt(x_241, x_285);
if (x_286 == 0)
{
lean_dec(x_285);
lean_inc(x_238);
x_252 = x_165;
x_253 = x_238;
x_254 = x_284;
x_255 = x_239;
goto block_283;
}
else
{
uint8_t x_287; 
x_287 = lean_nat_dec_le(x_285, x_285);
if (x_287 == 0)
{
lean_dec(x_285);
lean_inc(x_238);
x_252 = x_165;
x_253 = x_238;
x_254 = x_284;
x_255 = x_239;
goto block_283;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; size_t x_291; size_t x_292; lean_object* x_293; 
lean_inc(x_238);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_238);
lean_ctor_set(x_288, 1, x_284);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_165);
lean_ctor_set(x_289, 1, x_288);
lean_inc(x_166);
x_290 = lean_alloc_closure((void*)(l_Lake_Workspace_updateToolchain___elam__0___boxed), 5, 1);
lean_closure_set(x_290, 0, x_166);
x_291 = 0;
x_292 = lean_usize_of_nat(x_285);
lean_dec(x_285);
lean_inc(x_1);
x_293 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__1(x_290, x_3, x_291, x_292, x_289, x_1, x_239);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_293, 1);
lean_inc(x_296);
lean_dec(x_293);
x_297 = lean_ctor_get(x_294, 0);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_ctor_get(x_295, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_295, 1);
lean_inc(x_299);
lean_dec(x_295);
x_252 = x_297;
x_253 = x_298;
x_254 = x_299;
x_255 = x_296;
goto block_283;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_238);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_300 = lean_ctor_get(x_293, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_293, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_302 = x_293;
} else {
 lean_dec_ref(x_293);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
}
block_251:
{
uint8_t x_246; 
x_246 = lean_nat_dec_lt(x_241, x_243);
if (x_246 == 0)
{
lean_dec(x_244);
lean_dec(x_243);
x_5 = x_242;
x_6 = x_245;
goto block_15;
}
else
{
uint8_t x_247; 
x_247 = lean_nat_dec_le(x_243, x_243);
if (x_247 == 0)
{
lean_dec(x_244);
lean_dec(x_243);
x_5 = x_242;
x_6 = x_245;
goto block_15;
}
else
{
size_t x_248; size_t x_249; lean_object* x_250; 
x_248 = 0;
x_249 = lean_usize_of_nat(x_243);
lean_dec(x_243);
x_250 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0(x_240, x_244, x_248, x_249, x_245);
lean_dec(x_244);
x_5 = x_242;
x_6 = x_250;
goto block_15;
}
}
}
block_283:
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_array_get_size(x_254);
x_257 = lean_nat_dec_lt(x_241, x_256);
if (x_257 == 0)
{
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_238);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
x_258 = l_Lake_Workspace_updateToolchain___closed__16;
x_259 = lean_apply_2(x_1, x_258, x_255);
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
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_253, 0);
lean_inc(x_264);
lean_dec(x_253);
x_265 = l_Lake_joinRelative(x_166, x_167);
if (lean_obj_tag(x_238) == 0)
{
x_19 = x_265;
x_20 = x_255;
x_21 = x_264;
x_22 = x_257;
goto block_164;
}
else
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_238, 0);
lean_inc(x_266);
lean_dec(x_238);
x_267 = l_Lake_decEqToolchainVer____x40_Lake_Util_Version___hyg_1773_(x_266, x_264);
lean_dec(x_266);
if (x_267 == 0)
{
x_19 = x_265;
x_20 = x_255;
x_21 = x_264;
x_22 = x_267;
goto block_164;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_18);
lean_dec(x_17);
x_268 = l_Lake_Workspace_updateToolchain___closed__18;
x_269 = lean_apply_2(x_1, x_268, x_255);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
x_272 = lean_box(0);
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_271;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_270);
return x_273;
}
}
}
}
else
{
lean_dec(x_238);
lean_dec(x_166);
lean_dec(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_274; 
lean_dec(x_252);
x_274 = l_Lake_Workspace_updateToolchain___closed__19;
x_242 = x_255;
x_243 = x_256;
x_244 = x_254;
x_245 = x_274;
goto block_251;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_275 = lean_ctor_get(x_253, 0);
lean_inc(x_275);
lean_dec(x_253);
x_276 = l_Lake_Workspace_updateToolchain___closed__20;
x_277 = l_Lake_ToolchainVer_toString(x_275);
x_278 = lean_string_append(x_276, x_277);
lean_dec(x_277);
x_279 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__1;
x_280 = lean_string_append(x_278, x_279);
x_281 = l_Lean_Name_toString(x_252, x_257, x_240);
x_282 = lean_string_append(x_280, x_281);
lean_dec(x_281);
x_242 = x_255;
x_243 = x_256;
x_244 = x_254;
x_245 = x_282;
goto block_251;
}
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; uint8_t x_311; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_18);
lean_dec(x_17);
x_304 = lean_ctor_get(x_169, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_169, 1);
lean_inc(x_305);
lean_dec(x_169);
x_306 = lean_io_error_to_string(x_304);
x_307 = lean_box(3);
x_308 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_308, 0, x_306);
x_309 = lean_unbox(x_307);
lean_ctor_set_uint8(x_308, sizeof(void*)*1, x_309);
x_310 = lean_apply_2(x_1, x_308, x_305);
x_311 = !lean_is_exclusive(x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_310, 0);
lean_dec(x_312);
x_313 = lean_box(0);
lean_ctor_set_tag(x_310, 1);
lean_ctor_set(x_310, 0, x_313);
return x_310;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_310, 1);
lean_inc(x_314);
lean_dec(x_310);
x_315 = lean_box(0);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
block_15:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_box(2);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_apply_2(x_1, x_8, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
block_164:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = l_Lake_Workspace_updateToolchain___closed__0;
x_24 = l_Lake_ToolchainVer_toString(x_21);
x_25 = lean_string_append(x_23, x_24);
x_26 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
lean_inc(x_1);
x_31 = lean_apply_2(x_1, x_29, x_20);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_IO_FS_writeFile(x_19, x_24, x_32);
lean_dec(x_19);
if (lean_obj_tag(x_33) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_dec(x_24);
lean_dec(x_17);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lake_Workspace_updateToolchain___closed__2;
lean_inc(x_1);
x_36 = lean_apply_2(x_1, x_35, x_34);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lake_Workspace_updateToolchain___closed__3;
x_39 = lean_io_exit(x_38, x_37);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_io_error_to_string(x_44);
x_47 = lean_box(3);
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_apply_2(x_1, x_48, x_45);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_17, 2);
lean_inc(x_57);
lean_dec(x_17);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
lean_dec(x_24);
lean_dec(x_18);
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
lean_dec(x_33);
x_59 = l_Lake_Workspace_updateToolchain___closed__5;
lean_inc(x_1);
x_60 = lean_apply_2(x_1, x_59, x_58);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lake_Workspace_updateToolchain___closed__3;
x_63 = lean_io_exit(x_62, x_61);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; 
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_io_error_to_string(x_68);
x_71 = lean_box(3);
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
x_73 = lean_unbox(x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_73);
x_74 = lean_apply_2(x_1, x_72, x_69);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_81 = lean_ctor_get(x_33, 1);
lean_inc(x_81);
lean_dec(x_33);
x_82 = lean_ctor_get(x_18, 0);
lean_inc(x_82);
lean_dec(x_18);
x_83 = lean_ctor_get(x_57, 0);
lean_inc(x_83);
lean_dec(x_57);
x_84 = l_Lake_Workspace_updateToolchain___closed__7;
lean_inc(x_1);
x_85 = lean_apply_2(x_1, x_84, x_81);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = l_Lake_Workspace_updateToolchain___closed__8;
x_89 = l_Lake_Workspace_updateToolchain___closed__11;
x_90 = l_Lake_Workspace_updateToolchain___closed__14;
x_91 = lean_array_push(x_90, x_24);
x_92 = lean_array_push(x_91, x_89);
x_93 = l_Array_append___redArg(x_92, x_82);
lean_dec(x_82);
x_94 = lean_box(0);
x_95 = l_Lake_Env_noToolchainVars;
x_96 = lean_box(1);
x_97 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_87);
lean_ctor_set(x_97, 2, x_93);
lean_ctor_set(x_97, 3, x_94);
lean_ctor_set(x_97, 4, x_95);
x_98 = lean_unbox(x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*5, x_98);
lean_ctor_set_uint8(x_97, sizeof(void*)*5 + 1, x_22);
x_99 = lean_io_process_spawn(x_97, x_86);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_io_process_child_wait(x_88, x_100, x_101);
lean_dec(x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint32_t x_105; uint8_t x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_unbox_uint32(x_103);
lean_dec(x_103);
x_106 = lean_uint32_to_uint8(x_105);
x_107 = lean_io_exit(x_106, x_104);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
return x_107;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_107);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
x_114 = lean_io_error_to_string(x_112);
x_115 = lean_box(3);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
x_117 = lean_unbox(x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_117);
x_118 = lean_apply_2(x_1, x_116, x_113);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_118, 0);
lean_dec(x_120);
x_121 = lean_box(0);
lean_ctor_set_tag(x_118, 1);
lean_ctor_set(x_118, 0, x_121);
return x_118;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; uint8_t x_132; 
x_125 = lean_ctor_get(x_102, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_102, 1);
lean_inc(x_126);
lean_dec(x_102);
x_127 = lean_io_error_to_string(x_125);
x_128 = lean_box(3);
x_129 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_129, 0, x_127);
x_130 = lean_unbox(x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_130);
x_131 = lean_apply_2(x_1, x_129, x_126);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 0);
lean_dec(x_133);
x_134 = lean_box(0);
lean_ctor_set_tag(x_131, 1);
lean_ctor_set(x_131, 0, x_134);
return x_131;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; 
x_138 = lean_ctor_get(x_99, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_99, 1);
lean_inc(x_139);
lean_dec(x_99);
x_140 = lean_io_error_to_string(x_138);
x_141 = lean_box(3);
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_140);
x_143 = lean_unbox(x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_143);
x_144 = lean_apply_2(x_1, x_142, x_139);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 0);
lean_dec(x_146);
x_147 = lean_box(0);
lean_ctor_set_tag(x_144, 1);
lean_ctor_set(x_144, 0, x_147);
return x_144;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; uint8_t x_158; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
x_151 = lean_ctor_get(x_33, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_33, 1);
lean_inc(x_152);
lean_dec(x_33);
x_153 = lean_io_error_to_string(x_151);
x_154 = lean_box(3);
x_155 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_155, 0, x_153);
x_156 = lean_unbox(x_154);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_156);
x_157 = lean_apply_2(x_1, x_155, x_152);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
lean_dec(x_159);
x_160 = lean_box(0);
lean_ctor_set_tag(x_157, 1);
lean_ctor_set(x_157, 0, x_160);
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_7);
x_11 = lean_apply_5(x_1, x_5, x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_6 = x_15;
x_8 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_7);
x_11 = lean_apply_5(x_1, x_5, x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_6 = x_15;
x_8 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
}
static lean_object* _init_l_Lake_Workspace_updateAndMaterializeCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
lean_inc(x_1);
lean_inc(x_5);
x_8 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___Lake_Workspace_updateAndMaterializeCore_spec__0(x_5, x_1, x_2, x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Lake_Workspace_addPackage(x_12, x_1);
if (x_4 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__3), 7, 1);
lean_closure_set(x_15, 0, x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1), 8, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6(x_17, x_13, x_14, x_16, x_11, x_5, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 9);
lean_inc(x_21);
x_22 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
x_23 = lean_box(x_4);
lean_inc(x_13);
x_24 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__1___boxed), 8, 4);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_13);
x_25 = l_Array_reverse___redArg(x_21);
x_26 = lean_array_size(x_25);
x_27 = 0;
lean_inc(x_5);
lean_inc(x_25);
x_28 = l_Array_mapMUnsafe_map___at___Lake_Workspace_updateAndMaterializeCore_spec__10(x_24, x_26, x_27, x_25, x_11, x_5, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_13);
lean_inc(x_5);
x_34 = l_Lake_Workspace_updateToolchain___at___Lake_Workspace_updateAndMaterializeCore_spec__15(x_5, x_13, x_32, x_30);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(x_4);
lean_inc(x_3);
x_39 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11___boxed), 7, 2);
lean_closure_set(x_39, 0, x_3);
lean_closure_set(x_39, 1, x_38);
x_53 = l_Array_zip___redArg(x_25, x_32);
lean_dec(x_32);
lean_dec(x_25);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_53);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_3);
lean_inc(x_33);
lean_inc(x_13);
lean_ctor_set(x_29, 0, x_13);
lean_inc(x_36);
lean_ctor_set(x_34, 0, x_29);
x_40 = x_34;
x_41 = x_13;
x_42 = x_33;
x_43 = x_36;
goto block_52;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_55, x_55);
if (x_57 == 0)
{
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_3);
lean_inc(x_33);
lean_inc(x_13);
lean_ctor_set(x_29, 0, x_13);
lean_inc(x_36);
lean_ctor_set(x_34, 0, x_29);
x_40 = x_34;
x_41 = x_13;
x_42 = x_33;
x_43 = x_36;
goto block_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; lean_object* x_62; 
lean_free_object(x_34);
lean_free_object(x_29);
x_58 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_59 = lean_box(x_4);
x_60 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__2___boxed), 9, 4);
lean_closure_set(x_60, 0, x_3);
lean_closure_set(x_60, 1, x_59);
lean_closure_set(x_60, 2, x_58);
lean_closure_set(x_60, 3, x_58);
x_61 = lean_usize_of_nat(x_55);
lean_dec(x_55);
lean_inc(x_5);
x_62 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17(x_60, x_53, x_27, x_61, x_13, x_33, x_5, x_36);
lean_dec(x_53);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_40 = x_62;
x_41 = x_65;
x_42 = x_66;
x_43 = x_64;
goto block_52;
}
else
{
lean_dec(x_39);
lean_dec(x_20);
lean_dec(x_5);
return x_62;
}
}
}
block_52:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_41, 3);
lean_inc(x_44);
x_45 = lean_array_get_size(x_20);
lean_dec(x_20);
x_46 = lean_array_get_size(x_44);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_5);
return x_40;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_5);
return x_40;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
lean_dec(x_40);
x_49 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_50 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_51 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16(x_39, x_44, x_49, x_50, x_41, x_42, x_5, x_43);
lean_dec(x_44);
return x_51;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_67 = lean_ctor_get(x_34, 1);
lean_inc(x_67);
lean_dec(x_34);
x_68 = lean_box(x_4);
lean_inc(x_3);
x_69 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11___boxed), 7, 2);
lean_closure_set(x_69, 0, x_3);
lean_closure_set(x_69, 1, x_68);
x_83 = l_Array_zip___redArg(x_25, x_32);
lean_dec(x_32);
lean_dec(x_25);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_array_get_size(x_83);
x_86 = lean_nat_dec_lt(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_3);
lean_inc(x_33);
lean_inc(x_13);
lean_ctor_set(x_29, 0, x_13);
lean_inc(x_67);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_29);
lean_ctor_set(x_87, 1, x_67);
x_70 = x_87;
x_71 = x_13;
x_72 = x_33;
x_73 = x_67;
goto block_82;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_85, x_85);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_3);
lean_inc(x_33);
lean_inc(x_13);
lean_ctor_set(x_29, 0, x_13);
lean_inc(x_67);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_29);
lean_ctor_set(x_89, 1, x_67);
x_70 = x_89;
x_71 = x_13;
x_72 = x_33;
x_73 = x_67;
goto block_82;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; size_t x_93; lean_object* x_94; 
lean_free_object(x_29);
x_90 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_91 = lean_box(x_4);
x_92 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__2___boxed), 9, 4);
lean_closure_set(x_92, 0, x_3);
lean_closure_set(x_92, 1, x_91);
lean_closure_set(x_92, 2, x_90);
lean_closure_set(x_92, 3, x_90);
x_93 = lean_usize_of_nat(x_85);
lean_dec(x_85);
lean_inc(x_5);
x_94 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17(x_92, x_83, x_27, x_93, x_13, x_33, x_5, x_67);
lean_dec(x_83);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_70 = x_94;
x_71 = x_97;
x_72 = x_98;
x_73 = x_96;
goto block_82;
}
else
{
lean_dec(x_69);
lean_dec(x_20);
lean_dec(x_5);
return x_94;
}
}
}
block_82:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_71, 3);
lean_inc(x_74);
x_75 = lean_array_get_size(x_20);
lean_dec(x_20);
x_76 = lean_array_get_size(x_74);
x_77 = lean_nat_dec_lt(x_75, x_76);
if (x_77 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_5);
return x_70;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_76, x_76);
if (x_78 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_5);
return x_70;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; 
lean_dec(x_70);
x_79 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_80 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_81 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16(x_69, x_74, x_79, x_80, x_71, x_72, x_5, x_73);
lean_dec(x_74);
return x_81;
}
}
}
}
}
else
{
uint8_t x_99; 
lean_free_object(x_29);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_99 = !lean_is_exclusive(x_34);
if (x_99 == 0)
{
return x_34;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_34, 0);
x_101 = lean_ctor_get(x_34, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_34);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_29, 0);
x_104 = lean_ctor_get(x_29, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_29);
lean_inc(x_13);
lean_inc(x_5);
x_105 = l_Lake_Workspace_updateToolchain___at___Lake_Workspace_updateAndMaterializeCore_spec__15(x_5, x_13, x_103, x_30);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
x_108 = lean_box(x_4);
lean_inc(x_3);
x_109 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11___boxed), 7, 2);
lean_closure_set(x_109, 0, x_3);
lean_closure_set(x_109, 1, x_108);
x_123 = l_Array_zip___redArg(x_25, x_103);
lean_dec(x_103);
lean_dec(x_25);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_array_get_size(x_123);
x_126 = lean_nat_dec_lt(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_3);
lean_inc(x_104);
lean_inc(x_13);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_13);
lean_ctor_set(x_127, 1, x_104);
lean_inc(x_106);
if (lean_is_scalar(x_107)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_107;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_106);
x_110 = x_128;
x_111 = x_13;
x_112 = x_104;
x_113 = x_106;
goto block_122;
}
else
{
uint8_t x_129; 
x_129 = lean_nat_dec_le(x_125, x_125);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_3);
lean_inc(x_104);
lean_inc(x_13);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_13);
lean_ctor_set(x_130, 1, x_104);
lean_inc(x_106);
if (lean_is_scalar(x_107)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_107;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_106);
x_110 = x_131;
x_111 = x_13;
x_112 = x_104;
x_113 = x_106;
goto block_122;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; size_t x_135; lean_object* x_136; 
lean_dec(x_107);
x_132 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_133 = lean_box(x_4);
x_134 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__2___boxed), 9, 4);
lean_closure_set(x_134, 0, x_3);
lean_closure_set(x_134, 1, x_133);
lean_closure_set(x_134, 2, x_132);
lean_closure_set(x_134, 3, x_132);
x_135 = lean_usize_of_nat(x_125);
lean_dec(x_125);
lean_inc(x_5);
x_136 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17(x_134, x_123, x_27, x_135, x_13, x_104, x_5, x_106);
lean_dec(x_123);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_110 = x_136;
x_111 = x_139;
x_112 = x_140;
x_113 = x_138;
goto block_122;
}
else
{
lean_dec(x_109);
lean_dec(x_20);
lean_dec(x_5);
return x_136;
}
}
}
block_122:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_111, 3);
lean_inc(x_114);
x_115 = lean_array_get_size(x_20);
lean_dec(x_20);
x_116 = lean_array_get_size(x_114);
x_117 = lean_nat_dec_lt(x_115, x_116);
if (x_117 == 0)
{
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_5);
return x_110;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_116, x_116);
if (x_118 == 0)
{
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_5);
return x_110;
}
else
{
size_t x_119; size_t x_120; lean_object* x_121; 
lean_dec(x_110);
x_119 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_120 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_121 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16(x_109, x_114, x_119, x_120, x_111, x_112, x_5, x_113);
lean_dec(x_114);
return x_121;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_141 = lean_ctor_get(x_105, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_105, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_143 = x_105;
} else {
 lean_dec_ref(x_105);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_145 = !lean_is_exclusive(x_28);
if (x_145 == 0)
{
return x_28;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_28, 0);
x_147 = lean_ctor_get(x_28, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_28);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_8);
if (x_149 == 0)
{
return x_8;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_8, 0);
x_151 = lean_ctor_get(x_8, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_8);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_Workspace_updateAndMaterializeCore___elam__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___lam__0(x_11, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_16 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_15, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Workspace_updateAndMaterializeCore___elam__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Workspace_updateAndMaterializeCore___elam__6(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_16 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_15, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8_spec__8___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_Workspace_updateAndMaterializeCore___elam__5(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2___redArg(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2_spec__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7_spec__7___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Workspace_updateAndMaterializeCore_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at___Lake_Workspace_updateAndMaterializeCore_spec__10(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11_spec__11___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11_spec__11_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateToolchain___at___Lake_Workspace_updateAndMaterializeCore_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_updateToolchain___at___Lake_Workspace_updateAndMaterializeCore_spec__15(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
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
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_writeManifest_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 6);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_1, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_15);
lean_dec(x_14);
x_6 = x_5;
goto block_10;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_dec(x_21);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 2, x_14);
x_22 = lean_array_push(x_5, x_18);
x_6 = x_22;
goto block_10;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
x_25 = lean_ctor_get_uint8(x_18, sizeof(void*)*5);
x_26 = lean_ctor_get(x_18, 4);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_15);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_14);
lean_ctor_set(x_27, 3, x_16);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_25);
x_28 = lean_array_push(x_5, x_27);
x_6 = x_28;
goto block_10;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_29, sizeof(void*)*5);
x_33 = lean_ctor_get(x_29, 4);
lean_inc(x_33);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 x_34 = x_29;
} else {
 lean_dec_ref(x_29);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_15);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 5, 1);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_14);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*5, x_32);
x_37 = lean_array_push(x_5, x_36);
x_6 = x_37;
goto block_10;
}
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lake_Workspace_writeManifest___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lake", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_writeManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lake_loadDepPackage___closed__0;
x_21 = lean_array_get_size(x_5);
x_22 = lean_nat_dec_lt(x_19, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_5);
x_6 = x_20;
goto block_18;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_5);
x_6 = x_20;
goto block_18;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_writeManifest_spec__0(x_2, x_5, x_24, x_25, x_20);
lean_dec(x_5);
x_6 = x_26;
goto block_18;
}
}
block_18:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 6);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lake_Workspace_writeManifest___closed__0;
x_13 = l_System_FilePath_normalize(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_6);
x_16 = l_Lake_joinRelative(x_9, x_10);
lean_dec(x_10);
x_17 = l_Lake_Manifest_save(x_15, x_16, x_3);
lean_dec(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_writeManifest_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_writeManifest_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_writeManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Workspace_writeManifest(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks___elam__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_14 = lean_apply_4(x_4, x_1, x_5, x_13, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_12, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_2);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_2);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
lean_free_object(x_14);
x_24 = lean_box(0);
x_25 = 0;
x_26 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_27 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_2, x_20, x_25, x_26, x_24, x_6, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_dec(x_19);
return x_27;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_ctor_get(x_15, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_array_get_size(x_34);
x_36 = lean_nat_dec_lt(x_12, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_35, x_35);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_40 = lean_box(0);
x_41 = 0;
x_42 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_43 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_2, x_34, x_41, x_42, x_40, x_6, x_32);
lean_dec(x_34);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_dec(x_33);
return x_43;
}
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_14, 1);
x_49 = lean_ctor_get(x_14, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
lean_dec(x_15);
x_51 = lean_array_get_size(x_50);
x_52 = lean_nat_dec_lt(x_12, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_6);
lean_dec(x_3);
x_53 = lean_box(0);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_53);
return x_14;
}
else
{
uint8_t x_54; 
lean_free_object(x_14);
x_54 = lean_nat_dec_le(x_51, x_51);
if (x_54 == 0)
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_6);
lean_dec(x_3);
x_8 = x_48;
goto block_11;
}
else
{
lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_55 = lean_box(0);
x_56 = 0;
x_57 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_58 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_3, x_50, x_56, x_57, x_55, x_6, x_48);
lean_dec(x_50);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_8 = x_59;
goto block_11;
}
else
{
return x_58;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_14, 1);
lean_inc(x_60);
lean_dec(x_14);
x_61 = lean_ctor_get(x_15, 1);
lean_inc(x_61);
lean_dec(x_15);
x_62 = lean_array_get_size(x_61);
x_63 = lean_nat_dec_lt(x_12, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_3);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_62, x_62);
if (x_66 == 0)
{
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_3);
x_8 = x_60;
goto block_11;
}
else
{
lean_object* x_67; size_t x_68; size_t x_69; lean_object* x_70; 
x_67 = lean_box(0);
x_68 = 0;
x_69 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_70 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_3, x_61, x_68, x_69, x_67, x_6, x_60);
lean_dec(x_61);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_8 = x_71;
goto block_11;
}
else
{
return x_70;
}
}
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks___elam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Package_runPostUpdateHooks___elam__2___redArg(x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_runPostUpdateHooks_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_apply_5(x_1, x_5, x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_5 = x_12;
x_8 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
}
static lean_object* _init_l_Lake_Package_runPostUpdateHooks___closed__0() {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 15);
lean_inc(x_6);
x_7 = l_Array_isEmpty___redArg(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_box(x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_loadDepPackage___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_5);
x_12 = l_Lean_Name_toString(x_5, x_11, x_9);
x_13 = l_Lake_Package_runPostUpdateHooks___closed__0;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
lean_inc(x_3);
x_18 = lean_apply_2(x_3, x_16, x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_6);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_22, x_23);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_23, x_23);
if (x_26 == 0)
{
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
lean_free_object(x_18);
x_27 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_28 = lean_alloc_closure((void*)(l_Lake_Package_runPostUpdateHooks___elam__2___boxed), 9, 4);
lean_closure_set(x_28, 0, x_5);
lean_closure_set(x_28, 1, x_1);
lean_closure_set(x_28, 2, x_27);
lean_closure_set(x_28, 3, x_27);
x_29 = 0;
x_30 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_31 = l_Array_foldlMUnsafe_fold___at___Lake_Package_runPostUpdateHooks_spec__0(x_28, x_6, x_29, x_30, x_24, x_2, x_3, x_20);
lean_dec(x_6);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_6);
x_35 = lean_box(0);
x_36 = lean_nat_dec_lt(x_33, x_34);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_34, x_34);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_40 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_41 = lean_alloc_closure((void*)(l_Lake_Package_runPostUpdateHooks___elam__2___boxed), 9, 4);
lean_closure_set(x_41, 0, x_5);
lean_closure_set(x_41, 1, x_1);
lean_closure_set(x_41, 2, x_40);
lean_closure_set(x_41, 3, x_40);
x_42 = 0;
x_43 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_44 = l_Array_foldlMUnsafe_fold___at___Lake_Package_runPostUpdateHooks_spec__0(x_41, x_6, x_42, x_43, x_35, x_2, x_3, x_32);
lean_dec(x_6);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks___elam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Package_runPostUpdateHooks___elam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at___Lake_Package_runPostUpdateHooks_spec__0(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_runPostUpdateHooks___at___Lake_Workspace_updateAndMaterialize___elam__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 15);
lean_inc(x_6);
x_7 = l_Array_isEmpty___redArg(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_box(x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_loadDepPackage___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_5);
x_12 = l_Lean_Name_toString(x_5, x_11, x_9);
x_13 = l_Lake_Package_runPostUpdateHooks___closed__0;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
lean_inc(x_1);
x_18 = lean_apply_2(x_1, x_16, x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_6);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_22, x_23);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_23, x_23);
if (x_26 == 0)
{
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
lean_free_object(x_18);
x_27 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_28 = lean_alloc_closure((void*)(l_Lake_Package_runPostUpdateHooks___elam__2___boxed), 9, 4);
lean_closure_set(x_28, 0, x_5);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_27);
lean_closure_set(x_28, 3, x_27);
x_29 = 0;
x_30 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_31 = l_Array_foldlMUnsafe_fold___at___Lake_Package_runPostUpdateHooks_spec__0(x_28, x_6, x_29, x_30, x_24, x_3, x_1, x_20);
lean_dec(x_6);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_6);
x_35 = lean_box(0);
x_36 = lean_nat_dec_lt(x_33, x_34);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_34, x_34);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_40 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_41 = lean_alloc_closure((void*)(l_Lake_Package_runPostUpdateHooks___elam__2___boxed), 9, 4);
lean_closure_set(x_41, 0, x_5);
lean_closure_set(x_41, 1, x_2);
lean_closure_set(x_41, 2, x_40);
lean_closure_set(x_41, 3, x_40);
x_42 = 0;
x_43 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_44 = l_Array_foldlMUnsafe_fold___at___Lake_Package_runPostUpdateHooks_spec__0(x_41, x_6, x_42, x_43, x_35, x_3, x_1, x_32);
lean_dec(x_6);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___elam__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_runPostUpdateHooks___at___Lake_Workspace_updateAndMaterialize___elam__0_spec__0(x_3, x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_runPostUpdateHooks___at___Lake_Workspace_updateAndMaterialize___elam__0_spec__0(x_4, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore_spec__1_spec__1(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___Lake_Workspace_updateAndMaterializeCore_spec__0(x_1, x_2, x_3, x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = l_Lake_Workspace_addPackage(x_12, x_2);
if (x_5 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__3), 7, 1);
lean_closure_set(x_15, 0, x_4);
x_16 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0___lam__0), 8, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore_spec__6(x_16, x_13, x_14, x_17, x_11, x_1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 9);
lean_inc(x_21);
x_22 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
x_23 = lean_box(x_5);
lean_inc(x_13);
x_24 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__1___boxed), 8, 4);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_13);
x_25 = l_Array_reverse___redArg(x_21);
x_26 = lean_array_size(x_25);
x_27 = 0;
lean_inc(x_1);
lean_inc(x_25);
x_28 = l_Array_mapMUnsafe_map___at___Lake_Workspace_updateAndMaterializeCore_spec__10(x_24, x_26, x_27, x_25, x_11, x_1, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_13);
lean_inc(x_1);
x_34 = l_Lake_Workspace_updateToolchain___at___Lake_Workspace_updateAndMaterializeCore_spec__15(x_1, x_13, x_32, x_30);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(x_5);
lean_inc(x_4);
x_39 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11___boxed), 7, 2);
lean_closure_set(x_39, 0, x_4);
lean_closure_set(x_39, 1, x_38);
x_53 = l_Array_zip___redArg(x_25, x_32);
lean_dec(x_32);
lean_dec(x_25);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_53);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_4);
lean_inc(x_33);
lean_inc(x_13);
lean_ctor_set(x_29, 0, x_13);
lean_inc(x_36);
lean_ctor_set(x_34, 0, x_29);
x_40 = x_34;
x_41 = x_13;
x_42 = x_33;
x_43 = x_36;
goto block_52;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_55, x_55);
if (x_57 == 0)
{
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_4);
lean_inc(x_33);
lean_inc(x_13);
lean_ctor_set(x_29, 0, x_13);
lean_inc(x_36);
lean_ctor_set(x_34, 0, x_29);
x_40 = x_34;
x_41 = x_13;
x_42 = x_33;
x_43 = x_36;
goto block_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; lean_object* x_62; 
lean_free_object(x_34);
lean_free_object(x_29);
x_58 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_59 = lean_box(x_5);
x_60 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__2___boxed), 9, 4);
lean_closure_set(x_60, 0, x_4);
lean_closure_set(x_60, 1, x_59);
lean_closure_set(x_60, 2, x_58);
lean_closure_set(x_60, 3, x_58);
x_61 = lean_usize_of_nat(x_55);
lean_dec(x_55);
lean_inc(x_1);
x_62 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17(x_60, x_53, x_27, x_61, x_13, x_33, x_1, x_36);
lean_dec(x_53);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_40 = x_62;
x_41 = x_65;
x_42 = x_66;
x_43 = x_64;
goto block_52;
}
else
{
lean_dec(x_39);
lean_dec(x_20);
lean_dec(x_1);
return x_62;
}
}
}
block_52:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_41, 3);
lean_inc(x_44);
x_45 = lean_array_get_size(x_20);
lean_dec(x_20);
x_46 = lean_array_get_size(x_44);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_1);
return x_40;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_1);
return x_40;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
lean_dec(x_40);
x_49 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_50 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_51 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16(x_39, x_44, x_49, x_50, x_41, x_42, x_1, x_43);
lean_dec(x_44);
return x_51;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_67 = lean_ctor_get(x_34, 1);
lean_inc(x_67);
lean_dec(x_34);
x_68 = lean_box(x_5);
lean_inc(x_4);
x_69 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11___boxed), 7, 2);
lean_closure_set(x_69, 0, x_4);
lean_closure_set(x_69, 1, x_68);
x_83 = l_Array_zip___redArg(x_25, x_32);
lean_dec(x_32);
lean_dec(x_25);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_array_get_size(x_83);
x_86 = lean_nat_dec_lt(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_4);
lean_inc(x_33);
lean_inc(x_13);
lean_ctor_set(x_29, 0, x_13);
lean_inc(x_67);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_29);
lean_ctor_set(x_87, 1, x_67);
x_70 = x_87;
x_71 = x_13;
x_72 = x_33;
x_73 = x_67;
goto block_82;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_85, x_85);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_4);
lean_inc(x_33);
lean_inc(x_13);
lean_ctor_set(x_29, 0, x_13);
lean_inc(x_67);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_29);
lean_ctor_set(x_89, 1, x_67);
x_70 = x_89;
x_71 = x_13;
x_72 = x_33;
x_73 = x_67;
goto block_82;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; size_t x_93; lean_object* x_94; 
lean_free_object(x_29);
x_90 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_91 = lean_box(x_5);
x_92 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__2___boxed), 9, 4);
lean_closure_set(x_92, 0, x_4);
lean_closure_set(x_92, 1, x_91);
lean_closure_set(x_92, 2, x_90);
lean_closure_set(x_92, 3, x_90);
x_93 = lean_usize_of_nat(x_85);
lean_dec(x_85);
lean_inc(x_1);
x_94 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17(x_92, x_83, x_27, x_93, x_13, x_33, x_1, x_67);
lean_dec(x_83);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_70 = x_94;
x_71 = x_97;
x_72 = x_98;
x_73 = x_96;
goto block_82;
}
else
{
lean_dec(x_69);
lean_dec(x_20);
lean_dec(x_1);
return x_94;
}
}
}
block_82:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_71, 3);
lean_inc(x_74);
x_75 = lean_array_get_size(x_20);
lean_dec(x_20);
x_76 = lean_array_get_size(x_74);
x_77 = lean_nat_dec_lt(x_75, x_76);
if (x_77 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_1);
return x_70;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_76, x_76);
if (x_78 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_1);
return x_70;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; 
lean_dec(x_70);
x_79 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_80 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_81 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16(x_69, x_74, x_79, x_80, x_71, x_72, x_1, x_73);
lean_dec(x_74);
return x_81;
}
}
}
}
}
else
{
uint8_t x_99; 
lean_free_object(x_29);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_34);
if (x_99 == 0)
{
return x_34;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_34, 0);
x_101 = lean_ctor_get(x_34, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_34);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_29, 0);
x_104 = lean_ctor_get(x_29, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_29);
lean_inc(x_13);
lean_inc(x_1);
x_105 = l_Lake_Workspace_updateToolchain___at___Lake_Workspace_updateAndMaterializeCore_spec__15(x_1, x_13, x_103, x_30);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
x_108 = lean_box(x_5);
lean_inc(x_4);
x_109 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__5___at___Lake_Workspace_updateAndMaterializeCore_spec__11___boxed), 7, 2);
lean_closure_set(x_109, 0, x_4);
lean_closure_set(x_109, 1, x_108);
x_123 = l_Array_zip___redArg(x_25, x_103);
lean_dec(x_103);
lean_dec(x_25);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_array_get_size(x_123);
x_126 = lean_nat_dec_lt(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_4);
lean_inc(x_104);
lean_inc(x_13);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_13);
lean_ctor_set(x_127, 1, x_104);
lean_inc(x_106);
if (lean_is_scalar(x_107)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_107;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_106);
x_110 = x_128;
x_111 = x_13;
x_112 = x_104;
x_113 = x_106;
goto block_122;
}
else
{
uint8_t x_129; 
x_129 = lean_nat_dec_le(x_125, x_125);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_4);
lean_inc(x_104);
lean_inc(x_13);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_13);
lean_ctor_set(x_130, 1, x_104);
lean_inc(x_106);
if (lean_is_scalar(x_107)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_107;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_106);
x_110 = x_131;
x_111 = x_13;
x_112 = x_104;
x_113 = x_106;
goto block_122;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; size_t x_135; lean_object* x_136; 
lean_dec(x_107);
x_132 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_133 = lean_box(x_5);
x_134 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__2___boxed), 9, 4);
lean_closure_set(x_134, 0, x_4);
lean_closure_set(x_134, 1, x_133);
lean_closure_set(x_134, 2, x_132);
lean_closure_set(x_134, 3, x_132);
x_135 = lean_usize_of_nat(x_125);
lean_dec(x_125);
lean_inc(x_1);
x_136 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__17(x_134, x_123, x_27, x_135, x_13, x_104, x_1, x_106);
lean_dec(x_123);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_110 = x_136;
x_111 = x_139;
x_112 = x_140;
x_113 = x_138;
goto block_122;
}
else
{
lean_dec(x_109);
lean_dec(x_20);
lean_dec(x_1);
return x_136;
}
}
}
block_122:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_111, 3);
lean_inc(x_114);
x_115 = lean_array_get_size(x_20);
lean_dec(x_20);
x_116 = lean_array_get_size(x_114);
x_117 = lean_nat_dec_lt(x_115, x_116);
if (x_117 == 0)
{
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_1);
return x_110;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_116, x_116);
if (x_118 == 0)
{
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_1);
return x_110;
}
else
{
size_t x_119; size_t x_120; lean_object* x_121; 
lean_dec(x_110);
x_119 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_120 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_121 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore_spec__16(x_109, x_114, x_119, x_120, x_111, x_112, x_1, x_113);
lean_dec(x_114);
return x_121;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_141 = lean_ctor_get(x_105, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_105, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_143 = x_105;
} else {
 lean_dec_ref(x_105);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_28);
if (x_145 == 0)
{
return x_28;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_28, 0);
x_147 = lean_ctor_get(x_28, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_28);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_8);
if (x_149 == 0)
{
return x_8;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_8, 0);
x_151 = lean_ctor_get(x_8, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_8);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
lean_inc(x_6);
x_10 = l_Lake_Package_runPostUpdateHooks___at___Lake_Workspace_updateAndMaterialize___elam__0_spec__0(x_6, x_9, x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_7 = x_12;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
else
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
lean_inc(x_6);
x_10 = l_Lake_Package_runPostUpdateHooks___at___Lake_Workspace_updateAndMaterialize___elam__0_spec__0(x_6, x_9, x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1_spec__1(x_1, x_14, x_3, x_11, x_5, x_6, x_12);
return x_15;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
else
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0(x_5, x_1, x_2, x_3, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_10);
x_12 = l_Lake_Workspace_writeManifest(x_10, x_11, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 3);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_5);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_5);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
lean_free_object(x_12);
x_21 = lean_box(0);
x_22 = 0;
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
lean_inc(x_10);
x_24 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1(x_16, x_22, x_23, x_21, x_10, x_5, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_10);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
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
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_ctor_get(x_10, 3);
lean_inc(x_34);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_5);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_36, x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_5);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_41 = lean_box(0);
x_42 = 0;
x_43 = lean_usize_of_nat(x_36);
lean_dec(x_36);
lean_inc(x_10);
x_44 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1(x_34, x_42, x_43, x_41, x_10, x_5, x_33);
lean_dec(x_34);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
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
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_10);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
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
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_10);
x_52 = lean_ctor_get(x_12, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_io_error_to_string(x_52);
x_55 = lean_box(3);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_unbox(x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
x_58 = lean_apply_2(x_5, x_56, x_53);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set_tag(x_58, 1);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_7);
if (x_65 == 0)
{
return x_7;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_7);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_updateAndMaterialize___elam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1_spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
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
return x_8;
}
}
static lean_object* _init_l_Lake_validateManifest___elam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("manifest out of date: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_validateManifest___elam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" of dependency '", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_validateManifest___elam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' changed; use `lake update ", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lake_validateManifest___elam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` to update it", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lake_validateManifest___elam__0___closed__0;
x_8 = lean_string_append(x_7, x_3);
x_9 = l_Lake_validateManifest___elam__0___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Name_toString(x_6, x_12, x_2);
x_14 = lean_string_append(x_10, x_13);
x_15 = l_Lake_validateManifest___elam__0___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_13);
lean_dec(x_13);
x_18 = l_Lake_validateManifest___elam__0___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_box(2);
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
x_23 = lean_apply_2(x_4, x_21, x_5);
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
}
static lean_object* _init_l_Lake_validateManifest___elam__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("source kind (git/path)", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_validateManifest___elam__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git revision", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_validateManifest___elam__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git url", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_2, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
else
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
else
{
lean_dec(x_20);
x_6 = x_4;
x_7 = x_5;
goto block_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_23, 4);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_24);
lean_dec(x_15);
x_6 = x_4;
x_7 = x_5;
goto block_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_39; uint8_t x_40; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
lean_dec(x_24);
x_39 = lean_string_dec_eq(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_40 = l_instDecidableNot___redArg(x_39);
if (x_40 == 0)
{
x_29 = x_4;
x_30 = x_5;
goto block_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = l_Lake_validateManifest___elam__1___redArg___closed__2;
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_3);
x_42 = l_Lake_validateManifest___elam__0(x_3, x_1, x_41, x_4, x_5);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_29 = x_4;
x_30 = x_43;
goto block_38;
}
block_38:
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; 
x_31 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_32 = l_Option_decEqOption___redArg____x40_Init_Data_Option_Basic___hyg_5_(x_31, x_26, x_28);
x_33 = l_instDecidableNot___redArg(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lake_validateManifest___elam__1___redArg___closed__1;
x_37 = l_Lake_validateManifest___elam__0(x_3, x_1, x_36, x_29, x_30);
return x_37;
}
}
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lake_validateManifest___elam__1___redArg___closed__0;
x_9 = l_Lake_validateManifest___elam__0(x_3, x_1, x_8, x_6, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_validateManifest___elam__1___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_validateManifest_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_6);
x_10 = lean_apply_4(x_1, x_5, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
x_7 = x_12;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_2);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_12 = l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0;
x_13 = lean_alloc_closure((void*)(l_Lake_validateManifest___elam__1___boxed), 6, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_1);
x_14 = 0;
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = l_Array_foldlMUnsafe_fold___at___Lake_validateManifest_spec__0(x_13, x_2, x_14, x_15, x_7, x_3, x_4);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_validateManifest___elam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_validateManifest___elam__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest___elam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_validateManifest___elam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_validateManifest_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_validateManifest_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_validateManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_validateManifest(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___elam__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dependency '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___elam__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' of '", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___elam__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' not in manifest; this suggests that the manifest is corrupt; use `lake update` to generate a new, complete file (warning: this will update ALL workspace dependencies)", 168, 168);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___elam__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' not in manifest; use `lake update ", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___elam__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` to add it", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___elam__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_20; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 4);
lean_inc(x_25);
lean_dec(x_12);
x_26 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_5, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_name_eq(x_28, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_7);
x_31 = l_Lake_Workspace_materializeDeps___elam__4___closed__0;
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
lean_inc(x_6);
x_34 = l_Lean_Name_toString(x_24, x_33, x_6);
x_35 = lean_string_append(x_31, x_34);
lean_dec(x_34);
x_36 = l_Lake_Workspace_materializeDeps___elam__4___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_unbox(x_32);
x_39 = l_Lean_Name_toString(x_28, x_38, x_6);
x_40 = lean_string_append(x_37, x_39);
lean_dec(x_39);
x_41 = l_Lake_Workspace_materializeDeps___elam__4___closed__2;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_box(3);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = lean_apply_2(x_14, x_44, x_15);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_28);
lean_dec(x_6);
x_53 = l_Lake_Workspace_materializeDeps___elam__4___closed__0;
x_54 = l_Lean_Name_toString(x_24, x_30, x_7);
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lake_Workspace_materializeDeps___elam__4___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_string_append(x_57, x_54);
lean_dec(x_54);
x_59 = l_Lake_Workspace_materializeDeps___elam__4___closed__4;
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_box(3);
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
x_64 = lean_apply_2(x_14, x_62, x_15);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
x_71 = lean_ctor_get(x_13, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_26, 0);
lean_inc(x_72);
lean_dec(x_26);
x_73 = lean_ctor_get(x_13, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4;
x_77 = l_Lake_PackageEntry_materialize(x_72, x_73, x_74, x_8, x_76, x_15);
lean_dec(x_73);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_159; uint8_t x_160; 
lean_dec(x_10);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_159 = lean_array_get_size(x_81);
x_160 = lean_nat_dec_lt(x_75, x_159);
if (x_160 == 0)
{
lean_dec(x_159);
lean_dec(x_81);
lean_dec(x_9);
x_82 = x_13;
x_83 = x_79;
goto block_158;
}
else
{
uint8_t x_161; 
x_161 = lean_nat_dec_le(x_159, x_159);
if (x_161 == 0)
{
lean_dec(x_159);
lean_dec(x_81);
lean_dec(x_9);
x_82 = x_13;
x_83 = x_79;
goto block_158;
}
else
{
lean_object* x_162; size_t x_163; size_t x_164; lean_object* x_165; 
x_162 = lean_box(0);
x_163 = 0;
x_164 = lean_usize_of_nat(x_159);
lean_dec(x_159);
lean_inc(x_14);
x_165 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_9, x_81, x_163, x_164, x_162, x_14, x_79);
lean_dec(x_81);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_82 = x_13;
x_83 = x_166;
goto block_158;
}
else
{
uint8_t x_167; 
lean_dec(x_80);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_165);
if (x_167 == 0)
{
return x_165;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_165, 0);
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_165);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
block_158:
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lake_loadDepPackage(x_80, x_25, x_1, x_2, x_82, x_76, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_84, 1);
x_88 = lean_ctor_get(x_84, 0);
lean_dec(x_88);
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_array_get_size(x_90);
x_92 = lean_nat_dec_lt(x_75, x_91);
if (x_92 == 0)
{
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_14);
lean_dec(x_3);
lean_ctor_set(x_84, 0, x_89);
return x_84;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_le(x_91, x_91);
if (x_93 == 0)
{
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_14);
lean_dec(x_3);
lean_ctor_set(x_84, 0, x_89);
return x_84;
}
else
{
lean_object* x_94; size_t x_95; size_t x_96; lean_object* x_97; 
lean_free_object(x_84);
x_94 = lean_box(0);
x_95 = 0;
x_96 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_97 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_3, x_90, x_95, x_96, x_94, x_14, x_87);
lean_dec(x_90);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_97, 0);
lean_dec(x_99);
lean_ctor_set(x_97, 0, x_89);
return x_97;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_89);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_89);
x_102 = !lean_is_exclusive(x_97);
if (x_102 == 0)
{
return x_97;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_97, 0);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_97);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_84, 1);
lean_inc(x_106);
lean_dec(x_84);
x_107 = lean_ctor_get(x_85, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_85, 1);
lean_inc(x_108);
lean_dec(x_85);
x_109 = lean_array_get_size(x_108);
x_110 = lean_nat_dec_lt(x_75, x_109);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_14);
lean_dec(x_3);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_109, x_109);
if (x_112 == 0)
{
lean_object* x_113; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_14);
lean_dec(x_3);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_106);
return x_113;
}
else
{
lean_object* x_114; size_t x_115; size_t x_116; lean_object* x_117; 
x_114 = lean_box(0);
x_115 = 0;
x_116 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_117 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_3, x_108, x_115, x_116, x_114, x_14, x_106);
lean_dec(x_108);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_107);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_107);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_3);
x_125 = !lean_is_exclusive(x_84);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_126 = lean_ctor_get(x_84, 1);
x_127 = lean_ctor_get(x_84, 0);
lean_dec(x_127);
x_128 = lean_ctor_get(x_85, 1);
lean_inc(x_128);
lean_dec(x_85);
x_129 = lean_array_get_size(x_128);
x_130 = lean_nat_dec_lt(x_75, x_129);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_14);
lean_dec(x_4);
x_131 = lean_box(0);
lean_ctor_set_tag(x_84, 1);
lean_ctor_set(x_84, 0, x_131);
return x_84;
}
else
{
uint8_t x_132; 
lean_free_object(x_84);
x_132 = lean_nat_dec_le(x_129, x_129);
if (x_132 == 0)
{
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_14);
lean_dec(x_4);
x_16 = x_126;
goto block_19;
}
else
{
lean_object* x_133; size_t x_134; size_t x_135; lean_object* x_136; 
x_133 = lean_box(0);
x_134 = 0;
x_135 = lean_usize_of_nat(x_129);
lean_dec(x_129);
x_136 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_4, x_128, x_134, x_135, x_133, x_14, x_126);
lean_dec(x_128);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_16 = x_137;
goto block_19;
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_136);
if (x_138 == 0)
{
return x_136;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_136, 0);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_136);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_84, 1);
lean_inc(x_142);
lean_dec(x_84);
x_143 = lean_ctor_get(x_85, 1);
lean_inc(x_143);
lean_dec(x_85);
x_144 = lean_array_get_size(x_143);
x_145 = lean_nat_dec_lt(x_75, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_14);
lean_dec(x_4);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_142);
return x_147;
}
else
{
uint8_t x_148; 
x_148 = lean_nat_dec_le(x_144, x_144);
if (x_148 == 0)
{
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_14);
lean_dec(x_4);
x_16 = x_142;
goto block_19;
}
else
{
lean_object* x_149; size_t x_150; size_t x_151; lean_object* x_152; 
x_149 = lean_box(0);
x_150 = 0;
x_151 = lean_usize_of_nat(x_144);
lean_dec(x_144);
x_152 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_4, x_143, x_150, x_151, x_149, x_14, x_142);
lean_dec(x_143);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_16 = x_153;
goto block_19;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_156 = x_152;
} else {
 lean_dec_ref(x_152);
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
}
}
else
{
uint8_t x_171; 
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_77);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_172 = lean_ctor_get(x_77, 1);
x_173 = lean_ctor_get(x_77, 0);
lean_dec(x_173);
x_174 = lean_ctor_get(x_78, 1);
lean_inc(x_174);
lean_dec(x_78);
x_175 = lean_array_get_size(x_174);
x_176 = lean_nat_dec_lt(x_75, x_175);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_14);
lean_dec(x_10);
x_177 = lean_box(0);
lean_ctor_set_tag(x_77, 1);
lean_ctor_set(x_77, 0, x_177);
return x_77;
}
else
{
uint8_t x_178; 
lean_free_object(x_77);
x_178 = lean_nat_dec_le(x_175, x_175);
if (x_178 == 0)
{
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_14);
lean_dec(x_10);
x_20 = x_172;
goto block_23;
}
else
{
lean_object* x_179; size_t x_180; size_t x_181; lean_object* x_182; 
x_179 = lean_box(0);
x_180 = 0;
x_181 = lean_usize_of_nat(x_175);
lean_dec(x_175);
x_182 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_10, x_174, x_180, x_181, x_179, x_14, x_172);
lean_dec(x_174);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_20 = x_183;
goto block_23;
}
else
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_182);
if (x_184 == 0)
{
return x_182;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_182, 0);
x_186 = lean_ctor_get(x_182, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_182);
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
x_188 = lean_ctor_get(x_77, 1);
lean_inc(x_188);
lean_dec(x_77);
x_189 = lean_ctor_get(x_78, 1);
lean_inc(x_189);
lean_dec(x_78);
x_190 = lean_array_get_size(x_189);
x_191 = lean_nat_dec_lt(x_75, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_14);
lean_dec(x_10);
x_192 = lean_box(0);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_188);
return x_193;
}
else
{
uint8_t x_194; 
x_194 = lean_nat_dec_le(x_190, x_190);
if (x_194 == 0)
{
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_14);
lean_dec(x_10);
x_20 = x_188;
goto block_23;
}
else
{
lean_object* x_195; size_t x_196; size_t x_197; lean_object* x_198; 
x_195 = lean_box(0);
x_196 = 0;
x_197 = lean_usize_of_nat(x_190);
lean_dec(x_190);
x_198 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_10, x_189, x_196, x_197, x_195, x_14, x_188);
lean_dec(x_189);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_20 = x_199;
goto block_23;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_202 = x_198;
} else {
 lean_dec_ref(x_198);
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
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___lam__0(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = 1;
x_13 = lean_usize_add(x_1, x_12);
x_14 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0(x_2, x_3, x_4, x_13, x_5, x_10, x_6, x_11, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_4, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_box_usize(x_4);
x_14 = lean_box_usize(x_5);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___lam__0___boxed), 9, 6);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_14);
lean_closure_set(x_15, 5, x_7);
x_16 = lean_array_uget(x_3, x_4);
lean_dec(x_3);
x_17 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___lam__1), 6, 4);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_7);
lean_closure_set(x_17, 3, x_8);
x_18 = lean_apply_6(x_12, lean_box(0), lean_box(0), x_17, x_15, x_9, x_10);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_6);
x_23 = lean_apply_4(x_22, lean_box(0), x_1, x_9, x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_8);
x_27 = lean_apply_4(x_25, lean_box(0), x_26, x_9, x_10);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13, x_9, x_14, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_3(x_1, x_2, x_3, x_8);
x_12 = lean_apply_6(x_4, lean_box(0), lean_box(0), x_11, x_5, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_apply_5(x_1, x_6, x_2, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_apply_4(x_2, lean_box(0), x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_name_eq(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_17 = lean_box(0);
lean_ctor_set(x_9, 0, x_17);
x_18 = lean_apply_2(x_3, lean_box(0), x_9);
x_19 = lean_apply_6(x_4, lean_box(0), lean_box(0), x_18, x_5, x_10, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_9);
lean_dec(x_5);
x_20 = l_Lean_Name_toString(x_15, x_16, x_6);
x_21 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_apply_2(x_7, lean_box(0), x_22);
x_24 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__4), 5, 2);
lean_closure_set(x_24, 0, x_13);
lean_closure_set(x_24, 1, x_3);
lean_inc(x_4);
x_25 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_23, x_24);
x_26 = lean_apply_6(x_4, lean_box(0), lean_box(0), x_25, x_8, x_10, x_11);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_name_eq(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_apply_2(x_3, lean_box(0), x_31);
x_33 = lean_apply_6(x_4, lean_box(0), lean_box(0), x_32, x_5, x_10, x_11);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
x_34 = l_Lean_Name_toString(x_28, x_29, x_6);
x_35 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_apply_2(x_7, lean_box(0), x_36);
x_38 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__4), 5, 2);
lean_closure_set(x_38, 0, x_27);
lean_closure_set(x_38, 1, x_3);
lean_inc(x_4);
x_39 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_37, x_38);
x_40 = lean_apply_6(x_4, lean_box(0), lean_box(0), x_39, x_8, x_10, x_11);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_14, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__3___boxed), 11, 8);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_6);
lean_closure_set(x_18, 6, x_7);
lean_closure_set(x_18, 7, x_8);
x_19 = lean_box(0);
lean_ctor_set(x_9, 0, x_19);
x_20 = lean_apply_2(x_17, lean_box(0), x_9);
x_21 = lean_apply_6(x_4, lean_box(0), lean_box(0), x_20, x_18, x_10, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_box(0);
lean_ctor_set(x_9, 0, x_23);
x_24 = lean_apply_4(x_22, lean_box(0), x_9, x_10, x_11);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_ctor_get(x_25, 4);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_27, x_28);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__3___boxed), 11, 8);
lean_closure_set(x_31, 0, x_3);
lean_closure_set(x_31, 1, x_28);
lean_closure_set(x_31, 2, x_30);
lean_closure_set(x_31, 3, x_4);
lean_closure_set(x_31, 4, x_5);
lean_closure_set(x_31, 5, x_6);
lean_closure_set(x_31, 6, x_7);
lean_closure_set(x_31, 7, x_8);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_34 = lean_apply_2(x_30, lean_box(0), x_33);
x_35 = lean_apply_6(x_4, lean_box(0), lean_box(0), x_34, x_31, x_10, x_11);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_apply_4(x_36, lean_box(0), x_38, x_10, x_11);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, lean_box(0), x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_4(x_1, lean_box(0), x_9, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, lean_box(0), x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_4(x_1, lean_box(0), x_9, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__6), 4, 1);
lean_closure_set(x_8, 0, x_7);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__7), 4, 1);
lean_closure_set(x_9, 0, x_7);
lean_inc(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_2);
x_11 = lean_apply_2(x_7, lean_box(0), x_10);
lean_inc(x_3);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_11, x_9);
lean_inc(x_3);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_8);
x_14 = lean_apply_6(x_3, lean_box(0), lean_box(0), x_13, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_7, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_box(x_14);
x_18 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = 1;
x_20 = lean_usize_sub(x_7, x_19);
x_21 = lean_box_usize(x_20);
x_22 = lean_box_usize(x_8);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__1___boxed), 12, 9);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_21);
lean_closure_set(x_23, 7, x_22);
lean_closure_set(x_23, 8, x_10);
x_24 = lean_array_uget(x_6, x_20);
lean_dec(x_6);
lean_inc(x_16);
lean_inc(x_24);
lean_inc(x_3);
x_25 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 10, 5);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_3);
lean_closure_set(x_25, 2, x_24);
lean_closure_set(x_25, 3, x_16);
lean_closure_set(x_25, 4, x_4);
x_26 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__2), 5, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_10);
lean_inc(x_26);
lean_inc(x_16);
lean_inc(x_15);
x_27 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__5), 11, 8);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_15);
lean_closure_set(x_27, 2, x_3);
lean_closure_set(x_27, 3, x_16);
lean_closure_set(x_27, 4, x_26);
lean_closure_set(x_27, 5, x_18);
lean_closure_set(x_27, 6, x_5);
lean_closure_set(x_27, 7, x_26);
lean_inc(x_16);
x_28 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__8), 6, 4);
lean_closure_set(x_28, 0, x_15);
lean_closure_set(x_28, 1, x_11);
lean_closure_set(x_28, 2, x_16);
lean_closure_set(x_28, 3, x_27);
x_29 = lean_apply_6(x_16, lean_box(0), lean_box(0), x_28, x_23, x_12, x_13);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
x_34 = lean_apply_4(x_33, lean_box(0), x_1, x_12, x_13);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_11);
x_38 = lean_apply_4(x_36, lean_box(0), x_37, x_12, x_13);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_7, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_box(x_14);
x_18 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = 1;
x_20 = lean_usize_sub(x_7, x_19);
x_21 = lean_box_usize(x_20);
x_22 = lean_box_usize(x_8);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__1___boxed), 12, 9);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_21);
lean_closure_set(x_23, 7, x_22);
lean_closure_set(x_23, 8, x_10);
x_24 = lean_array_uget(x_6, x_20);
lean_dec(x_6);
lean_inc(x_16);
lean_inc(x_24);
lean_inc(x_3);
x_25 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 10, 5);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_3);
lean_closure_set(x_25, 2, x_24);
lean_closure_set(x_25, 3, x_16);
lean_closure_set(x_25, 4, x_4);
x_26 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__2), 5, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_10);
lean_inc(x_26);
lean_inc(x_16);
lean_inc(x_15);
x_27 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__5), 11, 8);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_15);
lean_closure_set(x_27, 2, x_3);
lean_closure_set(x_27, 3, x_16);
lean_closure_set(x_27, 4, x_26);
lean_closure_set(x_27, 5, x_18);
lean_closure_set(x_27, 6, x_5);
lean_closure_set(x_27, 7, x_26);
lean_inc(x_16);
x_28 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__8), 6, 4);
lean_closure_set(x_28, 0, x_15);
lean_closure_set(x_28, 1, x_11);
lean_closure_set(x_28, 2, x_16);
lean_closure_set(x_28, 3, x_27);
x_29 = lean_apply_6(x_16, lean_box(0), lean_box(0), x_28, x_23, x_12, x_13);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
x_34 = lean_apply_4(x_33, lean_box(0), x_1, x_12, x_13);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_11);
x_38 = lean_apply_4(x_36, lean_box(0), x_37, x_12, x_13);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_box(0);
x_9 = l_Lake_Workspace_addPackage(x_6, x_7);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_8);
x_10 = lean_apply_4(x_1, lean_box(0), x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = l_Lake_Workspace_addPackage(x_11, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_apply_4(x_1, lean_box(0), x_15, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_get_size(x_12);
x_14 = lean_box(0);
x_15 = lean_nat_dec_lt(x_1, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_6, 0, x_14);
x_16 = lean_apply_4(x_2, lean_box(0), x_6, x_7, x_8);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_13, x_13);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_6, 0, x_14);
x_18 = lean_apply_4(x_2, lean_box(0), x_6, x_7, x_8);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
lean_free_object(x_6);
lean_dec(x_2);
x_19 = lean_usize_of_nat(x_1);
x_20 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_21 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0(x_3, x_4, x_12, x_19, x_20, x_14, x_5, x_11, x_7, x_8);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_ctor_get(x_22, 3);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_24);
x_26 = lean_box(0);
x_27 = lean_nat_dec_lt(x_1, x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_apply_4(x_2, lean_box(0), x_28, x_7, x_8);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_25, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_23);
x_32 = lean_apply_4(x_2, lean_box(0), x_31, x_7, x_8);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
lean_dec(x_2);
x_33 = lean_usize_of_nat(x_1);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0(x_3, x_4, x_24, x_33, x_34, x_26, x_5, x_23, x_7, x_8);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, lean_box(0), x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_4(x_1, lean_box(0), x_9, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, lean_box(0), x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_4(x_1, lean_box(0), x_9, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__2), 4, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__3), 4, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_8);
lean_ctor_set(x_4, 0, x_8);
x_12 = lean_apply_2(x_1, lean_box(0), x_4);
lean_inc(x_2);
x_13 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_12, x_11);
lean_inc(x_2);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_13, x_10);
x_15 = lean_apply_6(x_2, lean_box(0), lean_box(0), x_14, x_3, x_5, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__2), 4, 1);
lean_closure_set(x_17, 0, x_1);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__3), 4, 1);
lean_closure_set(x_18, 0, x_1);
lean_inc(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_16);
x_20 = lean_apply_2(x_1, lean_box(0), x_19);
lean_inc(x_2);
x_21 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_20, x_18);
lean_inc(x_2);
x_22 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_21, x_17);
x_23 = lean_apply_6(x_2, lean_box(0), lean_box(0), x_22, x_3, x_5, x_6);
return x_23;
}
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__5___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 9);
lean_inc(x_17);
x_18 = lean_array_get_size(x_16);
lean_dec(x_16);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__1___boxed), 8, 5);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_inc(x_6);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__4), 6, 3);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_6);
lean_closure_set(x_20, 2, x_19);
x_21 = lean_array_get_size(x_17);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_22, x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_10, 0, x_23);
x_25 = lean_apply_2(x_2, lean_box(0), x_10);
x_26 = lean_apply_6(x_6, lean_box(0), lean_box(0), x_25, x_20, x_11, x_12);
return x_26;
}
else
{
size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_10);
lean_dec(x_2);
x_27 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_28 = lean_box_usize(x_27);
x_29 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__5___boxed__const__1;
x_30 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1___boxed), 13, 11);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_7);
lean_closure_set(x_30, 2, x_1);
lean_closure_set(x_30, 3, x_8);
lean_closure_set(x_30, 4, x_9);
lean_closure_set(x_30, 5, x_17);
lean_closure_set(x_30, 6, x_28);
lean_closure_set(x_30, 7, x_29);
lean_closure_set(x_30, 8, x_23);
lean_closure_set(x_30, 9, x_5);
lean_closure_set(x_30, 10, x_15);
x_31 = lean_apply_6(x_6, lean_box(0), lean_box(0), x_30, x_20, x_11, x_12);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_ctor_get(x_32, 3);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_1, 9);
lean_inc(x_35);
x_36 = lean_array_get_size(x_34);
lean_dec(x_34);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_37 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__1___boxed), 8, 5);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_2);
lean_closure_set(x_37, 2, x_3);
lean_closure_set(x_37, 3, x_4);
lean_closure_set(x_37, 4, x_5);
lean_inc(x_6);
lean_inc(x_2);
x_38 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__4), 6, 3);
lean_closure_set(x_38, 0, x_2);
lean_closure_set(x_38, 1, x_6);
lean_closure_set(x_38, 2, x_37);
x_39 = lean_array_get_size(x_35);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_box(0);
x_42 = lean_nat_dec_lt(x_40, x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_33);
x_44 = lean_apply_2(x_2, lean_box(0), x_43);
x_45 = lean_apply_6(x_6, lean_box(0), lean_box(0), x_44, x_38, x_11, x_12);
return x_45;
}
else
{
size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
x_46 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_47 = lean_box_usize(x_46);
x_48 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__5___boxed__const__1;
x_49 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1___boxed), 13, 11);
lean_closure_set(x_49, 0, x_3);
lean_closure_set(x_49, 1, x_7);
lean_closure_set(x_49, 2, x_1);
lean_closure_set(x_49, 3, x_8);
lean_closure_set(x_49, 4, x_9);
lean_closure_set(x_49, 5, x_35);
lean_closure_set(x_49, 6, x_47);
lean_closure_set(x_49, 7, x_48);
lean_closure_set(x_49, 8, x_41);
lean_closure_set(x_49, 9, x_5);
lean_closure_set(x_49, 10, x_33);
x_50 = lean_apply_6(x_6, lean_box(0), lean_box(0), x_49, x_38, x_11, x_12);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__0), 4, 1);
lean_closure_set(x_13, 0, x_12);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__5), 12, 9);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_6);
lean_closure_set(x_14, 5, x_11);
lean_closure_set(x_14, 6, x_3);
lean_closure_set(x_14, 7, x_13);
lean_closure_set(x_14, 8, x_2);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__2), 4, 1);
lean_closure_set(x_18, 0, x_12);
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__3), 4, 1);
lean_closure_set(x_19, 0, x_12);
lean_inc(x_7);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_7);
x_20 = lean_apply_2(x_12, lean_box(0), x_1);
lean_inc(x_11);
x_21 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_20, x_19);
lean_inc(x_11);
x_22 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_21, x_18);
x_23 = lean_apply_6(x_11, lean_box(0), lean_box(0), x_22, x_14, x_8, x_9);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
lean_inc(x_12);
x_24 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__2), 4, 1);
lean_closure_set(x_24, 0, x_12);
lean_inc(x_12);
x_25 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__3), 4, 1);
lean_closure_set(x_25, 0, x_12);
lean_inc(x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_7);
x_27 = lean_apply_2(x_12, lean_box(0), x_26);
lean_inc(x_11);
x_28 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_27, x_25);
lean_inc(x_11);
x_29 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_28, x_24);
x_30 = lean_apply_6(x_11, lean_box(0), lean_box(0), x_29, x_14, x_8, x_9);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0(x_1, x_2, x_3, x_5, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_8);
lean_inc(x_6);
x_12 = lean_apply_5(x_1, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
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
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_7 = x_16;
x_9 = x_14;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_7, 4);
lean_inc(x_11);
x_12 = 1;
x_13 = lean_usize_sub(x_4, x_12);
x_14 = lean_array_uget(x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_11, x_15);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_name_eq(x_17, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_1);
x_19 = lean_apply_5(x_2, x_1, x_14, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lake_Workspace_addPackage(x_22, x_23);
x_4 = x_13;
x_6 = x_24;
x_7 = x_25;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(x_10);
x_32 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = l_Lean_Name_toString(x_17, x_18, x_32);
x_34 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_box(3);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_apply_2(x_8, x_37, x_9);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_46 = lean_box(0);
x_4 = x_13;
x_6 = x_46;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_6);
lean_ctor_set(x_48, 1, x_7);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_4, x_5);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_8, 4);
lean_inc(x_12);
x_13 = 1;
x_14 = lean_usize_sub(x_4, x_13);
x_15 = lean_array_uget(x_3, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_12, x_16);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_name_eq(x_18, x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_inc(x_2);
lean_inc(x_9);
lean_inc(x_1);
x_20 = lean_apply_5(x_2, x_1, x_15, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l_Lake_Workspace_addPackage(x_23, x_24);
x_27 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_14, x_5, x_25, x_26, x_9, x_22);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_9);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_box(x_11);
x_33 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = l_Lean_Name_toString(x_18, x_19, x_33);
x_35 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_box(3);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
x_40 = lean_apply_2(x_9, x_38, x_10);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_47 = lean_box(0);
x_48 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_14, x_5, x_47, x_8, x_9, x_10);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_6);
lean_ctor_set(x_49, 1, x_8);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_10);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_box(0);
x_13 = lean_nat_dec_lt(x_1, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_free_object(x_4);
x_17 = lean_usize_of_nat(x_1);
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__0(x_2, x_10, x_17, x_18, x_12, x_3, x_8, x_5, x_6);
lean_dec(x_10);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_1, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_22, x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_1);
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__0(x_2, x_21, x_30, x_31, x_23, x_3, x_20, x_5, x_6);
lean_dec(x_21);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 9);
lean_inc(x_9);
x_10 = lean_array_get_size(x_8);
x_11 = lean_array_get_size(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_box(0);
x_14 = lean_nat_dec_le(x_11, x_11);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_12, x_11);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_10, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_10, x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
else
{
size_t x_22; lean_object* x_23; 
x_22 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_23 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__0(x_2, x_8, x_22, x_22, x_13, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_23;
}
}
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
lean_dec(x_8);
x_24 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_25 = 0;
lean_inc(x_6);
x_26 = l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1(x_3, x_1, x_9, x_24, x_25, x_13, x_4, x_5, x_6, x_7);
lean_dec(x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0___lam__0(x_10, x_2, x_4, x_27, x_6, x_28);
lean_dec(x_10);
return x_29;
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_26;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
x_30 = lean_nat_dec_lt(x_12, x_11);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_5);
x_32 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0___lam__0(x_10, x_2, x_4, x_31, x_6, x_7);
lean_dec(x_10);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_34 = 0;
lean_inc(x_6);
x_35 = l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1(x_3, x_1, x_9, x_33, x_34, x_13, x_4, x_5, x_6, x_7);
lean_dec(x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0___lam__0(x_10, x_2, x_4, x_36, x_6, x_37);
lean_dec(x_10);
return x_38;
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0(x_1, x_3, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lake_depCycleError___redArg___closed__0;
x_5 = l_Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5(x_1);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = lean_box(3);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_apply_2(x_2, x_8, x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg(x_1, x_3, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
lean_inc(x_9);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg___lam__0___boxed), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_apply_6(x_1, x_2, x_10, x_9, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
x_14 = l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(x_7, x_8, x_3, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
lean_inc(x_7);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
x_19 = l_List_appendTR___redArg(x_14, x_18);
x_20 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5___redArg(x_19, x_5, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_inc(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_12);
x_24 = l_List_appendTR___redArg(x_22, x_23);
x_25 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5___redArg(x_24, x_5, x_6);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
lean_inc(x_9);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg___lam__0___boxed), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_apply_6(x_1, x_2, x_10, x_9, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0;
x_14 = l_List_partition_loop___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__4(x_7, x_8, x_3, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
lean_inc(x_7);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_12);
x_19 = l_List_appendTR___redArg(x_14, x_18);
x_20 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5___redArg(x_19, x_5, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_inc(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_12);
x_24 = l_List_appendTR___redArg(x_22, x_23);
x_25 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5___redArg(x_24, x_5, x_6);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6___redArg(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6___redArg(x_1, x_3, x_4, x_2, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
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
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
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
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_Workspace_materializeDeps_spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_string_dec_eq(x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_materializeDeps___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("missing manifest; use `lake update` to generate one", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Workspace_materializeDeps___closed__0;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package-overrides.json", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("manifest out of date: packages directory changed; use `lake update` to rebuild the manifest (warning: this will update ALL workspace dependencies)", 146, 146);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_materializeDeps___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_Workspace_materializeDeps___closed__3;
x_2 = lean_box(2);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_115; lean_object* x_116; uint8_t x_123; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___lam__0), 2, 0);
x_11 = l_Lake_Workspace_updateAndMaterializeCore___closed__0;
x_123 = l_Array_isEmpty___redArg(x_9);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 3);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = l_System_FilePath_normalize(x_126);
x_128 = l_Lake_mkRelPathString(x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_Workspace_materializeDeps_spec__10(x_8, x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = l_Lake_Workspace_materializeDeps___closed__4;
lean_inc(x_6);
x_132 = lean_apply_2(x_6, x_131, x_7);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_115 = x_6;
x_116 = x_133;
goto block_122;
}
else
{
x_115 = x_6;
x_116 = x_7;
goto block_122;
}
}
else
{
x_115 = x_6;
x_116 = x_7;
goto block_122;
}
block_27:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = l_Lake_Workspace_addPackage(x_14, x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_box(x_17);
x_21 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___lam__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_box(x_4);
lean_inc(x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___elam__4___boxed), 15, 10);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_11);
lean_closure_set(x_23, 3, x_11);
lean_closure_set(x_23, 4, x_12);
lean_closure_set(x_23, 5, x_21);
lean_closure_set(x_23, 6, x_21);
lean_closure_set(x_23, 7, x_15);
lean_closure_set(x_23, 8, x_11);
lean_closure_set(x_23, 9, x_11);
x_24 = lean_box(0);
x_25 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0), 7, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5(x_25, x_18, x_19, x_24, x_16, x_13);
return x_26;
}
block_47:
{
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = l_Array_isEmpty___redArg(x_30);
lean_dec(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_1);
x_35 = l_Lake_Workspace_materializeDeps___closed__1;
x_36 = lean_apply_2(x_32, x_35, x_28);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_box(0);
x_44 = lean_unbox(x_43);
x_12 = x_33;
x_13 = x_28;
x_14 = x_29;
x_15 = x_31;
x_16 = x_32;
x_17 = x_44;
goto block_27;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_30);
x_45 = lean_box(0);
x_46 = lean_unbox(x_45);
x_12 = x_33;
x_13 = x_28;
x_14 = x_29;
x_15 = x_31;
x_16 = x_32;
x_17 = x_46;
goto block_27;
}
}
block_61:
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_array_get_size(x_5);
x_56 = lean_nat_dec_lt(x_52, x_55);
if (x_56 == 0)
{
lean_dec(x_55);
lean_dec(x_10);
x_28 = x_48;
x_29 = x_49;
x_30 = x_51;
x_31 = x_50;
x_32 = x_53;
x_33 = x_54;
goto block_47;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_55, x_55);
if (x_57 == 0)
{
lean_dec(x_55);
lean_dec(x_10);
x_28 = x_48;
x_29 = x_49;
x_30 = x_51;
x_31 = x_50;
x_32 = x_53;
x_33 = x_54;
goto block_47;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_60 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_10, x_5, x_58, x_59, x_54);
x_28 = x_48;
x_29 = x_49;
x_30 = x_51;
x_31 = x_50;
x_32 = x_53;
x_33 = x_60;
goto block_47;
}
}
}
block_102:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 9);
lean_inc(x_69);
lean_inc(x_65);
lean_inc(x_66);
x_70 = l_Lake_validateManifest(x_66, x_69, x_65, x_62);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lake_Workspace_writeManifest___closed__0;
x_73 = l_Lake_joinRelative(x_68, x_72);
x_74 = l_Lake_Workspace_materializeDeps___closed__2;
x_75 = l_Lake_joinRelative(x_73, x_74);
x_76 = l_Lake_Manifest_tryLoadEntries(x_75, x_71);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_array_get_size(x_77);
x_80 = lean_nat_dec_lt(x_64, x_79);
if (x_80 == 0)
{
lean_dec(x_79);
lean_dec(x_77);
x_48 = x_78;
x_49 = x_67;
x_50 = x_63;
x_51 = x_69;
x_52 = x_64;
x_53 = x_65;
x_54 = x_66;
goto block_61;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_79, x_79);
if (x_81 == 0)
{
lean_dec(x_79);
lean_dec(x_77);
x_48 = x_78;
x_49 = x_67;
x_50 = x_63;
x_51 = x_69;
x_52 = x_64;
x_53 = x_65;
x_54 = x_66;
goto block_61;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_79);
lean_dec(x_79);
lean_inc(x_10);
x_84 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_10, x_77, x_82, x_83, x_66);
lean_dec(x_77);
x_48 = x_78;
x_49 = x_67;
x_50 = x_63;
x_51 = x_69;
x_52 = x_64;
x_53 = x_65;
x_54 = x_84;
goto block_61;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_85 = lean_ctor_get(x_76, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_76, 1);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_io_error_to_string(x_85);
x_88 = lean_box(3);
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
x_90 = lean_unbox(x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_90);
x_91 = lean_apply_2(x_65, x_89, x_86);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
x_94 = lean_box(0);
lean_ctor_set_tag(x_91, 1);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_70);
if (x_98 == 0)
{
return x_70;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_70, 0);
x_100 = lean_ctor_get(x_70, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_70);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_114:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_box(0);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_array_get_size(x_9);
x_109 = lean_nat_dec_lt(x_107, x_108);
if (x_109 == 0)
{
lean_dec(x_108);
lean_dec(x_9);
x_62 = x_103;
x_63 = x_105;
x_64 = x_107;
x_65 = x_104;
x_66 = x_106;
goto block_102;
}
else
{
uint8_t x_110; 
x_110 = lean_nat_dec_le(x_108, x_108);
if (x_110 == 0)
{
lean_dec(x_108);
lean_dec(x_9);
x_62 = x_103;
x_63 = x_105;
x_64 = x_107;
x_65 = x_104;
x_66 = x_106;
goto block_102;
}
else
{
size_t x_111; size_t x_112; lean_object* x_113; 
x_111 = 0;
x_112 = lean_usize_of_nat(x_108);
lean_dec(x_108);
lean_inc(x_10);
x_113 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_10, x_9, x_111, x_112, x_106);
lean_dec(x_9);
x_62 = x_103;
x_63 = x_105;
x_64 = x_107;
x_65 = x_104;
x_66 = x_113;
goto block_102;
}
}
}
block_122:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_1, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 3);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
x_120 = l_System_FilePath_normalize(x_119);
x_103 = x_116;
x_104 = x_115;
x_105 = x_120;
goto block_114;
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_8, 0);
lean_inc(x_121);
lean_dec(x_8);
x_103 = x_116;
x_104 = x_115;
x_105 = x_121;
goto block_114;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___elam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l_Lake_Workspace_materializeDeps___elam__4(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___lam__0(x_10, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__0(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_14, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_16 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_15, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_15 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_16 = l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_15, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__0(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_foldrMUnsafe_fold___at___Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_foldrMUnsafe_fold___at_____private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at___Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6_spec__6___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_recFetch___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_Workspace_materializeDeps_spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_Workspace_materializeDeps_spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Workspace_materializeDeps___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lake_Workspace_materializeDeps(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_5);
return x_9;
}
}
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
l_Lake_stdMismatchError___closed__0 = _init_l_Lake_stdMismatchError___closed__0();
lean_mark_persistent(l_Lake_stdMismatchError___closed__0);
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
l_Lake_loadDepPackage___closed__0 = _init_l_Lake_loadDepPackage___closed__0();
lean_mark_persistent(l_Lake_loadDepPackage___closed__0);
l_Lake_loadDepPackage___closed__1 = _init_l_Lake_loadDepPackage___closed__1();
lean_mark_persistent(l_Lake_loadDepPackage___closed__1);
l_Lake_depCycleError___redArg___closed__0 = _init_l_Lake_depCycleError___redArg___closed__0();
lean_mark_persistent(l_Lake_depCycleError___redArg___closed__0);
l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0 = _init_l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0();
lean_mark_persistent(l_Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0);
l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__3___closed__0);
l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0);
l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___closed__0);
l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0);
l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6();
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7();
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8();
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9);
l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10 = _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10);
l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0 = _init_l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0);
l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1);
l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0 = _init_l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__0);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__1);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__2);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__3);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__4 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__4();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__4);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__5 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__5();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__5);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__6 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__6();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__6);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__7 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__7();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__7);
l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__8 = _init_l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__8();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_validateDep___closed__8);
l_Lake_restartCode = _init_l_Lake_restartCode();
l_Lake_Workspace_updateToolchain___elam__0___closed__0 = _init_l_Lake_Workspace_updateToolchain___elam__0___closed__0();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___elam__0___closed__0);
l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__0);
l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateToolchain_spec__0___closed__1);
l_Lake_Workspace_updateToolchain___closed__0 = _init_l_Lake_Workspace_updateToolchain___closed__0();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__0);
l_Lake_Workspace_updateToolchain___closed__1 = _init_l_Lake_Workspace_updateToolchain___closed__1();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__1);
l_Lake_Workspace_updateToolchain___closed__2 = _init_l_Lake_Workspace_updateToolchain___closed__2();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__2);
l_Lake_Workspace_updateToolchain___closed__3 = _init_l_Lake_Workspace_updateToolchain___closed__3();
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
l_Lake_Workspace_updateToolchain___closed__10 = _init_l_Lake_Workspace_updateToolchain___closed__10();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__10);
l_Lake_Workspace_updateToolchain___closed__11 = _init_l_Lake_Workspace_updateToolchain___closed__11();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__11);
l_Lake_Workspace_updateToolchain___closed__12 = _init_l_Lake_Workspace_updateToolchain___closed__12();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__12);
l_Lake_Workspace_updateToolchain___closed__13 = _init_l_Lake_Workspace_updateToolchain___closed__13();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__13);
l_Lake_Workspace_updateToolchain___closed__14 = _init_l_Lake_Workspace_updateToolchain___closed__14();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__14);
l_Lake_Workspace_updateToolchain___closed__15 = _init_l_Lake_Workspace_updateToolchain___closed__15();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__15);
l_Lake_Workspace_updateToolchain___closed__16 = _init_l_Lake_Workspace_updateToolchain___closed__16();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__16);
l_Lake_Workspace_updateToolchain___closed__17 = _init_l_Lake_Workspace_updateToolchain___closed__17();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__17);
l_Lake_Workspace_updateToolchain___closed__18 = _init_l_Lake_Workspace_updateToolchain___closed__18();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__18);
l_Lake_Workspace_updateToolchain___closed__19 = _init_l_Lake_Workspace_updateToolchain___closed__19();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__19);
l_Lake_Workspace_updateToolchain___closed__20 = _init_l_Lake_Workspace_updateToolchain___closed__20();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__20);
l_Lake_Workspace_updateToolchain___closed__21 = _init_l_Lake_Workspace_updateToolchain___closed__21();
lean_mark_persistent(l_Lake_Workspace_updateToolchain___closed__21);
l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0 = _init_l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0);
l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1 = _init_l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1);
l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep___closed__0 = _init_l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep___closed__0();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep___closed__0);
l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__5___boxed__const__1 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__5___boxed__const__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___lam__5___boxed__const__1);
l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__0 = _init_l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__0();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__0);
l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__1 = _init_l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__1();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterializeCore___elam__1___closed__1);
l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0___lam__5___boxed__const__1 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0___lam__5___boxed__const__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_updateAndMaterializeCore___elam__0___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__0_spec__0___lam__5___boxed__const__1);
l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___closed__0 = _init_l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___closed__0();
lean_mark_persistent(l_List_mapTR_loop___at___Lake_formatCycle___at___Lake_depCycleError___at_____private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4_spec__5_spec__5_spec__5___closed__0);
l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4___closed__0 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4___closed__0();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_updateAndMaterializeCore___elam__5_spec__4___closed__0);
l_Lake_Workspace_updateAndMaterializeCore___closed__0 = _init_l_Lake_Workspace_updateAndMaterializeCore___closed__0();
lean_mark_persistent(l_Lake_Workspace_updateAndMaterializeCore___closed__0);
l_Lake_Workspace_writeManifest___closed__0 = _init_l_Lake_Workspace_writeManifest___closed__0();
lean_mark_persistent(l_Lake_Workspace_writeManifest___closed__0);
l_Lake_Package_runPostUpdateHooks___closed__0 = _init_l_Lake_Package_runPostUpdateHooks___closed__0();
lean_mark_persistent(l_Lake_Package_runPostUpdateHooks___closed__0);
l_Lake_validateManifest___elam__0___closed__0 = _init_l_Lake_validateManifest___elam__0___closed__0();
lean_mark_persistent(l_Lake_validateManifest___elam__0___closed__0);
l_Lake_validateManifest___elam__0___closed__1 = _init_l_Lake_validateManifest___elam__0___closed__1();
lean_mark_persistent(l_Lake_validateManifest___elam__0___closed__1);
l_Lake_validateManifest___elam__0___closed__2 = _init_l_Lake_validateManifest___elam__0___closed__2();
lean_mark_persistent(l_Lake_validateManifest___elam__0___closed__2);
l_Lake_validateManifest___elam__0___closed__3 = _init_l_Lake_validateManifest___elam__0___closed__3();
lean_mark_persistent(l_Lake_validateManifest___elam__0___closed__3);
l_Lake_validateManifest___elam__1___redArg___closed__0 = _init_l_Lake_validateManifest___elam__1___redArg___closed__0();
lean_mark_persistent(l_Lake_validateManifest___elam__1___redArg___closed__0);
l_Lake_validateManifest___elam__1___redArg___closed__1 = _init_l_Lake_validateManifest___elam__1___redArg___closed__1();
lean_mark_persistent(l_Lake_validateManifest___elam__1___redArg___closed__1);
l_Lake_validateManifest___elam__1___redArg___closed__2 = _init_l_Lake_validateManifest___elam__1___redArg___closed__2();
lean_mark_persistent(l_Lake_validateManifest___elam__1___redArg___closed__2);
l_Lake_Workspace_materializeDeps___elam__4___closed__0 = _init_l_Lake_Workspace_materializeDeps___elam__4___closed__0();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___elam__4___closed__0);
l_Lake_Workspace_materializeDeps___elam__4___closed__1 = _init_l_Lake_Workspace_materializeDeps___elam__4___closed__1();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___elam__4___closed__1);
l_Lake_Workspace_materializeDeps___elam__4___closed__2 = _init_l_Lake_Workspace_materializeDeps___elam__4___closed__2();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___elam__4___closed__2);
l_Lake_Workspace_materializeDeps___elam__4___closed__3 = _init_l_Lake_Workspace_materializeDeps___elam__4___closed__3();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___elam__4___closed__3);
l_Lake_Workspace_materializeDeps___elam__4___closed__4 = _init_l_Lake_Workspace_materializeDeps___elam__4___closed__4();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___elam__4___closed__4);
l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__5___boxed__const__1 = _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__5___boxed__const__1();
lean_mark_persistent(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___Lake_Workspace_materializeDeps___elam__0_spec__0___lam__5___boxed__const__1);
l_Lake_Workspace_materializeDeps___closed__0 = _init_l_Lake_Workspace_materializeDeps___closed__0();
lean_mark_persistent(l_Lake_Workspace_materializeDeps___closed__0);
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

// Lean compiler output
// Module: Lake.Load.Resolve
// Imports: public import Lake.Config.Workspace public import Lake.Load.Manifest import Lake.Util.IO import Lake.Util.StoreInsts import Lake.Config.Monad import Lake.Load.Materialize import Lake.Load.Lean.Eval import Lake.Load.Package import Init.Data.Vector.Lemmas import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic.Lemmas import Init.TacticsExtra import Lean.Runtime
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_resolveConfigFile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadConfigFile___redArg(lean_object*, lean_object*);
lean_object* l_Lake_mkPackage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
extern lean_object* l_Lake_toolchainFileName;
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Env_noToolchainVars(lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_io_exit(uint8_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object*);
uint8_t l_Lake_instDecidableEqToolchainVer_decEq(lean_object*, lean_object*);
uint8_t l_Lake_MaterializedDep_fixedToolchain(lean_object*);
uint8_t l_Lake_ToolchainVer_blt(lean_object*, lean_object*);
uint8_t l_Lake_ToolchainVer_ble(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_save(lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = ": package requires itself (or a package with the same name)"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unknown package `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "could not rename workspace packages directory: "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "workspace packages directory changed; renaming '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "' to '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3_value;
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4_value;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = ": no previous manifest, creating one from scratch"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = ": ignoring previous manifest because it failed to load: "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = ": ignoring missing manifest:\n  "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = ": ignoring manifest because it failed to load: "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l___private_Lake_Load_Resolve_0__Lake_restartCode;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\n    from "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\n  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " (fixed toolchain)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "toolchain not updated; multiple toolchain candidates:\n  "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "restarting Lake via Elan"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "run"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--install"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_value;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "no Elan detected; you will need to manually restart Lake"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "cannot auto-restart; you will need to manually restart Lake"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "updating toolchain to '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "toolchain not updated; already up-to-date"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "toolchain not updated; no toolchain information found"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "toolchain not updated; multiple toolchain candidates:"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18_value;
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": updating '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' with "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = ": running post-update hooks"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "manifest out of date: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " of dependency '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' changed; use `lake update "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "` to update it"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "git revision"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "source kind (git/path)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "git url"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dependency '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "' of '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "' not in manifest; this suggests that the manifest is corrupt; use `lake update` to generate a new, complete file (warning: this will update ALL workspace dependencies)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "' not in manifest; use `lake update "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` to add it"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Workspace_materializeDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "missing manifest; use `lake update` to generate one"};
static const lean_object* l_Lake_Workspace_materializeDeps___closed__0 = (const lean_object*)&l_Lake_Workspace_materializeDeps___closed__0_value;
static const lean_ctor_object l_Lake_Workspace_materializeDeps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_materializeDeps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Workspace_materializeDeps___closed__1 = (const lean_object*)&l_Lake_Workspace_materializeDeps___closed__1_value;
static const lean_string_object l_Lake_Workspace_materializeDeps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "package-overrides.json"};
static const lean_object* l_Lake_Workspace_materializeDeps___closed__2 = (const lean_object*)&l_Lake_Workspace_materializeDeps___closed__2_value;
static const lean_string_object l_Lake_Workspace_materializeDeps___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 147, .m_capacity = 147, .m_length = 146, .m_data = "manifest out of date: packages directory changed; use `lake update` to rebuild the manifest (warning: this will update ALL workspace dependencies)"};
static const lean_object* l_Lake_Workspace_materializeDeps___closed__3 = (const lean_object*)&l_Lake_Workspace_materializeDeps___closed__3_value;
static const lean_ctor_object l_Lake_Workspace_materializeDeps___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_materializeDeps___closed__3_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Workspace_materializeDeps___closed__4 = (const lean_object*)&l_Lake_Workspace_materializeDeps___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(lean_object* v_ws_3_, lean_object* v_dep_4_, lean_object* v_lakeOpts_5_, lean_object* v_leanOpts_6_, uint8_t v_reconfigure_7_){
_start:
{
lean_object* v_lakeEnv_8_; lean_object* v_packages_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v_manifestEntry_12_; lean_object* v_dir_13_; lean_object* v_pkgDir_14_; lean_object* v_relPkgDir_15_; lean_object* v_remoteUrl_16_; lean_object* v_name_17_; lean_object* v_scope_18_; lean_object* v_configFile_19_; lean_object* v_manifestFile_x3f_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___y_25_; 
v_lakeEnv_8_ = lean_ctor_get(v_ws_3_, 0);
v_packages_9_ = lean_ctor_get(v_ws_3_, 4);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_array_fget_borrowed(v_packages_9_, v___x_10_);
v_manifestEntry_12_ = lean_ctor_get(v_dep_4_, 4);
lean_inc_ref(v_manifestEntry_12_);
v_dir_13_ = lean_ctor_get(v___x_11_, 4);
v_pkgDir_14_ = lean_ctor_get(v_dep_4_, 0);
lean_inc_ref_n(v_pkgDir_14_, 2);
v_relPkgDir_15_ = lean_ctor_get(v_dep_4_, 1);
lean_inc_ref(v_relPkgDir_15_);
v_remoteUrl_16_ = lean_ctor_get(v_dep_4_, 2);
lean_inc_ref(v_remoteUrl_16_);
lean_dec_ref(v_dep_4_);
v_name_17_ = lean_ctor_get(v_manifestEntry_12_, 0);
lean_inc(v_name_17_);
v_scope_18_ = lean_ctor_get(v_manifestEntry_12_, 1);
lean_inc_ref(v_scope_18_);
v_configFile_19_ = lean_ctor_get(v_manifestEntry_12_, 2);
lean_inc_ref_n(v_configFile_19_, 2);
v_manifestFile_x3f_20_ = lean_ctor_get(v_manifestEntry_12_, 3);
lean_inc(v_manifestFile_x3f_20_);
lean_dec_ref(v_manifestEntry_12_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_array_get_size(v_packages_9_);
v___x_23_ = l_Lake_joinRelative(v_pkgDir_14_, v_configFile_19_);
if (lean_obj_tag(v_manifestFile_x3f_20_) == 0)
{
lean_object* v___x_30_; 
v___x_30_ = l_Lake_defaultManifestFile;
v___y_25_ = v___x_30_;
goto v___jp_24_;
}
else
{
lean_object* v_val_31_; 
v_val_31_ = lean_ctor_get(v_manifestFile_x3f_20_, 0);
lean_inc(v_val_31_);
lean_dec_ref_known(v_manifestFile_x3f_20_, 1);
v___y_25_ = v_val_31_;
goto v___jp_24_;
}
v___jp_24_:
{
lean_object* v___x_26_; uint8_t v___x_27_; uint8_t v___x_28_; lean_object* v___x_29_; 
v___x_26_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_27_ = 0;
v___x_28_ = 1;
lean_inc_ref(v_dir_13_);
lean_inc_ref(v_lakeEnv_8_);
v___x_29_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_29_, 0, v_lakeEnv_8_);
lean_ctor_set(v___x_29_, 1, v___x_21_);
lean_ctor_set(v___x_29_, 2, v_dir_13_);
lean_ctor_set(v___x_29_, 3, v___x_22_);
lean_ctor_set(v___x_29_, 4, v_name_17_);
lean_ctor_set(v___x_29_, 5, v_relPkgDir_15_);
lean_ctor_set(v___x_29_, 6, v_pkgDir_14_);
lean_ctor_set(v___x_29_, 7, v_configFile_19_);
lean_ctor_set(v___x_29_, 8, v___x_23_);
lean_ctor_set(v___x_29_, 9, v___x_21_);
lean_ctor_set(v___x_29_, 10, v___y_25_);
lean_ctor_set(v___x_29_, 11, v___x_26_);
lean_ctor_set(v___x_29_, 12, v_lakeOpts_5_);
lean_ctor_set(v___x_29_, 13, v_leanOpts_6_);
lean_ctor_set(v___x_29_, 14, v_scope_18_);
lean_ctor_set(v___x_29_, 15, v_remoteUrl_16_);
lean_ctor_set_uint8(v___x_29_, sizeof(void*)*16, v_reconfigure_7_);
lean_ctor_set_uint8(v___x_29_, sizeof(void*)*16 + 1, v___x_27_);
lean_ctor_set_uint8(v___x_29_, sizeof(void*)*16 + 2, v___x_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___boxed(lean_object* v_ws_32_, lean_object* v_dep_33_, lean_object* v_lakeOpts_34_, lean_object* v_leanOpts_35_, lean_object* v_reconfigure_36_){
_start:
{
uint8_t v_reconfigure_boxed_37_; lean_object* v_res_38_; 
v_reconfigure_boxed_37_ = lean_unbox(v_reconfigure_36_);
v_res_38_ = l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(v_ws_32_, v_dep_33_, v_lakeOpts_34_, v_leanOpts_35_, v_reconfigure_boxed_37_);
lean_dec_ref(v_ws_32_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(lean_object* v_as_39_, size_t v_i_40_, size_t v_stop_41_, lean_object* v_b_42_){
_start:
{
uint8_t v___x_43_; 
v___x_43_ = lean_usize_dec_eq(v_i_40_, v_stop_41_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v_name_45_; lean_object* v_config_46_; lean_object* v_lakeEnv_47_; lean_object* v_lakeConfig_48_; lean_object* v_lakeCache_49_; lean_object* v_lakeArgs_x3f_50_; lean_object* v_packages_51_; lean_object* v_packageMap_52_; lean_object* v_facetConfigs_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_64_; 
v___x_44_ = lean_array_uget_borrowed(v_as_39_, v_i_40_);
v_name_45_ = lean_ctor_get(v___x_44_, 0);
v_config_46_ = lean_ctor_get(v___x_44_, 1);
v_lakeEnv_47_ = lean_ctor_get(v_b_42_, 0);
v_lakeConfig_48_ = lean_ctor_get(v_b_42_, 1);
v_lakeCache_49_ = lean_ctor_get(v_b_42_, 2);
v_lakeArgs_x3f_50_ = lean_ctor_get(v_b_42_, 3);
v_packages_51_ = lean_ctor_get(v_b_42_, 4);
v_packageMap_52_ = lean_ctor_get(v_b_42_, 5);
v_facetConfigs_53_ = lean_ctor_get(v_b_42_, 6);
v_isSharedCheck_64_ = !lean_is_exclusive(v_b_42_);
if (v_isSharedCheck_64_ == 0)
{
v___x_55_ = v_b_42_;
v_isShared_56_ = v_isSharedCheck_64_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_facetConfigs_53_);
lean_inc(v_packageMap_52_);
lean_inc(v_packages_51_);
lean_inc(v_lakeArgs_x3f_50_);
lean_inc(v_lakeCache_49_);
lean_inc(v_lakeConfig_48_);
lean_inc(v_lakeEnv_47_);
lean_dec(v_b_42_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_64_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_59_; 
lean_inc(v_config_46_);
lean_inc(v_name_45_);
v___x_57_ = l_Lake_FacetConfigMap_insert(v_name_45_, v_config_46_, v_facetConfigs_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 6, v___x_57_);
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_lakeEnv_47_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_lakeConfig_48_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v_lakeCache_49_);
lean_ctor_set(v_reuseFailAlloc_63_, 3, v_lakeArgs_x3f_50_);
lean_ctor_set(v_reuseFailAlloc_63_, 4, v_packages_51_);
lean_ctor_set(v_reuseFailAlloc_63_, 5, v_packageMap_52_);
lean_ctor_set(v_reuseFailAlloc_63_, 6, v___x_57_);
v___x_59_ = v_reuseFailAlloc_63_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
size_t v___x_60_; size_t v___x_61_; 
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_add(v_i_40_, v___x_60_);
v_i_40_ = v___x_61_;
v_b_42_ = v___x_59_;
goto _start;
}
}
}
else
{
return v_b_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0___boxed(lean_object* v_as_65_, lean_object* v_i_66_, lean_object* v_stop_67_, lean_object* v_b_68_){
_start:
{
size_t v_i_boxed_69_; size_t v_stop_boxed_70_; lean_object* v_res_71_; 
v_i_boxed_69_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_stop_boxed_70_ = lean_unbox_usize(v_stop_67_);
lean_dec(v_stop_67_);
v_res_71_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_as_65_, v_i_boxed_69_, v_stop_boxed_70_, v_b_68_);
lean_dec_ref(v_as_65_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(lean_object* v_decls_72_, lean_object* v_self_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_array_get_size(v_decls_72_);
v___x_76_ = lean_nat_dec_lt(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
return v_self_73_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = lean_nat_dec_le(v___x_75_, v___x_75_);
if (v___x_77_ == 0)
{
if (v___x_76_ == 0)
{
return v_self_73_;
}
else
{
size_t v___x_78_; size_t v___x_79_; lean_object* v___x_80_; 
v___x_78_ = ((size_t)0ULL);
v___x_79_ = lean_usize_of_nat(v___x_75_);
v___x_80_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_decls_72_, v___x_78_, v___x_79_, v_self_73_);
return v___x_80_;
}
}
else
{
size_t v___x_81_; size_t v___x_82_; lean_object* v___x_83_; 
v___x_81_ = ((size_t)0ULL);
v___x_82_ = lean_usize_of_nat(v___x_75_);
v___x_83_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_decls_72_, v___x_81_, v___x_82_, v_self_73_);
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls___boxed(lean_object* v_decls_84_, lean_object* v_self_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(v_decls_84_, v_self_85_);
lean_dec_ref(v_decls_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(lean_object* v_k_87_, lean_object* v_v_88_, lean_object* v_t_89_){
_start:
{
if (lean_obj_tag(v_t_89_) == 0)
{
lean_object* v_size_90_; lean_object* v_k_91_; lean_object* v_v_92_; lean_object* v_l_93_; lean_object* v_r_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_374_; 
v_size_90_ = lean_ctor_get(v_t_89_, 0);
v_k_91_ = lean_ctor_get(v_t_89_, 1);
v_v_92_ = lean_ctor_get(v_t_89_, 2);
v_l_93_ = lean_ctor_get(v_t_89_, 3);
v_r_94_ = lean_ctor_get(v_t_89_, 4);
v_isSharedCheck_374_ = !lean_is_exclusive(v_t_89_);
if (v_isSharedCheck_374_ == 0)
{
v___x_96_ = v_t_89_;
v_isShared_97_ = v_isSharedCheck_374_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_r_94_);
lean_inc(v_l_93_);
lean_inc(v_v_92_);
lean_inc(v_k_91_);
lean_inc(v_size_90_);
lean_dec(v_t_89_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_374_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
uint8_t v___x_98_; 
v___x_98_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_87_, v_k_91_);
switch(v___x_98_)
{
case 0:
{
lean_object* v_impl_99_; lean_object* v___x_100_; 
lean_dec(v_size_90_);
v_impl_99_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_87_, v_v_88_, v_l_93_);
v___x_100_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_94_) == 0)
{
lean_object* v_size_101_; lean_object* v_size_102_; lean_object* v_k_103_; lean_object* v_v_104_; lean_object* v_l_105_; lean_object* v_r_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_size_101_ = lean_ctor_get(v_r_94_, 0);
v_size_102_ = lean_ctor_get(v_impl_99_, 0);
v_k_103_ = lean_ctor_get(v_impl_99_, 1);
v_v_104_ = lean_ctor_get(v_impl_99_, 2);
v_l_105_ = lean_ctor_get(v_impl_99_, 3);
v_r_106_ = lean_ctor_get(v_impl_99_, 4);
lean_inc(v_r_106_);
v___x_107_ = lean_unsigned_to_nat(3u);
v___x_108_ = lean_nat_mul(v___x_107_, v_size_101_);
v___x_109_ = lean_nat_dec_lt(v___x_108_, v_size_102_);
lean_dec(v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
lean_dec(v_r_106_);
v___x_110_ = lean_nat_add(v___x_100_, v_size_102_);
v___x_111_ = lean_nat_add(v___x_110_, v_size_101_);
lean_dec(v___x_110_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 3, v_impl_99_);
lean_ctor_set(v___x_96_, 0, v___x_111_);
v___x_113_ = v___x_96_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_114_, 3, v_impl_99_);
lean_ctor_set(v_reuseFailAlloc_114_, 4, v_r_94_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
else
{
lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_180_; 
lean_inc(v_l_105_);
lean_inc(v_v_104_);
lean_inc(v_k_103_);
lean_inc(v_size_102_);
v_isSharedCheck_180_ = !lean_is_exclusive(v_impl_99_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; lean_object* v_unused_184_; lean_object* v_unused_185_; 
v_unused_181_ = lean_ctor_get(v_impl_99_, 4);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_impl_99_, 3);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_impl_99_, 2);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_impl_99_, 1);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_impl_99_, 0);
lean_dec(v_unused_185_);
v___x_116_ = v_impl_99_;
v_isShared_117_ = v_isSharedCheck_180_;
goto v_resetjp_115_;
}
else
{
lean_dec(v_impl_99_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_180_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_size_118_; lean_object* v_size_119_; lean_object* v_k_120_; lean_object* v_v_121_; lean_object* v_l_122_; lean_object* v_r_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_size_118_ = lean_ctor_get(v_l_105_, 0);
v_size_119_ = lean_ctor_get(v_r_106_, 0);
v_k_120_ = lean_ctor_get(v_r_106_, 1);
v_v_121_ = lean_ctor_get(v_r_106_, 2);
v_l_122_ = lean_ctor_get(v_r_106_, 3);
v_r_123_ = lean_ctor_get(v_r_106_, 4);
v___x_124_ = lean_unsigned_to_nat(2u);
v___x_125_ = lean_nat_mul(v___x_124_, v_size_118_);
v___x_126_ = lean_nat_dec_lt(v_size_119_, v___x_125_);
lean_dec(v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_155_; 
lean_inc(v_r_123_);
lean_inc(v_l_122_);
lean_inc(v_v_121_);
lean_inc(v_k_120_);
v_isSharedCheck_155_ = !lean_is_exclusive(v_r_106_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; lean_object* v_unused_159_; lean_object* v_unused_160_; 
v_unused_156_ = lean_ctor_get(v_r_106_, 4);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_r_106_, 3);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_r_106_, 2);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_r_106_, 1);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_r_106_, 0);
lean_dec(v_unused_160_);
v___x_128_ = v_r_106_;
v_isShared_129_ = v_isSharedCheck_155_;
goto v_resetjp_127_;
}
else
{
lean_dec(v_r_106_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_155_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___x_143_; lean_object* v___y_145_; 
v___x_130_ = lean_nat_add(v___x_100_, v_size_102_);
lean_dec(v_size_102_);
v___x_131_ = lean_nat_add(v___x_130_, v_size_101_);
lean_dec(v___x_130_);
v___x_143_ = lean_nat_add(v___x_100_, v_size_118_);
if (lean_obj_tag(v_l_122_) == 0)
{
lean_object* v_size_153_; 
v_size_153_ = lean_ctor_get(v_l_122_, 0);
lean_inc(v_size_153_);
v___y_145_ = v_size_153_;
goto v___jp_144_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v___y_145_ = v___x_154_;
goto v___jp_144_;
}
v___jp_132_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_nat_add(v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec(v___y_134_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 4, v_r_94_);
lean_ctor_set(v___x_128_, 3, v_r_123_);
lean_ctor_set(v___x_128_, 2, v_v_92_);
lean_ctor_set(v___x_128_, 1, v_k_91_);
lean_ctor_set(v___x_128_, 0, v___x_136_);
v___x_138_ = v___x_128_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_r_123_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v_r_94_);
v___x_138_ = v_reuseFailAlloc_142_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 4, v___x_138_);
lean_ctor_set(v___x_116_, 3, v___y_133_);
lean_ctor_set(v___x_116_, 2, v_v_121_);
lean_ctor_set(v___x_116_, 1, v_k_120_);
lean_ctor_set(v___x_116_, 0, v___x_131_);
v___x_140_ = v___x_116_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v___y_133_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_nat_add(v___x_143_, v___y_145_);
lean_dec(v___y_145_);
lean_dec(v___x_143_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_l_122_);
lean_ctor_set(v___x_96_, 3, v_l_105_);
lean_ctor_set(v___x_96_, 2, v_v_104_);
lean_ctor_set(v___x_96_, 1, v_k_103_);
lean_ctor_set(v___x_96_, 0, v___x_146_);
v___x_148_ = v___x_96_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_k_103_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_v_104_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_l_105_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v_l_122_);
v___x_148_ = v_reuseFailAlloc_152_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = lean_nat_add(v___x_100_, v_size_101_);
if (lean_obj_tag(v_r_123_) == 0)
{
lean_object* v_size_150_; 
v_size_150_ = lean_ctor_get(v_r_123_, 0);
lean_inc(v_size_150_);
v___y_133_ = v___x_148_;
v___y_134_ = v___x_149_;
v___y_135_ = v_size_150_;
goto v___jp_132_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___y_133_ = v___x_148_;
v___y_134_ = v___x_149_;
v___y_135_ = v___x_151_;
goto v___jp_132_;
}
}
}
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
lean_del_object(v___x_96_);
v___x_161_ = lean_nat_add(v___x_100_, v_size_102_);
lean_dec(v_size_102_);
v___x_162_ = lean_nat_add(v___x_161_, v_size_101_);
lean_dec(v___x_161_);
v___x_163_ = lean_nat_add(v___x_100_, v_size_101_);
v___x_164_ = lean_nat_add(v___x_163_, v_size_119_);
lean_dec(v___x_163_);
lean_inc_ref(v_r_94_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 4, v_r_94_);
lean_ctor_set(v___x_116_, 3, v_r_106_);
lean_ctor_set(v___x_116_, 2, v_v_92_);
lean_ctor_set(v___x_116_, 1, v_k_91_);
lean_ctor_set(v___x_116_, 0, v___x_164_);
v___x_166_ = v___x_116_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_r_106_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v_r_94_);
v___x_166_ = v_reuseFailAlloc_179_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_isSharedCheck_173_ = !lean_is_exclusive(v_r_94_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; lean_object* v_unused_175_; lean_object* v_unused_176_; lean_object* v_unused_177_; lean_object* v_unused_178_; 
v_unused_174_ = lean_ctor_get(v_r_94_, 4);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_r_94_, 3);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_r_94_, 2);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_r_94_, 1);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_r_94_, 0);
lean_dec(v_unused_178_);
v___x_168_ = v_r_94_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_dec(v_r_94_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 4, v___x_166_);
lean_ctor_set(v___x_168_, 3, v_l_105_);
lean_ctor_set(v___x_168_, 2, v_v_104_);
lean_ctor_set(v___x_168_, 1, v_k_103_);
lean_ctor_set(v___x_168_, 0, v___x_162_);
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_k_103_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_v_104_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_l_105_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v___x_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_186_; 
v_l_186_ = lean_ctor_get(v_impl_99_, 3);
if (lean_obj_tag(v_l_186_) == 0)
{
lean_object* v_r_187_; lean_object* v_k_188_; lean_object* v_v_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_200_; 
lean_inc_ref(v_l_186_);
v_r_187_ = lean_ctor_get(v_impl_99_, 4);
v_k_188_ = lean_ctor_get(v_impl_99_, 1);
v_v_189_ = lean_ctor_get(v_impl_99_, 2);
v_isSharedCheck_200_ = !lean_is_exclusive(v_impl_99_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; lean_object* v_unused_202_; 
v_unused_201_ = lean_ctor_get(v_impl_99_, 3);
lean_dec(v_unused_201_);
v_unused_202_ = lean_ctor_get(v_impl_99_, 0);
lean_dec(v_unused_202_);
v___x_191_ = v_impl_99_;
v_isShared_192_ = v_isSharedCheck_200_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_r_187_);
lean_inc(v_v_189_);
lean_inc(v_k_188_);
lean_dec(v_impl_99_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_200_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 3, v_r_187_);
lean_ctor_set(v___x_191_, 2, v_v_92_);
lean_ctor_set(v___x_191_, 1, v_k_91_);
lean_ctor_set(v___x_191_, 0, v___x_100_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_r_187_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v_r_187_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v___x_195_);
lean_ctor_set(v___x_96_, 3, v_l_186_);
lean_ctor_set(v___x_96_, 2, v_v_189_);
lean_ctor_set(v___x_96_, 1, v_k_188_);
lean_ctor_set(v___x_96_, 0, v___x_193_);
v___x_197_ = v___x_96_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_k_188_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_v_189_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v_l_186_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_r_203_; 
v_r_203_ = lean_ctor_get(v_impl_99_, 4);
lean_inc(v_r_203_);
if (lean_obj_tag(v_r_203_) == 0)
{
lean_object* v_k_204_; lean_object* v_v_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_228_; 
lean_inc(v_l_186_);
v_k_204_ = lean_ctor_get(v_impl_99_, 1);
v_v_205_ = lean_ctor_get(v_impl_99_, 2);
v_isSharedCheck_228_ = !lean_is_exclusive(v_impl_99_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_229_ = lean_ctor_get(v_impl_99_, 4);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_impl_99_, 3);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_impl_99_, 0);
lean_dec(v_unused_231_);
v___x_207_ = v_impl_99_;
v_isShared_208_ = v_isSharedCheck_228_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_v_205_);
lean_inc(v_k_204_);
lean_dec(v_impl_99_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_228_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_k_209_; lean_object* v_v_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_224_; 
v_k_209_ = lean_ctor_get(v_r_203_, 1);
v_v_210_ = lean_ctor_get(v_r_203_, 2);
v_isSharedCheck_224_ = !lean_is_exclusive(v_r_203_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; lean_object* v_unused_226_; lean_object* v_unused_227_; 
v_unused_225_ = lean_ctor_get(v_r_203_, 4);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_r_203_, 3);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_r_203_, 0);
lean_dec(v_unused_227_);
v___x_212_ = v_r_203_;
v_isShared_213_ = v_isSharedCheck_224_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_v_210_);
lean_inc(v_k_209_);
lean_dec(v_r_203_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_224_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(3u);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 4, v_l_186_);
lean_ctor_set(v___x_212_, 3, v_l_186_);
lean_ctor_set(v___x_212_, 2, v_v_205_);
lean_ctor_set(v___x_212_, 1, v_k_204_);
lean_ctor_set(v___x_212_, 0, v___x_100_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_k_204_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_v_205_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v_l_186_);
lean_ctor_set(v_reuseFailAlloc_223_, 4, v_l_186_);
v___x_216_ = v_reuseFailAlloc_223_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_218_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 4, v_l_186_);
lean_ctor_set(v___x_207_, 2, v_v_92_);
lean_ctor_set(v___x_207_, 1, v_k_91_);
lean_ctor_set(v___x_207_, 0, v___x_100_);
v___x_218_ = v___x_207_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_222_, 3, v_l_186_);
lean_ctor_set(v_reuseFailAlloc_222_, 4, v_l_186_);
v___x_218_ = v_reuseFailAlloc_222_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v___x_218_);
lean_ctor_set(v___x_96_, 3, v___x_216_);
lean_ctor_set(v___x_96_, 2, v_v_210_);
lean_ctor_set(v___x_96_, 1, v_k_209_);
lean_ctor_set(v___x_96_, 0, v___x_214_);
v___x_220_ = v___x_96_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_k_209_);
lean_ctor_set(v_reuseFailAlloc_221_, 2, v_v_210_);
lean_ctor_set(v_reuseFailAlloc_221_, 3, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_221_, 4, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_unsigned_to_nat(2u);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_r_203_);
lean_ctor_set(v___x_96_, 3, v_impl_99_);
lean_ctor_set(v___x_96_, 0, v___x_232_);
v___x_234_ = v___x_96_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_impl_99_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_r_203_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
case 1:
{
lean_object* v___x_237_; 
lean_dec(v_v_92_);
lean_dec(v_k_91_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 2, v_v_88_);
lean_ctor_set(v___x_96_, 1, v_k_87_);
v___x_237_ = v___x_96_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_size_90_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_l_93_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_r_94_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
default: 
{
lean_object* v_impl_239_; lean_object* v___x_240_; 
lean_dec(v_size_90_);
v_impl_239_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_87_, v_v_88_, v_r_94_);
v___x_240_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_93_) == 0)
{
lean_object* v_size_241_; lean_object* v_size_242_; lean_object* v_k_243_; lean_object* v_v_244_; lean_object* v_l_245_; lean_object* v_r_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_size_241_ = lean_ctor_get(v_l_93_, 0);
v_size_242_ = lean_ctor_get(v_impl_239_, 0);
v_k_243_ = lean_ctor_get(v_impl_239_, 1);
v_v_244_ = lean_ctor_get(v_impl_239_, 2);
v_l_245_ = lean_ctor_get(v_impl_239_, 3);
lean_inc(v_l_245_);
v_r_246_ = lean_ctor_get(v_impl_239_, 4);
v___x_247_ = lean_unsigned_to_nat(3u);
v___x_248_ = lean_nat_mul(v___x_247_, v_size_241_);
v___x_249_ = lean_nat_dec_lt(v___x_248_, v_size_242_);
lean_dec(v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec(v_l_245_);
v___x_250_ = lean_nat_add(v___x_240_, v_size_241_);
v___x_251_ = lean_nat_add(v___x_250_, v_size_242_);
lean_dec(v___x_250_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_impl_239_);
lean_ctor_set(v___x_96_, 0, v___x_251_);
v___x_253_ = v___x_96_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v_l_93_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v_impl_239_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
else
{
lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_318_; 
lean_inc(v_r_246_);
lean_inc(v_v_244_);
lean_inc(v_k_243_);
lean_inc(v_size_242_);
v_isSharedCheck_318_ = !lean_is_exclusive(v_impl_239_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; 
v_unused_319_ = lean_ctor_get(v_impl_239_, 4);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_impl_239_, 3);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_impl_239_, 2);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_impl_239_, 1);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_impl_239_, 0);
lean_dec(v_unused_323_);
v___x_256_ = v_impl_239_;
v_isShared_257_ = v_isSharedCheck_318_;
goto v_resetjp_255_;
}
else
{
lean_dec(v_impl_239_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_318_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v_size_258_; lean_object* v_k_259_; lean_object* v_v_260_; lean_object* v_l_261_; lean_object* v_r_262_; lean_object* v_size_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_size_258_ = lean_ctor_get(v_l_245_, 0);
v_k_259_ = lean_ctor_get(v_l_245_, 1);
v_v_260_ = lean_ctor_get(v_l_245_, 2);
v_l_261_ = lean_ctor_get(v_l_245_, 3);
v_r_262_ = lean_ctor_get(v_l_245_, 4);
v_size_263_ = lean_ctor_get(v_r_246_, 0);
v___x_264_ = lean_unsigned_to_nat(2u);
v___x_265_ = lean_nat_mul(v___x_264_, v_size_263_);
v___x_266_ = lean_nat_dec_lt(v_size_258_, v___x_265_);
lean_dec(v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_294_; 
lean_inc(v_r_262_);
lean_inc(v_l_261_);
lean_inc(v_v_260_);
lean_inc(v_k_259_);
v_isSharedCheck_294_ = !lean_is_exclusive(v_l_245_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_295_ = lean_ctor_get(v_l_245_, 4);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_l_245_, 3);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_l_245_, 2);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_l_245_, 1);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_l_245_, 0);
lean_dec(v_unused_299_);
v___x_268_ = v_l_245_;
v_isShared_269_ = v_isSharedCheck_294_;
goto v_resetjp_267_;
}
else
{
lean_dec(v_l_245_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_294_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_284_; 
v___x_270_ = lean_nat_add(v___x_240_, v_size_241_);
v___x_271_ = lean_nat_add(v___x_270_, v_size_242_);
lean_dec(v_size_242_);
if (lean_obj_tag(v_l_261_) == 0)
{
lean_object* v_size_292_; 
v_size_292_ = lean_ctor_get(v_l_261_, 0);
lean_inc(v_size_292_);
v___y_284_ = v_size_292_;
goto v___jp_283_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___y_284_ = v___x_293_;
goto v___jp_283_;
}
v___jp_272_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = lean_nat_add(v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec(v___y_274_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 4, v_r_246_);
lean_ctor_set(v___x_268_, 3, v_r_262_);
lean_ctor_set(v___x_268_, 2, v_v_244_);
lean_ctor_set(v___x_268_, 1, v_k_243_);
lean_ctor_set(v___x_268_, 0, v___x_276_);
v___x_278_ = v___x_268_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_k_243_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_v_244_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_r_262_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_r_246_);
v___x_278_ = v_reuseFailAlloc_282_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 4, v___x_278_);
lean_ctor_set(v___x_256_, 3, v___y_273_);
lean_ctor_set(v___x_256_, 2, v_v_260_);
lean_ctor_set(v___x_256_, 1, v_k_259_);
lean_ctor_set(v___x_256_, 0, v___x_271_);
v___x_280_ = v___x_256_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_k_259_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_v_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v___y_273_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
v___jp_283_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_nat_add(v___x_270_, v___y_284_);
lean_dec(v___y_284_);
lean_dec(v___x_270_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_l_261_);
lean_ctor_set(v___x_96_, 0, v___x_285_);
v___x_287_ = v___x_96_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_l_93_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_l_261_);
v___x_287_ = v_reuseFailAlloc_291_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; 
v___x_288_ = lean_nat_add(v___x_240_, v_size_263_);
if (lean_obj_tag(v_r_262_) == 0)
{
lean_object* v_size_289_; 
v_size_289_ = lean_ctor_get(v_r_262_, 0);
lean_inc(v_size_289_);
v___y_273_ = v___x_287_;
v___y_274_ = v___x_288_;
v___y_275_ = v_size_289_;
goto v___jp_272_;
}
else
{
lean_object* v___x_290_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___y_273_ = v___x_287_;
v___y_274_ = v___x_288_;
v___y_275_ = v___x_290_;
goto v___jp_272_;
}
}
}
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
lean_del_object(v___x_96_);
v___x_300_ = lean_nat_add(v___x_240_, v_size_241_);
v___x_301_ = lean_nat_add(v___x_300_, v_size_242_);
lean_dec(v_size_242_);
v___x_302_ = lean_nat_add(v___x_300_, v_size_258_);
lean_dec(v___x_300_);
lean_inc_ref(v_l_93_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 4, v_l_245_);
lean_ctor_set(v___x_256_, 3, v_l_93_);
lean_ctor_set(v___x_256_, 2, v_v_92_);
lean_ctor_set(v___x_256_, 1, v_k_91_);
lean_ctor_set(v___x_256_, 0, v___x_302_);
v___x_304_ = v___x_256_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_l_93_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v_l_245_);
v___x_304_ = v_reuseFailAlloc_317_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
v_isSharedCheck_311_ = !lean_is_exclusive(v_l_93_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_312_ = lean_ctor_get(v_l_93_, 4);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_l_93_, 3);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_l_93_, 2);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_l_93_, 1);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_l_93_, 0);
lean_dec(v_unused_316_);
v___x_306_ = v_l_93_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_dec(v_l_93_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 4, v_r_246_);
lean_ctor_set(v___x_306_, 3, v___x_304_);
lean_ctor_set(v___x_306_, 2, v_v_244_);
lean_ctor_set(v___x_306_, 1, v_k_243_);
lean_ctor_set(v___x_306_, 0, v___x_301_);
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_k_243_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_v_244_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_310_, 4, v_r_246_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_324_; 
v_l_324_ = lean_ctor_get(v_impl_239_, 3);
lean_inc(v_l_324_);
if (lean_obj_tag(v_l_324_) == 0)
{
lean_object* v_r_325_; lean_object* v_k_326_; lean_object* v_v_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_350_; 
v_r_325_ = lean_ctor_get(v_impl_239_, 4);
v_k_326_ = lean_ctor_get(v_impl_239_, 1);
v_v_327_ = lean_ctor_get(v_impl_239_, 2);
v_isSharedCheck_350_ = !lean_is_exclusive(v_impl_239_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_351_ = lean_ctor_get(v_impl_239_, 3);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_impl_239_, 0);
lean_dec(v_unused_352_);
v___x_329_ = v_impl_239_;
v_isShared_330_ = v_isSharedCheck_350_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_r_325_);
lean_inc(v_v_327_);
lean_inc(v_k_326_);
lean_dec(v_impl_239_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_350_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_k_331_; lean_object* v_v_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_346_; 
v_k_331_ = lean_ctor_get(v_l_324_, 1);
v_v_332_ = lean_ctor_get(v_l_324_, 2);
v_isSharedCheck_346_ = !lean_is_exclusive(v_l_324_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; lean_object* v_unused_348_; lean_object* v_unused_349_; 
v_unused_347_ = lean_ctor_get(v_l_324_, 4);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_l_324_, 3);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_l_324_, 0);
lean_dec(v_unused_349_);
v___x_334_ = v_l_324_;
v_isShared_335_ = v_isSharedCheck_346_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_v_332_);
lean_inc(v_k_331_);
lean_dec(v_l_324_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_346_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_325_, 2);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 4, v_r_325_);
lean_ctor_set(v___x_334_, 3, v_r_325_);
lean_ctor_set(v___x_334_, 2, v_v_92_);
lean_ctor_set(v___x_334_, 1, v_k_91_);
lean_ctor_set(v___x_334_, 0, v___x_240_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v_r_325_);
lean_ctor_set(v_reuseFailAlloc_345_, 4, v_r_325_);
v___x_338_ = v_reuseFailAlloc_345_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
lean_inc(v_r_325_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 3, v_r_325_);
lean_ctor_set(v___x_329_, 0, v___x_240_);
v___x_340_ = v___x_329_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_r_325_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v_r_325_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v___x_340_);
lean_ctor_set(v___x_96_, 3, v___x_338_);
lean_ctor_set(v___x_96_, 2, v_v_332_);
lean_ctor_set(v___x_96_, 1, v_k_331_);
lean_ctor_set(v___x_96_, 0, v___x_336_);
v___x_342_ = v___x_96_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_k_331_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_v_332_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
else
{
lean_object* v_r_353_; 
v_r_353_ = lean_ctor_get(v_impl_239_, 4);
lean_inc(v_r_353_);
if (lean_obj_tag(v_r_353_) == 0)
{
lean_object* v_k_354_; lean_object* v_v_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_366_; 
v_k_354_ = lean_ctor_get(v_impl_239_, 1);
v_v_355_ = lean_ctor_get(v_impl_239_, 2);
v_isSharedCheck_366_ = !lean_is_exclusive(v_impl_239_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; lean_object* v_unused_368_; lean_object* v_unused_369_; 
v_unused_367_ = lean_ctor_get(v_impl_239_, 4);
lean_dec(v_unused_367_);
v_unused_368_ = lean_ctor_get(v_impl_239_, 3);
lean_dec(v_unused_368_);
v_unused_369_ = lean_ctor_get(v_impl_239_, 0);
lean_dec(v_unused_369_);
v___x_357_ = v_impl_239_;
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_v_355_);
lean_inc(v_k_354_);
lean_dec(v_impl_239_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_unsigned_to_nat(3u);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 4, v_l_324_);
lean_ctor_set(v___x_357_, 2, v_v_92_);
lean_ctor_set(v___x_357_, 1, v_k_91_);
lean_ctor_set(v___x_357_, 0, v___x_240_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_l_324_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_l_324_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_r_353_);
lean_ctor_set(v___x_96_, 3, v___x_361_);
lean_ctor_set(v___x_96_, 2, v_v_355_);
lean_ctor_set(v___x_96_, 1, v_k_354_);
lean_ctor_set(v___x_96_, 0, v___x_359_);
v___x_363_ = v___x_96_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_k_354_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_v_355_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v_r_353_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_unsigned_to_nat(2u);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v_impl_239_);
lean_ctor_set(v___x_96_, 3, v_r_353_);
lean_ctor_set(v___x_96_, 0, v___x_370_);
v___x_372_ = v___x_96_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_r_353_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_impl_239_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_k_87_);
lean_ctor_set(v___x_376_, 2, v_v_88_);
lean_ctor_set(v___x_376_, 3, v_t_89_);
lean_ctor_set(v___x_376_, 4, v_t_89_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(lean_object* v_ws_377_, lean_object* v_dep_378_, lean_object* v_lakeOpts_379_, lean_object* v_leanOpts_380_, uint8_t v_reconfigure_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_lakeEnv_384_; lean_object* v_lakeConfig_385_; lean_object* v_lakeCache_386_; lean_object* v_lakeArgs_x3f_387_; lean_object* v_packages_388_; lean_object* v_packageMap_389_; lean_object* v_facetConfigs_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_457_; 
v_lakeEnv_384_ = lean_ctor_get(v_ws_377_, 0);
v_lakeConfig_385_ = lean_ctor_get(v_ws_377_, 1);
v_lakeCache_386_ = lean_ctor_get(v_ws_377_, 2);
v_lakeArgs_x3f_387_ = lean_ctor_get(v_ws_377_, 3);
v_packages_388_ = lean_ctor_get(v_ws_377_, 4);
v_packageMap_389_ = lean_ctor_get(v_ws_377_, 5);
v_facetConfigs_390_ = lean_ctor_get(v_ws_377_, 6);
v_isSharedCheck_457_ = !lean_is_exclusive(v_ws_377_);
if (v_isSharedCheck_457_ == 0)
{
v___x_392_ = v_ws_377_;
v_isShared_393_ = v_isSharedCheck_457_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_facetConfigs_390_);
lean_inc(v_packageMap_389_);
lean_inc(v_packages_388_);
lean_inc(v_lakeArgs_x3f_387_);
lean_inc(v_lakeCache_386_);
lean_inc(v_lakeConfig_385_);
lean_inc(v_lakeEnv_384_);
lean_dec(v_ws_377_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_457_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_manifestEntry_396_; lean_object* v_dir_397_; lean_object* v_pkgDir_398_; lean_object* v_relPkgDir_399_; lean_object* v_remoteUrl_400_; lean_object* v_name_401_; lean_object* v_scope_402_; lean_object* v_configFile_403_; lean_object* v_manifestFile_x3f_404_; lean_object* v_wsIdx_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___y_409_; 
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_array_fget_borrowed(v_packages_388_, v___x_394_);
v_manifestEntry_396_ = lean_ctor_get(v_dep_378_, 4);
lean_inc_ref(v_manifestEntry_396_);
v_dir_397_ = lean_ctor_get(v___x_395_, 4);
v_pkgDir_398_ = lean_ctor_get(v_dep_378_, 0);
lean_inc_ref_n(v_pkgDir_398_, 2);
v_relPkgDir_399_ = lean_ctor_get(v_dep_378_, 1);
lean_inc_ref(v_relPkgDir_399_);
v_remoteUrl_400_ = lean_ctor_get(v_dep_378_, 2);
lean_inc_ref(v_remoteUrl_400_);
lean_dec_ref(v_dep_378_);
v_name_401_ = lean_ctor_get(v_manifestEntry_396_, 0);
lean_inc(v_name_401_);
v_scope_402_ = lean_ctor_get(v_manifestEntry_396_, 1);
lean_inc_ref(v_scope_402_);
v_configFile_403_ = lean_ctor_get(v_manifestEntry_396_, 2);
lean_inc_ref_n(v_configFile_403_, 2);
v_manifestFile_x3f_404_ = lean_ctor_get(v_manifestEntry_396_, 3);
lean_inc(v_manifestFile_x3f_404_);
lean_dec_ref(v_manifestEntry_396_);
v_wsIdx_405_ = lean_array_get_size(v_packages_388_);
v___x_406_ = lean_box(0);
v___x_407_ = l_Lake_joinRelative(v_pkgDir_398_, v_configFile_403_);
if (lean_obj_tag(v_manifestFile_x3f_404_) == 0)
{
lean_object* v___x_455_; 
v___x_455_ = l_Lake_defaultManifestFile;
v___y_409_ = v___x_455_;
goto v___jp_408_;
}
else
{
lean_object* v_val_456_; 
v_val_456_ = lean_ctor_get(v_manifestFile_x3f_404_, 0);
lean_inc(v_val_456_);
lean_dec_ref_known(v_manifestFile_x3f_404_, 1);
v___y_409_ = v_val_456_;
goto v___jp_408_;
}
v___jp_408_:
{
lean_object* v___x_410_; uint8_t v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_410_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_411_ = 0;
v___x_412_ = 1;
lean_inc(v_name_401_);
lean_inc_ref(v_dir_397_);
lean_inc_ref(v_lakeEnv_384_);
v___x_413_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_413_, 0, v_lakeEnv_384_);
lean_ctor_set(v___x_413_, 1, v___x_406_);
lean_ctor_set(v___x_413_, 2, v_dir_397_);
lean_ctor_set(v___x_413_, 3, v_wsIdx_405_);
lean_ctor_set(v___x_413_, 4, v_name_401_);
lean_ctor_set(v___x_413_, 5, v_relPkgDir_399_);
lean_ctor_set(v___x_413_, 6, v_pkgDir_398_);
lean_ctor_set(v___x_413_, 7, v_configFile_403_);
lean_ctor_set(v___x_413_, 8, v___x_407_);
lean_ctor_set(v___x_413_, 9, v___x_406_);
lean_ctor_set(v___x_413_, 10, v___y_409_);
lean_ctor_set(v___x_413_, 11, v___x_410_);
lean_ctor_set(v___x_413_, 12, v_lakeOpts_379_);
lean_ctor_set(v___x_413_, 13, v_leanOpts_380_);
lean_ctor_set(v___x_413_, 14, v_scope_402_);
lean_ctor_set(v___x_413_, 15, v_remoteUrl_400_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*16, v_reconfigure_381_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*16 + 1, v___x_411_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*16 + 2, v___x_412_);
v___x_414_ = l_Lean_Name_toString(v_name_401_, v___x_411_);
v___x_415_ = l_Lake_resolveConfigFile(v___x_414_, v___x_413_, v_a_382_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v_a_417_; lean_object* v___x_418_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_n(v_a_416_, 2);
v_a_417_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_415_, 2);
v___x_418_ = l_Lake_loadConfigFile___redArg(v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_436_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_a_420_ = lean_ctor_get(v___x_418_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_436_ == 0)
{
v___x_422_ = v___x_418_;
v_isShared_423_ = v_isSharedCheck_436_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_436_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_facetDecls_424_; lean_object* v___x_425_; lean_object* v_keyName_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v_facetDecls_424_ = lean_ctor_get(v_a_419_, 2);
lean_inc_ref(v_facetDecls_424_);
v___x_425_ = l_Lake_mkPackage(v_a_416_, v_a_419_, v_wsIdx_405_);
lean_dec(v_a_416_);
v_keyName_426_ = lean_ctor_get(v___x_425_, 2);
lean_inc(v_keyName_426_);
lean_inc_ref(v___x_425_);
v___x_427_ = lean_array_push(v_packages_388_, v___x_425_);
v___x_428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_426_, v___x_425_, v_packageMap_389_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 5, v___x_428_);
lean_ctor_set(v___x_392_, 4, v___x_427_);
v___x_430_ = v___x_392_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_lakeEnv_384_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_lakeConfig_385_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_lakeCache_386_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_lakeArgs_x3f_387_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_facetConfigs_390_);
v___x_430_ = v_reuseFailAlloc_435_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(v_facetDecls_424_, v___x_430_);
lean_dec_ref(v_facetDecls_424_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_431_);
v___x_433_ = v___x_422_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_a_420_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_object* v_a_437_; lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec(v_a_416_);
lean_del_object(v___x_392_);
lean_dec(v_facetConfigs_390_);
lean_dec(v_packageMap_389_);
lean_dec_ref(v_packages_388_);
lean_dec(v_lakeArgs_x3f_387_);
lean_dec_ref(v_lakeCache_386_);
lean_dec_ref(v_lakeConfig_385_);
lean_dec_ref(v_lakeEnv_384_);
v_a_437_ = lean_ctor_get(v___x_418_, 0);
v_a_438_ = lean_ctor_get(v___x_418_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_418_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_inc(v_a_437_);
lean_dec(v___x_418_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_437_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_del_object(v___x_392_);
lean_dec(v_facetConfigs_390_);
lean_dec(v_packageMap_389_);
lean_dec_ref(v_packages_388_);
lean_dec(v_lakeArgs_x3f_387_);
lean_dec_ref(v_lakeCache_386_);
lean_dec_ref(v_lakeConfig_385_);
lean_dec_ref(v_lakeEnv_384_);
v_a_446_ = lean_ctor_get(v___x_415_, 0);
v_a_447_ = lean_ctor_get(v___x_415_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_415_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_inc(v_a_446_);
lean_dec(v___x_415_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_446_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27___boxed(lean_object* v_ws_458_, lean_object* v_dep_459_, lean_object* v_lakeOpts_460_, lean_object* v_leanOpts_461_, lean_object* v_reconfigure_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
uint8_t v_reconfigure_boxed_465_; lean_object* v_res_466_; 
v_reconfigure_boxed_465_ = lean_unbox(v_reconfigure_462_);
v_res_466_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_458_, v_dep_459_, v_lakeOpts_460_, v_leanOpts_461_, v_reconfigure_boxed_465_, v_a_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0(lean_object* v_00_u03b2_467_, lean_object* v_k_468_, lean_object* v_v_469_, lean_object* v_t_470_, lean_object* v_hl_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_468_, v_v_469_, v_t_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(lean_object* v_self_473_, lean_object* v_pkg_474_, lean_object* v_depIdxs_475_){
_start:
{
lean_object* v_wsIdx_476_; lean_object* v_baseName_477_; lean_object* v_keyName_478_; lean_object* v_origName_479_; lean_object* v_dir_480_; lean_object* v_relDir_481_; lean_object* v_config_482_; lean_object* v_configFile_483_; lean_object* v_relConfigFile_484_; lean_object* v_relManifestFile_485_; lean_object* v_scope_486_; lean_object* v_remoteUrl_487_; lean_object* v_depConfigs_488_; lean_object* v_depPkgs_489_; lean_object* v_targetDecls_490_; lean_object* v_targetDeclMap_491_; lean_object* v_defaultTargets_492_; lean_object* v_scripts_493_; lean_object* v_defaultScripts_494_; lean_object* v_postUpdateHooks_495_; lean_object* v_buildArchive_496_; lean_object* v_testDriver_497_; lean_object* v_lintDriver_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_521_; 
v_wsIdx_476_ = lean_ctor_get(v_pkg_474_, 0);
v_baseName_477_ = lean_ctor_get(v_pkg_474_, 1);
v_keyName_478_ = lean_ctor_get(v_pkg_474_, 2);
v_origName_479_ = lean_ctor_get(v_pkg_474_, 3);
v_dir_480_ = lean_ctor_get(v_pkg_474_, 4);
v_relDir_481_ = lean_ctor_get(v_pkg_474_, 5);
v_config_482_ = lean_ctor_get(v_pkg_474_, 6);
v_configFile_483_ = lean_ctor_get(v_pkg_474_, 7);
v_relConfigFile_484_ = lean_ctor_get(v_pkg_474_, 8);
v_relManifestFile_485_ = lean_ctor_get(v_pkg_474_, 9);
v_scope_486_ = lean_ctor_get(v_pkg_474_, 10);
v_remoteUrl_487_ = lean_ctor_get(v_pkg_474_, 11);
v_depConfigs_488_ = lean_ctor_get(v_pkg_474_, 12);
v_depPkgs_489_ = lean_ctor_get(v_pkg_474_, 14);
v_targetDecls_490_ = lean_ctor_get(v_pkg_474_, 15);
v_targetDeclMap_491_ = lean_ctor_get(v_pkg_474_, 16);
v_defaultTargets_492_ = lean_ctor_get(v_pkg_474_, 17);
v_scripts_493_ = lean_ctor_get(v_pkg_474_, 18);
v_defaultScripts_494_ = lean_ctor_get(v_pkg_474_, 19);
v_postUpdateHooks_495_ = lean_ctor_get(v_pkg_474_, 20);
v_buildArchive_496_ = lean_ctor_get(v_pkg_474_, 21);
v_testDriver_497_ = lean_ctor_get(v_pkg_474_, 22);
v_lintDriver_498_ = lean_ctor_get(v_pkg_474_, 23);
v_isSharedCheck_521_ = !lean_is_exclusive(v_pkg_474_);
if (v_isSharedCheck_521_ == 0)
{
lean_object* v_unused_522_; 
v_unused_522_ = lean_ctor_get(v_pkg_474_, 13);
lean_dec(v_unused_522_);
v___x_500_ = v_pkg_474_;
v_isShared_501_ = v_isSharedCheck_521_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_lintDriver_498_);
lean_inc(v_testDriver_497_);
lean_inc(v_buildArchive_496_);
lean_inc(v_postUpdateHooks_495_);
lean_inc(v_defaultScripts_494_);
lean_inc(v_scripts_493_);
lean_inc(v_defaultTargets_492_);
lean_inc(v_targetDeclMap_491_);
lean_inc(v_targetDecls_490_);
lean_inc(v_depPkgs_489_);
lean_inc(v_depConfigs_488_);
lean_inc(v_remoteUrl_487_);
lean_inc(v_scope_486_);
lean_inc(v_relManifestFile_485_);
lean_inc(v_relConfigFile_484_);
lean_inc(v_configFile_483_);
lean_inc(v_config_482_);
lean_inc(v_relDir_481_);
lean_inc(v_dir_480_);
lean_inc(v_origName_479_);
lean_inc(v_keyName_478_);
lean_inc(v_baseName_477_);
lean_inc(v_wsIdx_476_);
lean_dec(v_pkg_474_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_521_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_lakeEnv_502_; lean_object* v_lakeConfig_503_; lean_object* v_lakeCache_504_; lean_object* v_lakeArgs_x3f_505_; lean_object* v_packages_506_; lean_object* v_packageMap_507_; lean_object* v_facetConfigs_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_520_; 
v_lakeEnv_502_ = lean_ctor_get(v_self_473_, 0);
v_lakeConfig_503_ = lean_ctor_get(v_self_473_, 1);
v_lakeCache_504_ = lean_ctor_get(v_self_473_, 2);
v_lakeArgs_x3f_505_ = lean_ctor_get(v_self_473_, 3);
v_packages_506_ = lean_ctor_get(v_self_473_, 4);
v_packageMap_507_ = lean_ctor_get(v_self_473_, 5);
v_facetConfigs_508_ = lean_ctor_get(v_self_473_, 6);
v_isSharedCheck_520_ = !lean_is_exclusive(v_self_473_);
if (v_isSharedCheck_520_ == 0)
{
v___x_510_ = v_self_473_;
v_isShared_511_ = v_isSharedCheck_520_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_facetConfigs_508_);
lean_inc(v_packageMap_507_);
lean_inc(v_packages_506_);
lean_inc(v_lakeArgs_x3f_505_);
lean_inc(v_lakeCache_504_);
lean_inc(v_lakeConfig_503_);
lean_inc(v_lakeEnv_502_);
lean_dec(v_self_473_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_520_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_pkg_513_; 
lean_inc(v_keyName_478_);
lean_inc(v_wsIdx_476_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 13, v_depIdxs_475_);
v_pkg_513_ = v___x_500_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_wsIdx_476_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_baseName_477_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_keyName_478_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_origName_479_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_dir_480_);
lean_ctor_set(v_reuseFailAlloc_519_, 5, v_relDir_481_);
lean_ctor_set(v_reuseFailAlloc_519_, 6, v_config_482_);
lean_ctor_set(v_reuseFailAlloc_519_, 7, v_configFile_483_);
lean_ctor_set(v_reuseFailAlloc_519_, 8, v_relConfigFile_484_);
lean_ctor_set(v_reuseFailAlloc_519_, 9, v_relManifestFile_485_);
lean_ctor_set(v_reuseFailAlloc_519_, 10, v_scope_486_);
lean_ctor_set(v_reuseFailAlloc_519_, 11, v_remoteUrl_487_);
lean_ctor_set(v_reuseFailAlloc_519_, 12, v_depConfigs_488_);
lean_ctor_set(v_reuseFailAlloc_519_, 13, v_depIdxs_475_);
lean_ctor_set(v_reuseFailAlloc_519_, 14, v_depPkgs_489_);
lean_ctor_set(v_reuseFailAlloc_519_, 15, v_targetDecls_490_);
lean_ctor_set(v_reuseFailAlloc_519_, 16, v_targetDeclMap_491_);
lean_ctor_set(v_reuseFailAlloc_519_, 17, v_defaultTargets_492_);
lean_ctor_set(v_reuseFailAlloc_519_, 18, v_scripts_493_);
lean_ctor_set(v_reuseFailAlloc_519_, 19, v_defaultScripts_494_);
lean_ctor_set(v_reuseFailAlloc_519_, 20, v_postUpdateHooks_495_);
lean_ctor_set(v_reuseFailAlloc_519_, 21, v_buildArchive_496_);
lean_ctor_set(v_reuseFailAlloc_519_, 22, v_testDriver_497_);
lean_ctor_set(v_reuseFailAlloc_519_, 23, v_lintDriver_498_);
v_pkg_513_ = v_reuseFailAlloc_519_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
lean_inc_ref(v_pkg_513_);
v___x_514_ = lean_array_fset(v_packages_506_, v_wsIdx_476_, v_pkg_513_);
lean_dec(v_wsIdx_476_);
v___x_515_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_478_, v_pkg_513_, v_packageMap_507_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 5, v___x_515_);
lean_ctor_set(v___x_510_, 4, v___x_514_);
v___x_517_ = v___x_510_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_lakeEnv_502_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_lakeConfig_503_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_lakeCache_504_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_lakeArgs_x3f_505_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_518_, 5, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_518_, 6, v_facetConfigs_508_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs(lean_object* v_self_523_, lean_object* v_pkg_524_, lean_object* v_depIdxs_525_, lean_object* v_h__wsIdx_526_, lean_object* v_h__depIdxs_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_self_523_, v_pkg_524_, v_depIdxs_525_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(lean_object* v_val_529_, size_t v_sz_530_, size_t v_i_531_, lean_object* v_bs_532_){
_start:
{
uint8_t v___x_533_; 
v___x_533_ = lean_usize_dec_lt(v_i_531_, v_sz_530_);
if (v___x_533_ == 0)
{
return v_bs_532_;
}
else
{
lean_object* v_v_534_; lean_object* v___x_535_; lean_object* v_bs_x27_536_; lean_object* v___x_537_; size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v_v_534_ = lean_array_uget(v_bs_532_, v_i_531_);
v___x_535_ = lean_unsigned_to_nat(0u);
v_bs_x27_536_ = lean_array_uset(v_bs_532_, v_i_531_, v___x_535_);
v___x_537_ = lean_array_fget_borrowed(v_val_529_, v_v_534_);
lean_dec(v_v_534_);
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_add(v_i_531_, v___x_538_);
lean_inc(v___x_537_);
v___x_540_ = lean_array_uset(v_bs_x27_536_, v_i_531_, v___x_537_);
v_i_531_ = v___x_539_;
v_bs_532_ = v___x_540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0___boxed(lean_object* v_val_542_, lean_object* v_sz_543_, lean_object* v_i_544_, lean_object* v_bs_545_){
_start:
{
size_t v_sz_boxed_546_; size_t v_i_boxed_547_; lean_object* v_res_548_; 
v_sz_boxed_546_ = lean_unbox_usize(v_sz_543_);
lean_dec(v_sz_543_);
v_i_boxed_547_ = lean_unbox_usize(v_i_544_);
lean_dec(v_i_544_);
v_res_548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_val_542_, v_sz_boxed_546_, v_i_boxed_547_, v_bs_545_);
lean_dec_ref(v_val_542_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
lean_object* v_zero_551_; uint8_t v_isZero_552_; 
v_zero_551_ = lean_unsigned_to_nat(0u);
v_isZero_552_ = lean_nat_dec_eq(v_x_549_, v_zero_551_);
if (v_isZero_552_ == 1)
{
lean_dec(v_x_549_);
return v_x_550_;
}
else
{
lean_object* v_one_553_; lean_object* v_n_554_; lean_object* v_pkg_555_; lean_object* v_wsIdx_556_; lean_object* v_baseName_557_; lean_object* v_keyName_558_; lean_object* v_origName_559_; lean_object* v_dir_560_; lean_object* v_relDir_561_; lean_object* v_config_562_; lean_object* v_configFile_563_; lean_object* v_relConfigFile_564_; lean_object* v_relManifestFile_565_; lean_object* v_scope_566_; lean_object* v_remoteUrl_567_; lean_object* v_depConfigs_568_; lean_object* v_depIdxs_569_; lean_object* v_targetDecls_570_; lean_object* v_targetDeclMap_571_; lean_object* v_defaultTargets_572_; lean_object* v_scripts_573_; lean_object* v_defaultScripts_574_; lean_object* v_postUpdateHooks_575_; lean_object* v_buildArchive_576_; lean_object* v_testDriver_577_; lean_object* v_lintDriver_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_590_; 
v_one_553_ = lean_unsigned_to_nat(1u);
v_n_554_ = lean_nat_sub(v_x_549_, v_one_553_);
lean_dec(v_x_549_);
v_pkg_555_ = lean_array_fget(v_x_550_, v_n_554_);
v_wsIdx_556_ = lean_ctor_get(v_pkg_555_, 0);
v_baseName_557_ = lean_ctor_get(v_pkg_555_, 1);
v_keyName_558_ = lean_ctor_get(v_pkg_555_, 2);
v_origName_559_ = lean_ctor_get(v_pkg_555_, 3);
v_dir_560_ = lean_ctor_get(v_pkg_555_, 4);
v_relDir_561_ = lean_ctor_get(v_pkg_555_, 5);
v_config_562_ = lean_ctor_get(v_pkg_555_, 6);
v_configFile_563_ = lean_ctor_get(v_pkg_555_, 7);
v_relConfigFile_564_ = lean_ctor_get(v_pkg_555_, 8);
v_relManifestFile_565_ = lean_ctor_get(v_pkg_555_, 9);
v_scope_566_ = lean_ctor_get(v_pkg_555_, 10);
v_remoteUrl_567_ = lean_ctor_get(v_pkg_555_, 11);
v_depConfigs_568_ = lean_ctor_get(v_pkg_555_, 12);
v_depIdxs_569_ = lean_ctor_get(v_pkg_555_, 13);
v_targetDecls_570_ = lean_ctor_get(v_pkg_555_, 15);
v_targetDeclMap_571_ = lean_ctor_get(v_pkg_555_, 16);
v_defaultTargets_572_ = lean_ctor_get(v_pkg_555_, 17);
v_scripts_573_ = lean_ctor_get(v_pkg_555_, 18);
v_defaultScripts_574_ = lean_ctor_get(v_pkg_555_, 19);
v_postUpdateHooks_575_ = lean_ctor_get(v_pkg_555_, 20);
v_buildArchive_576_ = lean_ctor_get(v_pkg_555_, 21);
v_testDriver_577_ = lean_ctor_get(v_pkg_555_, 22);
v_lintDriver_578_ = lean_ctor_get(v_pkg_555_, 23);
v_isSharedCheck_590_ = !lean_is_exclusive(v_pkg_555_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_pkg_555_, 14);
lean_dec(v_unused_591_);
v___x_580_ = v_pkg_555_;
v_isShared_581_ = v_isSharedCheck_590_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_lintDriver_578_);
lean_inc(v_testDriver_577_);
lean_inc(v_buildArchive_576_);
lean_inc(v_postUpdateHooks_575_);
lean_inc(v_defaultScripts_574_);
lean_inc(v_scripts_573_);
lean_inc(v_defaultTargets_572_);
lean_inc(v_targetDeclMap_571_);
lean_inc(v_targetDecls_570_);
lean_inc(v_depIdxs_569_);
lean_inc(v_depConfigs_568_);
lean_inc(v_remoteUrl_567_);
lean_inc(v_scope_566_);
lean_inc(v_relManifestFile_565_);
lean_inc(v_relConfigFile_564_);
lean_inc(v_configFile_563_);
lean_inc(v_config_562_);
lean_inc(v_relDir_561_);
lean_inc(v_dir_560_);
lean_inc(v_origName_559_);
lean_inc(v_keyName_558_);
lean_inc(v_baseName_557_);
lean_inc(v_wsIdx_556_);
lean_dec(v_pkg_555_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_590_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
size_t v_sz_582_; size_t v___x_583_; lean_object* v_depPkgs_584_; lean_object* v___x_586_; 
v_sz_582_ = lean_array_size(v_depIdxs_569_);
v___x_583_ = ((size_t)0ULL);
lean_inc_ref(v_depIdxs_569_);
v_depPkgs_584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_x_550_, v_sz_582_, v___x_583_, v_depIdxs_569_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 14, v_depPkgs_584_);
v___x_586_ = v___x_580_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_wsIdx_556_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_baseName_557_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_keyName_558_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_origName_559_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v_dir_560_);
lean_ctor_set(v_reuseFailAlloc_589_, 5, v_relDir_561_);
lean_ctor_set(v_reuseFailAlloc_589_, 6, v_config_562_);
lean_ctor_set(v_reuseFailAlloc_589_, 7, v_configFile_563_);
lean_ctor_set(v_reuseFailAlloc_589_, 8, v_relConfigFile_564_);
lean_ctor_set(v_reuseFailAlloc_589_, 9, v_relManifestFile_565_);
lean_ctor_set(v_reuseFailAlloc_589_, 10, v_scope_566_);
lean_ctor_set(v_reuseFailAlloc_589_, 11, v_remoteUrl_567_);
lean_ctor_set(v_reuseFailAlloc_589_, 12, v_depConfigs_568_);
lean_ctor_set(v_reuseFailAlloc_589_, 13, v_depIdxs_569_);
lean_ctor_set(v_reuseFailAlloc_589_, 14, v_depPkgs_584_);
lean_ctor_set(v_reuseFailAlloc_589_, 15, v_targetDecls_570_);
lean_ctor_set(v_reuseFailAlloc_589_, 16, v_targetDeclMap_571_);
lean_ctor_set(v_reuseFailAlloc_589_, 17, v_defaultTargets_572_);
lean_ctor_set(v_reuseFailAlloc_589_, 18, v_scripts_573_);
lean_ctor_set(v_reuseFailAlloc_589_, 19, v_defaultScripts_574_);
lean_ctor_set(v_reuseFailAlloc_589_, 20, v_postUpdateHooks_575_);
lean_ctor_set(v_reuseFailAlloc_589_, 21, v_buildArchive_576_);
lean_ctor_set(v_reuseFailAlloc_589_, 22, v_testDriver_577_);
lean_ctor_set(v_reuseFailAlloc_589_, 23, v_lintDriver_578_);
v___x_586_ = v_reuseFailAlloc_589_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v_pkgs_x27_587_; 
v_pkgs_x27_587_ = lean_array_fset(v_x_550_, v_n_554_, v___x_586_);
v_x_549_ = v_n_554_;
v_x_550_ = v_pkgs_x27_587_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(lean_object* v___x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
lean_object* v_zero_595_; uint8_t v_isZero_596_; 
v_zero_595_ = lean_unsigned_to_nat(0u);
v_isZero_596_ = lean_nat_dec_eq(v_x_593_, v_zero_595_);
if (v_isZero_596_ == 1)
{
return v_x_594_;
}
else
{
lean_object* v_one_597_; lean_object* v_n_598_; lean_object* v_pkg_599_; lean_object* v_wsIdx_600_; lean_object* v_baseName_601_; lean_object* v_keyName_602_; lean_object* v_origName_603_; lean_object* v_dir_604_; lean_object* v_relDir_605_; lean_object* v_config_606_; lean_object* v_configFile_607_; lean_object* v_relConfigFile_608_; lean_object* v_relManifestFile_609_; lean_object* v_scope_610_; lean_object* v_remoteUrl_611_; lean_object* v_depConfigs_612_; lean_object* v_depIdxs_613_; lean_object* v_targetDecls_614_; lean_object* v_targetDeclMap_615_; lean_object* v_defaultTargets_616_; lean_object* v_scripts_617_; lean_object* v_defaultScripts_618_; lean_object* v_postUpdateHooks_619_; lean_object* v_buildArchive_620_; lean_object* v_testDriver_621_; lean_object* v_lintDriver_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_634_; 
v_one_597_ = lean_unsigned_to_nat(1u);
v_n_598_ = lean_nat_sub(v_x_593_, v_one_597_);
v_pkg_599_ = lean_array_fget(v_x_594_, v_n_598_);
v_wsIdx_600_ = lean_ctor_get(v_pkg_599_, 0);
v_baseName_601_ = lean_ctor_get(v_pkg_599_, 1);
v_keyName_602_ = lean_ctor_get(v_pkg_599_, 2);
v_origName_603_ = lean_ctor_get(v_pkg_599_, 3);
v_dir_604_ = lean_ctor_get(v_pkg_599_, 4);
v_relDir_605_ = lean_ctor_get(v_pkg_599_, 5);
v_config_606_ = lean_ctor_get(v_pkg_599_, 6);
v_configFile_607_ = lean_ctor_get(v_pkg_599_, 7);
v_relConfigFile_608_ = lean_ctor_get(v_pkg_599_, 8);
v_relManifestFile_609_ = lean_ctor_get(v_pkg_599_, 9);
v_scope_610_ = lean_ctor_get(v_pkg_599_, 10);
v_remoteUrl_611_ = lean_ctor_get(v_pkg_599_, 11);
v_depConfigs_612_ = lean_ctor_get(v_pkg_599_, 12);
v_depIdxs_613_ = lean_ctor_get(v_pkg_599_, 13);
v_targetDecls_614_ = lean_ctor_get(v_pkg_599_, 15);
v_targetDeclMap_615_ = lean_ctor_get(v_pkg_599_, 16);
v_defaultTargets_616_ = lean_ctor_get(v_pkg_599_, 17);
v_scripts_617_ = lean_ctor_get(v_pkg_599_, 18);
v_defaultScripts_618_ = lean_ctor_get(v_pkg_599_, 19);
v_postUpdateHooks_619_ = lean_ctor_get(v_pkg_599_, 20);
v_buildArchive_620_ = lean_ctor_get(v_pkg_599_, 21);
v_testDriver_621_ = lean_ctor_get(v_pkg_599_, 22);
v_lintDriver_622_ = lean_ctor_get(v_pkg_599_, 23);
v_isSharedCheck_634_ = !lean_is_exclusive(v_pkg_599_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v_pkg_599_, 14);
lean_dec(v_unused_635_);
v___x_624_ = v_pkg_599_;
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_lintDriver_622_);
lean_inc(v_testDriver_621_);
lean_inc(v_buildArchive_620_);
lean_inc(v_postUpdateHooks_619_);
lean_inc(v_defaultScripts_618_);
lean_inc(v_scripts_617_);
lean_inc(v_defaultTargets_616_);
lean_inc(v_targetDeclMap_615_);
lean_inc(v_targetDecls_614_);
lean_inc(v_depIdxs_613_);
lean_inc(v_depConfigs_612_);
lean_inc(v_remoteUrl_611_);
lean_inc(v_scope_610_);
lean_inc(v_relManifestFile_609_);
lean_inc(v_relConfigFile_608_);
lean_inc(v_configFile_607_);
lean_inc(v_config_606_);
lean_inc(v_relDir_605_);
lean_inc(v_dir_604_);
lean_inc(v_origName_603_);
lean_inc(v_keyName_602_);
lean_inc(v_baseName_601_);
lean_inc(v_wsIdx_600_);
lean_dec(v_pkg_599_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
size_t v_sz_626_; size_t v___x_627_; lean_object* v_depPkgs_628_; lean_object* v___x_630_; 
v_sz_626_ = lean_array_size(v_depIdxs_613_);
v___x_627_ = ((size_t)0ULL);
lean_inc_ref(v_depIdxs_613_);
v_depPkgs_628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_x_594_, v_sz_626_, v___x_627_, v_depIdxs_613_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 14, v_depPkgs_628_);
v___x_630_ = v___x_624_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_wsIdx_600_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_baseName_601_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_keyName_602_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_origName_603_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v_dir_604_);
lean_ctor_set(v_reuseFailAlloc_633_, 5, v_relDir_605_);
lean_ctor_set(v_reuseFailAlloc_633_, 6, v_config_606_);
lean_ctor_set(v_reuseFailAlloc_633_, 7, v_configFile_607_);
lean_ctor_set(v_reuseFailAlloc_633_, 8, v_relConfigFile_608_);
lean_ctor_set(v_reuseFailAlloc_633_, 9, v_relManifestFile_609_);
lean_ctor_set(v_reuseFailAlloc_633_, 10, v_scope_610_);
lean_ctor_set(v_reuseFailAlloc_633_, 11, v_remoteUrl_611_);
lean_ctor_set(v_reuseFailAlloc_633_, 12, v_depConfigs_612_);
lean_ctor_set(v_reuseFailAlloc_633_, 13, v_depIdxs_613_);
lean_ctor_set(v_reuseFailAlloc_633_, 14, v_depPkgs_628_);
lean_ctor_set(v_reuseFailAlloc_633_, 15, v_targetDecls_614_);
lean_ctor_set(v_reuseFailAlloc_633_, 16, v_targetDeclMap_615_);
lean_ctor_set(v_reuseFailAlloc_633_, 17, v_defaultTargets_616_);
lean_ctor_set(v_reuseFailAlloc_633_, 18, v_scripts_617_);
lean_ctor_set(v_reuseFailAlloc_633_, 19, v_defaultScripts_618_);
lean_ctor_set(v_reuseFailAlloc_633_, 20, v_postUpdateHooks_619_);
lean_ctor_set(v_reuseFailAlloc_633_, 21, v_buildArchive_620_);
lean_ctor_set(v_reuseFailAlloc_633_, 22, v_testDriver_621_);
lean_ctor_set(v_reuseFailAlloc_633_, 23, v_lintDriver_622_);
v___x_630_ = v_reuseFailAlloc_633_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v_pkgs_x27_631_; lean_object* v___x_632_; 
v_pkgs_x27_631_ = lean_array_fset(v_x_594_, v_n_598_, v___x_630_);
v___x_632_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(v_n_598_, v_pkgs_x27_631_);
return v___x_632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1___boxed(lean_object* v___x_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(v___x_636_, v_x_637_, v_x_638_);
lean_dec(v_x_637_);
lean_dec(v___x_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(lean_object* v_as_640_, size_t v_i_641_, size_t v_stop_642_, lean_object* v_b_643_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = lean_usize_dec_eq(v_i_641_, v_stop_642_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v_keyName_646_; lean_object* v___x_647_; size_t v___x_648_; size_t v___x_649_; 
v___x_645_ = lean_array_uget_borrowed(v_as_640_, v_i_641_);
v_keyName_646_ = lean_ctor_get(v___x_645_, 2);
lean_inc(v___x_645_);
lean_inc(v_keyName_646_);
v___x_647_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_646_, v___x_645_, v_b_643_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_641_, v___x_648_);
v_i_641_ = v___x_649_;
v_b_643_ = v___x_647_;
goto _start;
}
else
{
return v_b_643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2___boxed(lean_object* v_as_651_, lean_object* v_i_652_, lean_object* v_stop_653_, lean_object* v_b_654_){
_start:
{
size_t v_i_boxed_655_; size_t v_stop_boxed_656_; lean_object* v_res_657_; 
v_i_boxed_655_ = lean_unbox_usize(v_i_652_);
lean_dec(v_i_652_);
v_stop_boxed_656_ = lean_unbox_usize(v_stop_653_);
lean_dec(v_stop_653_);
v_res_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_as_651_, v_i_boxed_655_, v_stop_boxed_656_, v_b_654_);
lean_dec_ref(v_as_651_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(lean_object* v_self_658_){
_start:
{
lean_object* v_lakeEnv_659_; lean_object* v_lakeConfig_660_; lean_object* v_lakeCache_661_; lean_object* v_lakeArgs_x3f_662_; lean_object* v_packages_663_; lean_object* v_facetConfigs_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_683_; 
v_lakeEnv_659_ = lean_ctor_get(v_self_658_, 0);
v_lakeConfig_660_ = lean_ctor_get(v_self_658_, 1);
v_lakeCache_661_ = lean_ctor_get(v_self_658_, 2);
v_lakeArgs_x3f_662_ = lean_ctor_get(v_self_658_, 3);
v_packages_663_ = lean_ctor_get(v_self_658_, 4);
v_facetConfigs_664_ = lean_ctor_get(v_self_658_, 6);
v_isSharedCheck_683_ = !lean_is_exclusive(v_self_658_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v_self_658_, 5);
lean_dec(v_unused_684_);
v___x_666_ = v_self_658_;
v_isShared_667_ = v_isSharedCheck_683_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_facetConfigs_664_);
lean_inc(v_packages_663_);
lean_inc(v_lakeArgs_x3f_662_);
lean_inc(v_lakeCache_661_);
lean_inc(v_lakeConfig_660_);
lean_inc(v_lakeEnv_659_);
lean_dec(v_self_658_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_683_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v_val_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_668_ = lean_array_get_size(v_packages_663_);
v_val_669_ = l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(v___x_668_, v___x_668_, v_packages_663_);
v___x_670_ = lean_box(1);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_array_get_size(v_val_669_);
v___x_673_ = lean_nat_dec_lt(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_675_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 5, v___x_670_);
lean_ctor_set(v___x_666_, 4, v_val_669_);
v___x_675_ = v___x_666_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_lakeEnv_659_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_lakeConfig_660_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_lakeCache_661_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_lakeArgs_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_val_669_);
lean_ctor_set(v_reuseFailAlloc_676_, 5, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_676_, 6, v_facetConfigs_664_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_usize_of_nat(v___x_672_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_val_669_, v___x_677_, v___x_678_, v___x_670_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 5, v___x_679_);
lean_ctor_set(v___x_666_, 4, v_val_669_);
v___x_681_ = v___x_666_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_lakeEnv_659_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_lakeConfig_660_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_lakeCache_661_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_lakeArgs_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_val_669_);
lean_ctor_set(v_reuseFailAlloc_682_, 5, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_682_, 6, v_facetConfigs_664_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(lean_object* v___x_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(v_x_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___boxed(lean_object* v___x_689_, lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(v___x_689_, v_x_690_, v_x_691_);
lean_dec(v___x_689_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(lean_object* v_ws_693_, lean_object* v_size_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_mk_empty_array_with_capacity(v_size_694_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_ws_693_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init___boxed(lean_object* v_ws_697_, lean_object* v_size_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(v_ws_697_, v_size_698_);
lean_dec(v_size_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___redArg(lean_object* v_s_700_, lean_object* v_wsIdx_701_){
_start:
{
lean_object* v_ws_702_; lean_object* v_depIdxs_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
v_ws_702_ = lean_ctor_get(v_s_700_, 0);
v_depIdxs_703_ = lean_ctor_get(v_s_700_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_s_700_);
if (v_isSharedCheck_711_ == 0)
{
v___x_705_ = v_s_700_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_depIdxs_703_);
lean_inc(v_ws_702_);
lean_dec(v_s_700_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_array_push(v_depIdxs_703_, v_wsIdx_701_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_ws_702_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(lean_object* v_n_712_, lean_object* v_s_713_, lean_object* v_wsIdx_714_){
_start:
{
lean_object* v_ws_715_; lean_object* v_depIdxs_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_724_; 
v_ws_715_ = lean_ctor_get(v_s_713_, 0);
v_depIdxs_716_ = lean_ctor_get(v_s_713_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_s_713_);
if (v_isSharedCheck_724_ == 0)
{
v___x_718_ = v_s_713_;
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_depIdxs_716_);
lean_inc(v_ws_715_);
lean_dec(v_s_713_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_array_push(v_depIdxs_716_, v_wsIdx_714_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_ws_715_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___boxed(lean_object* v_n_725_, lean_object* v_s_726_, lean_object* v_wsIdx_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(v_n_725_, v_s_726_, v_wsIdx_727_);
lean_dec(v_n_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(lean_object* v_s_729_, lean_object* v_dep_730_, lean_object* v_lakeOpts_731_, lean_object* v_leanOpts_732_, uint8_t v_reconfigure_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_ws_736_; lean_object* v_depIdxs_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_766_; 
v_ws_736_ = lean_ctor_get(v_s_729_, 0);
v_depIdxs_737_ = lean_ctor_get(v_s_729_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_s_729_);
if (v_isSharedCheck_766_ == 0)
{
v___x_739_ = v_s_729_;
v_isShared_740_ = v_isSharedCheck_766_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_depIdxs_737_);
lean_inc(v_ws_736_);
lean_dec(v_s_729_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_766_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_packages_741_; lean_object* v_wsIdx_742_; lean_object* v___x_743_; 
v_packages_741_ = lean_ctor_get(v_ws_736_, 4);
v_wsIdx_742_ = lean_array_get_size(v_packages_741_);
v___x_743_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_736_, v_dep_730_, v_lakeOpts_731_, v_leanOpts_732_, v_reconfigure_733_, v_a_734_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_756_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_a_745_ = lean_ctor_get(v___x_743_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_756_ == 0)
{
v___x_747_ = v___x_743_;
v_isShared_748_ = v_isSharedCheck_756_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_756_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = lean_array_push(v_depIdxs_737_, v_wsIdx_742_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_749_);
lean_ctor_set(v___x_739_, 0, v_a_744_);
v___x_751_ = v___x_739_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_744_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_749_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_753_ = v___x_747_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_a_745_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_del_object(v___x_739_);
lean_dec_ref(v_depIdxs_737_);
v_a_757_ = lean_ctor_get(v___x_743_, 0);
v_a_758_ = lean_ctor_get(v___x_743_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_743_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_inc(v_a_757_);
lean_dec(v___x_743_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_757_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg___boxed(lean_object* v_s_767_, lean_object* v_dep_768_, lean_object* v_lakeOpts_769_, lean_object* v_leanOpts_770_, lean_object* v_reconfigure_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
uint8_t v_reconfigure_boxed_774_; lean_object* v_res_775_; 
v_reconfigure_boxed_774_ = lean_unbox(v_reconfigure_771_);
v_res_775_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(v_s_767_, v_dep_768_, v_lakeOpts_769_, v_leanOpts_770_, v_reconfigure_boxed_774_, v_a_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(lean_object* v_n_776_, lean_object* v_s_777_, lean_object* v_dep_778_, lean_object* v_lakeOpts_779_, lean_object* v_leanOpts_780_, uint8_t v_reconfigure_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_ws_784_; lean_object* v_depIdxs_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_814_; 
v_ws_784_ = lean_ctor_get(v_s_777_, 0);
v_depIdxs_785_ = lean_ctor_get(v_s_777_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_s_777_);
if (v_isSharedCheck_814_ == 0)
{
v___x_787_ = v_s_777_;
v_isShared_788_ = v_isSharedCheck_814_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_depIdxs_785_);
lean_inc(v_ws_784_);
lean_dec(v_s_777_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_814_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_packages_789_; lean_object* v_wsIdx_790_; lean_object* v___x_791_; 
v_packages_789_ = lean_ctor_get(v_ws_784_, 4);
v_wsIdx_790_ = lean_array_get_size(v_packages_789_);
v___x_791_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_784_, v_dep_778_, v_lakeOpts_779_, v_leanOpts_780_, v_reconfigure_781_, v_a_782_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_804_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_a_793_ = lean_ctor_get(v___x_791_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_804_ == 0)
{
v___x_795_ = v___x_791_;
v_isShared_796_ = v_isSharedCheck_804_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_804_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_array_push(v_depIdxs_785_, v_wsIdx_790_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_797_);
lean_ctor_set(v___x_787_, 0, v_a_792_);
v___x_799_ = v___x_787_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_792_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v___x_797_);
v___x_799_ = v_reuseFailAlloc_803_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_799_);
v___x_801_ = v___x_795_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_a_793_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_del_object(v___x_787_);
lean_dec_ref(v_depIdxs_785_);
v_a_805_ = lean_ctor_get(v___x_791_, 0);
v_a_806_ = lean_ctor_get(v___x_791_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_791_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_inc(v_a_805_);
lean_dec(v___x_791_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_805_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed(lean_object* v_n_815_, lean_object* v_s_816_, lean_object* v_dep_817_, lean_object* v_lakeOpts_818_, lean_object* v_leanOpts_819_, lean_object* v_reconfigure_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
uint8_t v_reconfigure_boxed_823_; lean_object* v_res_824_; 
v_reconfigure_boxed_823_ = lean_unbox(v_reconfigure_820_);
v_res_824_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(v_n_815_, v_s_816_, v_dep_817_, v_lakeOpts_818_, v_leanOpts_819_, v_reconfigure_boxed_823_, v_a_821_);
lean_dec(v_n_815_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___redArg(lean_object* v_inst_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = lean_apply_2(v_inst_825_, lean_box(0), lean_box(0));
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(lean_object* v_m_827_, lean_object* v_00_u03b1_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_as_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lean_apply_2(v_inst_829_, lean_box(0), lean_box(0));
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___boxed(lean_object* v_m_833_, lean_object* v_00_u03b1_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_as_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(v_m_833_, v_00_u03b1_834_, v_inst_835_, v_inst_836_, v_as_837_);
lean_dec_ref(v_as_837_);
lean_dec(v_inst_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object* v_resolve_839_, lean_object* v_pkg_840_, lean_object* v_dep_841_, lean_object* v_ws_842_, lean_object* v_toBind_843_, lean_object* v___f_844_, lean_object* v_____r_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_apply_3(v_resolve_839_, v_pkg_840_, v_dep_841_, v_ws_842_);
v___x_847_ = lean_apply_4(v_toBind_843_, lean_box(0), lean_box(0), v___x_846_, v___f_844_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object* v_start_848_, lean_object* v_s_849_, lean_object* v_opts_850_, lean_object* v_leanOpts_851_, uint8_t v_reconfigure_852_, lean_object* v_inst_853_, lean_object* v_matDep_854_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_box(v_reconfigure_852_);
v___x_856_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed), 8, 6);
lean_closure_set(v___x_856_, 0, v_start_848_);
lean_closure_set(v___x_856_, 1, v_s_849_);
lean_closure_set(v___x_856_, 2, v_matDep_854_);
lean_closure_set(v___x_856_, 3, v_opts_850_);
lean_closure_set(v___x_856_, 4, v_leanOpts_851_);
lean_closure_set(v___x_856_, 5, v___x_855_);
v___x_857_ = lean_apply_2(v_inst_853_, lean_box(0), v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object* v_start_858_, lean_object* v_s_859_, lean_object* v_opts_860_, lean_object* v_leanOpts_861_, lean_object* v_reconfigure_862_, lean_object* v_inst_863_, lean_object* v_matDep_864_){
_start:
{
uint8_t v_reconfigure_boxed_865_; lean_object* v_res_866_; 
v_reconfigure_boxed_865_ = lean_unbox(v_reconfigure_862_);
v_res_866_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(v_start_858_, v_s_859_, v_opts_860_, v_leanOpts_861_, v_reconfigure_boxed_865_, v_inst_863_, v_matDep_864_);
return v_res_866_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object* v_dep_867_, lean_object* v_x_868_){
_start:
{
lean_object* v_baseName_869_; lean_object* v_name_870_; uint8_t v___x_871_; 
v_baseName_869_ = lean_ctor_get(v_x_868_, 1);
v_name_870_ = lean_ctor_get(v_dep_867_, 0);
v___x_871_ = lean_name_eq(v_baseName_869_, v_name_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed(lean_object* v_dep_872_, lean_object* v_x_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(v_dep_872_, v_x_873_);
lean_dec_ref(v_x_873_);
lean_dec_ref(v_dep_872_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object* v___f_876_, lean_object* v_____r_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = lean_apply_1(v___f_876_, v_____r_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object* v_toPure_880_, lean_object* v_start_881_, lean_object* v_leanOpts_882_, uint8_t v_reconfigure_883_, lean_object* v_inst_884_, lean_object* v_resolve_885_, lean_object* v_pkg_886_, lean_object* v_toBind_887_, lean_object* v_baseName_888_, lean_object* v_inst_889_, lean_object* v_dep_890_, lean_object* v_s_891_){
_start:
{
lean_object* v_ws_892_; lean_object* v_depIdxs_893_; lean_object* v_packages_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_ws_892_ = lean_ctor_get(v_s_891_, 0);
lean_inc_ref(v_ws_892_);
v_depIdxs_893_ = lean_ctor_get(v_s_891_, 1);
v_packages_894_ = lean_ctor_get(v_ws_892_, 4);
lean_inc_ref(v_dep_890_);
v___f_895_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_895_, 0, v_dep_890_);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_895_, v_packages_894_, v___x_896_);
if (lean_obj_tag(v___x_897_) == 1)
{
lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_907_; 
lean_inc_ref(v_depIdxs_893_);
lean_dec_ref(v_dep_890_);
lean_dec(v_inst_889_);
lean_dec(v_baseName_888_);
lean_dec(v_toBind_887_);
lean_dec_ref(v_pkg_886_);
lean_dec(v_resolve_885_);
lean_dec(v_inst_884_);
lean_dec_ref(v_leanOpts_882_);
lean_dec(v_start_881_);
v_isSharedCheck_907_ = !lean_is_exclusive(v_s_891_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_908_ = lean_ctor_get(v_s_891_, 1);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_s_891_, 0);
lean_dec(v_unused_909_);
v___x_899_ = v_s_891_;
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
else
{
lean_dec(v_s_891_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_val_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v_val_901_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_val_901_);
lean_dec_ref_known(v___x_897_, 1);
v___x_902_ = lean_array_push(v_depIdxs_893_, v_val_901_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v___x_902_);
v___x_904_ = v___x_899_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_ws_892_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_902_);
v___x_904_ = v_reuseFailAlloc_906_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; 
v___x_905_ = lean_apply_2(v_toPure_880_, lean_box(0), v___x_904_);
return v___x_905_;
}
}
}
else
{
lean_object* v_name_910_; lean_object* v_opts_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___f_914_; uint8_t v___x_915_; 
lean_dec(v___x_897_);
lean_dec(v_toPure_880_);
v_name_910_ = lean_ctor_get(v_dep_890_, 0);
v_opts_911_ = lean_ctor_get(v_dep_890_, 4);
v___x_912_ = lean_box(v_reconfigure_883_);
lean_inc(v_opts_911_);
v___f_913_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_913_, 0, v_start_881_);
lean_closure_set(v___f_913_, 1, v_s_891_);
lean_closure_set(v___f_913_, 2, v_opts_911_);
lean_closure_set(v___f_913_, 3, v_leanOpts_882_);
lean_closure_set(v___f_913_, 4, v___x_912_);
lean_closure_set(v___f_913_, 5, v_inst_884_);
lean_inc_ref(v___f_913_);
lean_inc(v_toBind_887_);
lean_inc_ref(v_ws_892_);
lean_inc_ref(v_dep_890_);
lean_inc_ref(v_pkg_886_);
lean_inc(v_resolve_885_);
v___f_914_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4), 7, 6);
lean_closure_set(v___f_914_, 0, v_resolve_885_);
lean_closure_set(v___f_914_, 1, v_pkg_886_);
lean_closure_set(v___f_914_, 2, v_dep_890_);
lean_closure_set(v___f_914_, 3, v_ws_892_);
lean_closure_set(v___f_914_, 4, v_toBind_887_);
lean_closure_set(v___f_914_, 5, v___f_913_);
v___x_915_ = lean_name_eq(v_baseName_888_, v_name_910_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec_ref(v___f_914_);
lean_dec(v_inst_889_);
lean_dec(v_baseName_888_);
v___x_916_ = lean_box(0);
v___x_917_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(v_resolve_885_, v_pkg_886_, v_dep_890_, v_ws_892_, v_toBind_887_, v___f_913_, v___x_916_);
return v___x_917_;
}
else
{
lean_object* v___f_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec_ref(v___f_913_);
lean_dec_ref(v_ws_892_);
lean_dec_ref(v_dep_890_);
lean_dec_ref(v_pkg_886_);
lean_dec(v_resolve_885_);
v___f_918_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5), 2, 1);
lean_closure_set(v___f_918_, 0, v___f_914_);
v___x_919_ = 0;
v___x_920_ = l_Lean_Name_toString(v_baseName_888_, v___x_919_);
v___x_921_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_922_ = lean_string_append(v___x_920_, v___x_921_);
v___x_923_ = lean_apply_2(v_inst_889_, lean_box(0), v___x_922_);
v___x_924_ = lean_apply_4(v_toBind_887_, lean_box(0), lean_box(0), v___x_923_, v___f_918_);
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object* v_toPure_925_, lean_object* v_start_926_, lean_object* v_leanOpts_927_, lean_object* v_reconfigure_928_, lean_object* v_inst_929_, lean_object* v_resolve_930_, lean_object* v_pkg_931_, lean_object* v_toBind_932_, lean_object* v_baseName_933_, lean_object* v_inst_934_, lean_object* v_dep_935_, lean_object* v_s_936_){
_start:
{
uint8_t v_reconfigure_boxed_937_; lean_object* v_res_938_; 
v_reconfigure_boxed_937_ = lean_unbox(v_reconfigure_928_);
v_res_938_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(v_toPure_925_, v_start_926_, v_leanOpts_927_, v_reconfigure_boxed_937_, v_inst_929_, v_resolve_930_, v_pkg_931_, v_toBind_932_, v_baseName_933_, v_inst_934_, v_dep_935_, v_s_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0___boxed(lean_object* v_next_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_resolve_943_, lean_object* v_leanOpts_944_, lean_object* v_reconfigure_945_, lean_object* v_ws_946_, lean_object* v_____x_947_){
_start:
{
uint8_t v_reconfigure_boxed_948_; lean_object* v_res_949_; 
v_reconfigure_boxed_948_ = lean_unbox(v_reconfigure_945_);
v_res_949_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(v_next_939_, v_inst_940_, v_inst_941_, v_inst_942_, v_resolve_943_, v_leanOpts_944_, v_reconfigure_boxed_948_, v_ws_946_, v_____x_947_);
lean_dec(v_next_939_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object* v_pkg_950_, lean_object* v_next_951_, lean_object* v_toPure_952_, lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_inst_955_, lean_object* v_resolve_956_, lean_object* v_leanOpts_957_, uint8_t v_reconfigure_958_, lean_object* v_toBind_959_, lean_object* v_____x_960_){
_start:
{
lean_object* v_ws_961_; lean_object* v_depIdxs_962_; lean_object* v_ws_963_; lean_object* v_packages_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_ws_961_ = lean_ctor_get(v_____x_960_, 0);
lean_inc_ref(v_ws_961_);
v_depIdxs_962_ = lean_ctor_get(v_____x_960_, 1);
lean_inc_ref(v_depIdxs_962_);
lean_dec_ref(v_____x_960_);
v_ws_963_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_961_, v_pkg_950_, v_depIdxs_962_);
v_packages_964_ = lean_ctor_get(v_ws_963_, 4);
v___x_965_ = lean_array_get_size(v_packages_964_);
v___x_966_ = lean_nat_dec_lt(v_next_951_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
lean_dec(v_toBind_959_);
lean_dec_ref(v_leanOpts_957_);
lean_dec(v_resolve_956_);
lean_dec(v_inst_955_);
lean_dec(v_inst_954_);
lean_dec_ref(v_inst_953_);
lean_dec(v_next_951_);
v___x_967_ = lean_apply_2(v_toPure_952_, lean_box(0), v_ws_963_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_968_ = lean_box(v_reconfigure_958_);
v___f_969_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_969_, 0, v_next_951_);
lean_closure_set(v___f_969_, 1, v_inst_953_);
lean_closure_set(v___f_969_, 2, v_inst_954_);
lean_closure_set(v___f_969_, 3, v_inst_955_);
lean_closure_set(v___f_969_, 4, v_resolve_956_);
lean_closure_set(v___f_969_, 5, v_leanOpts_957_);
lean_closure_set(v___f_969_, 6, v___x_968_);
lean_closure_set(v___f_969_, 7, v_ws_963_);
v___x_970_ = lean_apply_2(v_toPure_952_, lean_box(0), lean_box(0));
v___x_971_ = lean_apply_4(v_toBind_959_, lean_box(0), lean_box(0), v___x_970_, v___f_969_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed(lean_object* v_pkg_972_, lean_object* v_next_973_, lean_object* v_toPure_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_resolve_978_, lean_object* v_leanOpts_979_, lean_object* v_reconfigure_980_, lean_object* v_toBind_981_, lean_object* v_____x_982_){
_start:
{
uint8_t v_reconfigure_boxed_983_; lean_object* v_res_984_; 
v_reconfigure_boxed_983_ = lean_unbox(v_reconfigure_980_);
v_res_984_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(v_pkg_972_, v_next_973_, v_toPure_974_, v_inst_975_, v_inst_976_, v_inst_977_, v_resolve_978_, v_leanOpts_979_, v_reconfigure_boxed_983_, v_toBind_981_, v_____x_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_resolve_988_, lean_object* v_leanOpts_989_, uint8_t v_reconfigure_990_, lean_object* v_ws_991_, lean_object* v_i_992_, lean_object* v_next_993_){
_start:
{
lean_object* v_packages_994_; lean_object* v_pkg_995_; lean_object* v_toApplicative_996_; lean_object* v_baseName_997_; lean_object* v_depConfigs_998_; lean_object* v_toBind_999_; lean_object* v_toPure_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v_s_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_packages_994_ = lean_ctor_get(v_ws_991_, 4);
lean_inc_ref(v_packages_994_);
v_pkg_995_ = lean_array_fget(v_packages_994_, v_i_992_);
v_toApplicative_996_ = lean_ctor_get(v_inst_985_, 0);
v_baseName_997_ = lean_ctor_get(v_pkg_995_, 1);
lean_inc(v_baseName_997_);
v_depConfigs_998_ = lean_ctor_get(v_pkg_995_, 12);
lean_inc_ref(v_depConfigs_998_);
v_toBind_999_ = lean_ctor_get(v_inst_985_, 1);
lean_inc_n(v_toBind_999_, 2);
v_toPure_1000_ = lean_ctor_get(v_toApplicative_996_, 1);
v___x_1001_ = lean_array_get_size(v_depConfigs_998_);
v___x_1002_ = lean_mk_empty_array_with_capacity(v___x_1001_);
v_s_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_1003_, 0, v_ws_991_);
lean_ctor_set(v_s_1003_, 1, v___x_1002_);
v___x_1004_ = lean_box(v_reconfigure_990_);
lean_inc_ref(v_leanOpts_989_);
lean_inc(v_resolve_988_);
lean_inc(v_inst_987_);
lean_inc(v_inst_986_);
lean_inc_ref(v_inst_985_);
lean_inc(v_toPure_1000_);
lean_inc(v_pkg_995_);
v___f_1005_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_1005_, 0, v_pkg_995_);
lean_closure_set(v___f_1005_, 1, v_next_993_);
lean_closure_set(v___f_1005_, 2, v_toPure_1000_);
lean_closure_set(v___f_1005_, 3, v_inst_985_);
lean_closure_set(v___f_1005_, 4, v_inst_986_);
lean_closure_set(v___f_1005_, 5, v_inst_987_);
lean_closure_set(v___f_1005_, 6, v_resolve_988_);
lean_closure_set(v___f_1005_, 7, v_leanOpts_989_);
lean_closure_set(v___f_1005_, 8, v___x_1004_);
lean_closure_set(v___f_1005_, 9, v_toBind_999_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_nat_dec_lt(v___x_1006_, v___x_1001_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_inc(v_toPure_1000_);
lean_dec_ref(v_depConfigs_998_);
lean_dec(v_baseName_997_);
lean_dec(v_pkg_995_);
lean_dec_ref(v_packages_994_);
lean_dec_ref(v_leanOpts_989_);
lean_dec(v_resolve_988_);
lean_dec(v_inst_987_);
lean_dec(v_inst_986_);
lean_dec_ref(v_inst_985_);
v___x_1008_ = lean_apply_2(v_toPure_1000_, lean_box(0), v_s_1003_);
v___x_1009_ = lean_apply_4(v_toBind_999_, lean_box(0), lean_box(0), v___x_1008_, v___f_1005_);
return v___x_1009_;
}
else
{
lean_object* v_start_1010_; lean_object* v___x_1011_; lean_object* v___f_1012_; size_t v___x_1013_; size_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_start_1010_ = lean_array_get_size(v_packages_994_);
lean_dec_ref(v_packages_994_);
v___x_1011_ = lean_box(v_reconfigure_990_);
lean_inc(v_toBind_999_);
lean_inc(v_toPure_1000_);
v___f_1012_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed), 12, 10);
lean_closure_set(v___f_1012_, 0, v_toPure_1000_);
lean_closure_set(v___f_1012_, 1, v_start_1010_);
lean_closure_set(v___f_1012_, 2, v_leanOpts_989_);
lean_closure_set(v___f_1012_, 3, v___x_1011_);
lean_closure_set(v___f_1012_, 4, v_inst_987_);
lean_closure_set(v___f_1012_, 5, v_resolve_988_);
lean_closure_set(v___f_1012_, 6, v_pkg_995_);
lean_closure_set(v___f_1012_, 7, v_toBind_999_);
lean_closure_set(v___f_1012_, 8, v_baseName_997_);
lean_closure_set(v___f_1012_, 9, v_inst_986_);
v___x_1013_ = lean_usize_of_nat(v___x_1001_);
v___x_1014_ = ((size_t)0ULL);
v___x_1015_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_985_, v___f_1012_, v_depConfigs_998_, v___x_1013_, v___x_1014_, v_s_1003_);
v___x_1016_ = lean_apply_4(v_toBind_999_, lean_box(0), lean_box(0), v___x_1015_, v___f_1005_);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object* v_next_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_resolve_1021_, lean_object* v_leanOpts_1022_, uint8_t v_reconfigure_1023_, lean_object* v_ws_1024_, lean_object* v_____x_1025_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_next_1017_, v___x_1026_);
v___x_1028_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1018_, v_inst_1019_, v_inst_1020_, v_resolve_1021_, v_leanOpts_1022_, v_reconfigure_1023_, v_ws_1024_, v_next_1017_, v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_resolve_1032_, lean_object* v_leanOpts_1033_, lean_object* v_reconfigure_1034_, lean_object* v_ws_1035_, lean_object* v_i_1036_, lean_object* v_next_1037_){
_start:
{
uint8_t v_reconfigure_boxed_1038_; lean_object* v_res_1039_; 
v_reconfigure_boxed_1038_ = lean_unbox(v_reconfigure_1034_);
v_res_1039_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1029_, v_inst_1030_, v_inst_1031_, v_resolve_1032_, v_leanOpts_1033_, v_reconfigure_boxed_1038_, v_ws_1035_, v_i_1036_, v_next_1037_);
lean_dec(v_i_1036_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* v_m_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_resolve_1044_, lean_object* v_leanOpts_1045_, uint8_t v_reconfigure_1046_, lean_object* v_ws_1047_, lean_object* v_i_1048_, lean_object* v_i__lt_1049_, lean_object* v_next_1050_, lean_object* v_lt__next_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1041_, v_inst_1042_, v_inst_1043_, v_resolve_1044_, v_leanOpts_1045_, v_reconfigure_1046_, v_ws_1047_, v_i_1048_, v_next_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object* v_m_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_resolve_1057_, lean_object* v_leanOpts_1058_, lean_object* v_reconfigure_1059_, lean_object* v_ws_1060_, lean_object* v_i_1061_, lean_object* v_i__lt_1062_, lean_object* v_next_1063_, lean_object* v_lt__next_1064_){
_start:
{
uint8_t v_reconfigure_boxed_1065_; lean_object* v_res_1066_; 
v_reconfigure_boxed_1065_ = lean_unbox(v_reconfigure_1059_);
v_res_1066_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(v_m_1053_, v_inst_1054_, v_inst_1055_, v_inst_1056_, v_resolve_1057_, v_leanOpts_1058_, v_reconfigure_boxed_1065_, v_ws_1060_, v_i_1061_, v_i__lt_1062_, v_next_1063_, v_lt__next_1064_);
lean_dec(v_i_1061_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___redArg(lean_object* v_x_1067_, lean_object* v_h__1_1068_, lean_object* v_h__2_1069_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 1)
{
lean_object* v_val_1070_; lean_object* v___x_1071_; 
lean_dec(v_h__2_1069_);
v_val_1070_ = lean_ctor_get(v_x_1067_, 0);
lean_inc(v_val_1070_);
lean_dec_ref_known(v_x_1067_, 1);
v___x_1071_ = lean_apply_1(v_h__1_1068_, v_val_1070_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; 
lean_dec(v_h__1_1068_);
v___x_1072_ = lean_apply_2(v_h__2_1069_, v_x_1067_, lean_box(0));
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(lean_object* v_ws_1073_, lean_object* v_s_1074_, lean_object* v_motive_1075_, lean_object* v_x_1076_, lean_object* v_h__1_1077_, lean_object* v_h__2_1078_){
_start:
{
if (lean_obj_tag(v_x_1076_) == 1)
{
lean_object* v_val_1079_; lean_object* v___x_1080_; 
lean_dec(v_h__2_1078_);
v_val_1079_ = lean_ctor_get(v_x_1076_, 0);
lean_inc(v_val_1079_);
lean_dec_ref_known(v_x_1076_, 1);
v___x_1080_ = lean_apply_1(v_h__1_1077_, v_val_1079_);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; 
lean_dec(v_h__1_1077_);
v___x_1081_ = lean_apply_2(v_h__2_1078_, v_x_1076_, lean_box(0));
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___boxed(lean_object* v_ws_1082_, lean_object* v_s_1083_, lean_object* v_motive_1084_, lean_object* v_x_1085_, lean_object* v_h__1_1086_, lean_object* v_h__2_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(v_ws_1082_, v_s_1083_, v_motive_1084_, v_x_1085_, v_h__1_1086_, v_h__2_1087_);
lean_dec_ref(v_s_1083_);
lean_dec_ref(v_ws_1082_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___redArg(lean_object* v_x_1089_, lean_object* v_h__1_1090_){
_start:
{
lean_object* v_ws_1091_; lean_object* v_depIdxs_1092_; lean_object* v___x_1093_; 
v_ws_1091_ = lean_ctor_get(v_x_1089_, 0);
lean_inc_ref(v_ws_1091_);
v_depIdxs_1092_ = lean_ctor_get(v_x_1089_, 1);
lean_inc_ref(v_depIdxs_1092_);
lean_dec_ref(v_x_1089_);
v___x_1093_ = lean_apply_4(v_h__1_1090_, v_ws_1091_, v_depIdxs_1092_, lean_box(0), lean_box(0));
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(lean_object* v_ws_1094_, lean_object* v_motive_1095_, lean_object* v_x_1096_, lean_object* v_h__1_1097_){
_start:
{
lean_object* v_ws_1098_; lean_object* v_depIdxs_1099_; lean_object* v___x_1100_; 
v_ws_1098_ = lean_ctor_get(v_x_1096_, 0);
lean_inc_ref(v_ws_1098_);
v_depIdxs_1099_ = lean_ctor_get(v_x_1096_, 1);
lean_inc_ref(v_depIdxs_1099_);
lean_dec_ref(v_x_1096_);
v___x_1100_ = lean_apply_4(v_h__1_1097_, v_ws_1098_, v_depIdxs_1099_, lean_box(0), lean_box(0));
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___boxed(lean_object* v_ws_1101_, lean_object* v_motive_1102_, lean_object* v_x_1103_, lean_object* v_h__1_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(v_ws_1101_, v_motive_1102_, v_x_1103_, v_h__1_1104_);
lean_dec_ref(v_ws_1101_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___redArg(lean_object* v_h__1_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_apply_1(v_h__1_1106_, lean_box(0));
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(lean_object* v_ws_1108_, lean_object* v_motive_1109_, lean_object* v_x_1110_, lean_object* v_h__1_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_apply_1(v_h__1_1111_, lean_box(0));
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___boxed(lean_object* v_ws_1113_, lean_object* v_motive_1114_, lean_object* v_x_1115_, lean_object* v_h__1_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(v_ws_1113_, v_motive_1114_, v_x_1115_, v_h__1_1116_);
lean_dec_ref(v_ws_1113_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_ws_1122_, lean_object* v_resolve_1123_, lean_object* v_root_1124_, lean_object* v_next_1125_, lean_object* v_leanOpts_1126_, uint8_t v_reconfigure_1127_){
_start:
{
lean_object* v_toApplicative_1128_; lean_object* v_toFunctor_1129_; lean_object* v_map_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_toApplicative_1128_ = lean_ctor_get(v_inst_1119_, 0);
v_toFunctor_1129_ = lean_ctor_get(v_toApplicative_1128_, 0);
v_map_1130_ = lean_ctor_get(v_toFunctor_1129_, 0);
lean_inc(v_map_1130_);
v___f_1131_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0));
v___x_1132_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1119_, v_inst_1120_, v_inst_1121_, v_resolve_1123_, v_leanOpts_1126_, v_reconfigure_1127_, v_ws_1122_, v_root_1124_, v_next_1125_);
v___x_1133_ = lean_apply_4(v_map_1130_, lean_box(0), lean_box(0), v___f_1131_, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_ws_1137_, lean_object* v_resolve_1138_, lean_object* v_root_1139_, lean_object* v_next_1140_, lean_object* v_leanOpts_1141_, lean_object* v_reconfigure_1142_){
_start:
{
uint8_t v_reconfigure_boxed_1143_; lean_object* v_res_1144_; 
v_reconfigure_boxed_1143_ = lean_unbox(v_reconfigure_1142_);
v_res_1144_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(v_inst_1134_, v_inst_1135_, v_inst_1136_, v_ws_1137_, v_resolve_1138_, v_root_1139_, v_next_1140_, v_leanOpts_1141_, v_reconfigure_boxed_1143_);
lean_dec(v_root_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* v_m_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_ws_1149_, lean_object* v_resolve_1150_, lean_object* v_root_1151_, lean_object* v_root__lt_1152_, lean_object* v_next_1153_, lean_object* v_next__lt_1154_, lean_object* v_leanOpts_1155_, uint8_t v_reconfigure_1156_){
_start:
{
lean_object* v_toApplicative_1157_; lean_object* v_toFunctor_1158_; lean_object* v_map_1159_; lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_toApplicative_1157_ = lean_ctor_get(v_inst_1146_, 0);
v_toFunctor_1158_ = lean_ctor_get(v_toApplicative_1157_, 0);
v_map_1159_ = lean_ctor_get(v_toFunctor_1158_, 0);
lean_inc(v_map_1159_);
v___f_1160_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0));
v___x_1161_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1146_, v_inst_1147_, v_inst_1148_, v_resolve_1150_, v_leanOpts_1155_, v_reconfigure_1156_, v_ws_1149_, v_root_1151_, v_next_1153_);
v___x_1162_ = lean_apply_4(v_map_1159_, lean_box(0), lean_box(0), v___f_1160_, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object* v_m_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_ws_1167_, lean_object* v_resolve_1168_, lean_object* v_root_1169_, lean_object* v_root__lt_1170_, lean_object* v_next_1171_, lean_object* v_next__lt_1172_, lean_object* v_leanOpts_1173_, lean_object* v_reconfigure_1174_){
_start:
{
uint8_t v_reconfigure_boxed_1175_; lean_object* v_res_1176_; 
v_reconfigure_boxed_1175_ = lean_unbox(v_reconfigure_1174_);
v_res_1176_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(v_m_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_, v_ws_1167_, v_resolve_1168_, v_root_1169_, v_root__lt_1170_, v_next_1171_, v_next__lt_1172_, v_leanOpts_1173_, v_reconfigure_boxed_1175_);
lean_dec(v_root_1169_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object* v_x_1177_, lean_object* v_init_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_apply_1(v_x_1177_, v_init_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object* v_m_1180_, lean_object* v_00_u03b1_1181_, lean_object* v_x_1182_, lean_object* v_init_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_apply_1(v_x_1182_, v_init_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(lean_object* v_as_1185_, size_t v_i_1186_, size_t v_stop_1187_, lean_object* v_b_1188_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_eq(v_i_1186_, v_stop_1187_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v_name_1191_; lean_object* v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; 
v___x_1190_ = lean_array_uget_borrowed(v_as_1185_, v_i_1186_);
v_name_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_name_1191_);
v___x_1192_ = l_Lean_NameSet_insert(v_b_1188_, v_name_1191_);
v___x_1193_ = ((size_t)1ULL);
v___x_1194_ = lean_usize_add(v_i_1186_, v___x_1193_);
v_i_1186_ = v___x_1194_;
v_b_1188_ = v___x_1192_;
goto _start;
}
else
{
return v_b_1188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2___boxed(lean_object* v_as_1196_, lean_object* v_i_1197_, lean_object* v_stop_1198_, lean_object* v_b_1199_){
_start:
{
size_t v_i_boxed_1200_; size_t v_stop_boxed_1201_; lean_object* v_res_1202_; 
v_i_boxed_1200_ = lean_unbox_usize(v_i_1197_);
lean_dec(v_i_1197_);
v_stop_boxed_1201_ = lean_unbox_usize(v_stop_1198_);
lean_dec(v_stop_1198_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_as_1196_, v_i_boxed_1200_, v_stop_boxed_1201_, v_b_1199_);
lean_dec_ref(v_as_1196_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(lean_object* v_as_1203_, size_t v_sz_1204_, size_t v_i_1205_, lean_object* v_b_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_usize_dec_lt(v_i_1205_, v_sz_1204_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_b_1206_);
lean_ctor_set(v___x_1210_, 1, v___y_1207_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
else
{
lean_object* v_a_1212_; lean_object* v_name_1213_; lean_object* v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; 
v_a_1212_ = lean_array_uget_borrowed(v_as_1203_, v_i_1205_);
v_name_1213_ = lean_ctor_get(v_a_1212_, 0);
lean_inc(v_name_1213_);
v___x_1214_ = l_Lean_NameSet_insert(v_b_1206_, v_name_1213_);
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_i_1205_, v___x_1215_);
v_i_1205_ = v___x_1216_;
v_b_1206_ = v___x_1214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg___boxed(lean_object* v_as_1218_, lean_object* v_sz_1219_, lean_object* v_i_1220_, lean_object* v_b_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
size_t v_sz_boxed_1224_; size_t v_i_boxed_1225_; lean_object* v_res_1226_; 
v_sz_boxed_1224_ = lean_unbox_usize(v_sz_1219_);
lean_dec(v_sz_1219_);
v_i_boxed_1225_ = lean_unbox_usize(v_i_1220_);
lean_dec(v_i_1220_);
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1218_, v_sz_boxed_1224_, v_i_boxed_1225_, v_b_1221_, v___y_1222_);
lean_dec_ref(v_as_1218_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_fst_1229_, lean_object* v_init_1230_, lean_object* v_x_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
if (lean_obj_tag(v_x_1231_) == 0)
{
lean_object* v_k_1235_; lean_object* v_l_1236_; lean_object* v_r_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_k_1235_ = lean_ctor_get(v_x_1231_, 1);
lean_inc(v_k_1235_);
v_l_1236_ = lean_ctor_get(v_x_1231_, 3);
lean_inc(v_l_1236_);
v_r_1237_ = lean_ctor_get(v_x_1231_, 4);
lean_inc(v_r_1237_);
lean_dec_ref_known(v_x_1231_, 5);
v___x_1238_ = lean_box(0);
v___x_1239_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1229_, v_init_1230_, v_l_1236_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1258_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1258_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1258_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_snd_1244_; uint8_t v___x_1245_; 
v_snd_1244_ = lean_ctor_get(v_a_1240_, 1);
lean_inc(v_snd_1244_);
lean_dec(v_a_1240_);
v___x_1245_ = l_Lean_NameSet_contains(v_fst_1229_, v_k_1235_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec(v_snd_1244_);
lean_dec(v_r_1237_);
v___x_1246_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__0));
v___x_1247_ = l_Lean_Name_toString(v_k_1235_, v___x_1245_);
v___x_1248_ = lean_string_append(v___x_1246_, v___x_1247_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__1));
v___x_1250_ = lean_string_append(v___x_1248_, v___x_1249_);
v___x_1251_ = 3;
v___x_1252_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*1, v___x_1251_);
lean_inc_ref(v___y_1233_);
v___x_1253_ = lean_apply_2(v___y_1233_, v___x_1252_, lean_box(0));
if (v_isShared_1243_ == 0)
{
lean_ctor_set_tag(v___x_1242_, 1);
lean_ctor_set(v___x_1242_, 0, v___x_1238_);
v___x_1255_ = v___x_1242_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1238_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_del_object(v___x_1242_);
lean_dec(v_k_1235_);
v_init_1230_ = v___x_1238_;
v_x_1231_ = v_r_1237_;
v___y_1232_ = v_snd_1244_;
goto _start;
}
}
}
else
{
lean_dec(v_r_1237_);
lean_dec(v_k_1235_);
return v___x_1239_;
}
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1259_, 0, v_init_1230_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___y_1232_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_fst_1262_, lean_object* v_init_1263_, lean_object* v_x_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1262_, v_init_1263_, v_x_1264_, v___y_1265_, v___y_1266_);
lean_dec_ref(v___y_1266_);
lean_dec(v_fst_1262_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(lean_object* v_toUpdate_1269_, lean_object* v___x_1270_, lean_object* v___x_1271_, lean_object* v_entries_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v___y_1277_; 
if (lean_obj_tag(v_toUpdate_1269_) == 0)
{
lean_object* v_depConfigs_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_depConfigs_1319_ = lean_ctor_get(v___x_1270_, 12);
v___x_1320_ = l_Lean_NameSet_empty;
v___x_1321_ = lean_array_get_size(v_depConfigs_1319_);
v___x_1322_ = lean_nat_dec_lt(v___x_1271_, v___x_1321_);
if (v___x_1322_ == 0)
{
v___y_1277_ = v___x_1320_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_nat_dec_le(v___x_1321_, v___x_1321_);
if (v___x_1323_ == 0)
{
if (v___x_1322_ == 0)
{
v___y_1277_ = v___x_1320_;
goto v___jp_1276_;
}
else
{
size_t v___x_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = lean_usize_of_nat(v___x_1321_);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_1319_, v___x_1324_, v___x_1325_, v___x_1320_);
v___y_1277_ = v___x_1326_;
goto v___jp_1276_;
}
}
else
{
size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((size_t)0ULL);
v___x_1328_ = lean_usize_of_nat(v___x_1321_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_1319_, v___x_1327_, v___x_1328_, v___x_1320_);
v___y_1277_ = v___x_1329_;
goto v___jp_1276_;
}
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v___y_1273_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
v___jp_1276_:
{
size_t v_sz_1278_; size_t v___x_1279_; lean_object* v___x_1280_; 
v_sz_1278_ = lean_array_size(v_entries_1272_);
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_entries_1272_, v_sz_1278_, v___x_1279_, v___y_1277_, v___y_1273_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v_fst_1282_ = lean_ctor_get(v_a_1281_, 0);
lean_inc(v_fst_1282_);
v_snd_1283_ = lean_ctor_get(v_a_1281_, 1);
lean_inc(v_snd_1283_);
lean_dec(v_a_1281_);
v___x_1284_ = lean_box(0);
v___x_1285_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1282_, v___x_1284_, v_toUpdate_1269_, v_snd_1283_, v___y_1274_);
lean_dec(v_fst_1282_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1302_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1302_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1302_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_snd_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1300_; 
v_snd_1290_ = lean_ctor_get(v_a_1286_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_a_1286_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v_a_1286_, 0);
lean_dec(v_unused_1301_);
v___x_1292_ = v_a_1286_;
v_isShared_1293_ = v_isSharedCheck_1300_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_snd_1290_);
lean_dec(v_a_1286_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1300_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1284_);
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_snd_1290_);
v___x_1295_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1297_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1295_);
v___x_1297_ = v___x_1288_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1285_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1285_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v_toUpdate_1269_);
v_a_1311_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1280_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1280_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0___boxed(lean_object* v_toUpdate_1333_, lean_object* v___x_1334_, lean_object* v___x_1335_, lean_object* v_entries_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1333_, v___x_1334_, v___x_1335_, v_entries_1336_, v___y_1337_, v___y_1338_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v_entries_1336_);
lean_dec(v___x_1335_);
lean_dec_ref(v___x_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(lean_object* v_as_1341_, size_t v_i_1342_, size_t v_stop_1343_, lean_object* v_b_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_usize_dec_eq(v_i_1342_, v_stop_1343_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; 
v___x_1348_ = lean_array_uget_borrowed(v_as_1341_, v_i_1342_);
lean_inc_ref(v___y_1345_);
lean_inc(v___x_1348_);
v___x_1349_ = lean_apply_2(v___y_1345_, v___x_1348_, lean_box(0));
v___x_1350_ = ((size_t)1ULL);
v___x_1351_ = lean_usize_add(v_i_1342_, v___x_1350_);
v_i_1342_ = v___x_1351_;
v_b_1344_ = v___x_1349_;
goto _start;
}
else
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_b_1344_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3___boxed(lean_object* v_as_1354_, lean_object* v_i_1355_, lean_object* v_stop_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
size_t v_i_boxed_1360_; size_t v_stop_boxed_1361_; lean_object* v_res_1362_; 
v_i_boxed_1360_ = lean_unbox_usize(v_i_1355_);
lean_dec(v_i_1355_);
v_stop_boxed_1361_ = lean_unbox_usize(v_stop_1356_);
lean_dec(v_stop_1356_);
v_res_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_as_1354_, v_i_boxed_1360_, v_stop_boxed_1361_, v_b_1357_, v___y_1358_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v_as_1354_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(lean_object* v_toUpdate_1363_, lean_object* v_as_1364_, size_t v_i_1365_, size_t v_stop_1366_, lean_object* v_b_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_fst_1371_; lean_object* v_snd_1372_; uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_eq(v_i_1365_, v_stop_1366_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; uint8_t v_inherited_1380_; 
v___x_1379_ = lean_array_uget_borrowed(v_as_1364_, v_i_1365_);
v_inherited_1380_ = lean_ctor_get_uint8(v___x_1379_, sizeof(void*)*5);
if (v_inherited_1380_ == 0)
{
lean_object* v_name_1381_; uint8_t v___x_1382_; 
v_name_1381_ = lean_ctor_get(v___x_1379_, 0);
v___x_1382_ = l_Lean_NameSet_contains(v_toUpdate_1363_, v_name_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_box(0);
lean_inc(v___x_1379_);
lean_inc(v_name_1381_);
v___x_1384_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1381_, v___x_1379_, v___y_1368_);
v_fst_1371_ = v___x_1383_;
v_snd_1372_ = v___x_1384_;
goto v___jp_1370_;
}
else
{
goto v___jp_1376_;
}
}
else
{
goto v___jp_1376_;
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_b_1367_);
lean_ctor_set(v___x_1385_, 1, v___y_1368_);
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
v___jp_1370_:
{
size_t v___x_1373_; size_t v___x_1374_; 
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = lean_usize_add(v_i_1365_, v___x_1373_);
v_i_1365_ = v___x_1374_;
v_b_1367_ = v_fst_1371_;
v___y_1368_ = v_snd_1372_;
goto _start;
}
v___jp_1376_:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_box(0);
v_fst_1371_ = v___x_1377_;
v_snd_1372_ = v___y_1368_;
goto v___jp_1370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg___boxed(lean_object* v_toUpdate_1387_, lean_object* v_as_1388_, lean_object* v_i_1389_, lean_object* v_stop_1390_, lean_object* v_b_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
size_t v_i_boxed_1394_; size_t v_stop_boxed_1395_; lean_object* v_res_1396_; 
v_i_boxed_1394_ = lean_unbox_usize(v_i_1389_);
lean_dec(v_i_1389_);
v_stop_boxed_1395_ = lean_unbox_usize(v_stop_1390_);
lean_dec(v_stop_1390_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1387_, v_as_1388_, v_i_boxed_1394_, v_stop_boxed_1395_, v_b_1391_, v___y_1392_);
lean_dec_ref(v_as_1388_);
lean_dec(v_toUpdate_1387_);
return v_res_1396_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1404_ = lean_array_get_size(v___x_1403_);
return v___x_1404_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1405_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = lean_nat_dec_lt(v___x_1406_, v___x_1405_);
return v___x_1407_;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7(void){
_start:
{
lean_object* v___x_1408_; size_t v___x_1409_; 
v___x_1408_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1409_ = lean_usize_of_nat(v___x_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* v_ws_1412_, lean_object* v_toUpdate_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___y_1418_; lean_object* v___y_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v_packages_1444_; lean_object* v___x_1445_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v_val_1450_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___x_1486_; lean_object* v_baseName_1487_; lean_object* v_dir_1488_; lean_object* v_config_1489_; lean_object* v_relManifestFile_1490_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; uint8_t v_fst_1495_; lean_object* v_snd_1496_; lean_object* v_packagesDir_x3f_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1541_; lean_object* v___y_1542_; uint8_t v___x_1546_; lean_object* v_rootName_1547_; lean_object* v_fst_1549_; lean_object* v_snd_1550_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v_val_1619_; lean_object* v___x_1633_; 
v_packages_1444_ = lean_ctor_get(v_ws_1412_, 4);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1486_ = lean_array_fget_borrowed(v_packages_1444_, v___x_1445_);
v_baseName_1487_ = lean_ctor_get(v___x_1486_, 1);
v_dir_1488_ = lean_ctor_get(v___x_1486_, 4);
v_config_1489_ = lean_ctor_get(v___x_1486_, 6);
v_relManifestFile_1490_ = lean_ctor_get(v___x_1486_, 9);
v___x_1546_ = 0;
lean_inc(v_baseName_1487_);
v_rootName_1547_ = l_Lean_Name_toString(v_baseName_1487_, v___x_1546_);
lean_inc_ref(v_relManifestFile_1490_);
lean_inc_ref(v_dir_1488_);
v___x_1616_ = l_Lake_joinRelative(v_dir_1488_, v_relManifestFile_1490_);
v___x_1617_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1633_ = l_Lake_Manifest_load(v___x_1616_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set_tag(v___x_1636_, 1);
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
v_val_1619_ = v___x_1639_;
goto v___jp_1618_;
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1633_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1633_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 0);
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
v_val_1619_ = v___x_1647_;
goto v___jp_1618_;
}
}
}
v___jp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v___y_1418_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
v___jp_1422_:
{
if (lean_obj_tag(v_fst_1424_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_snd_1425_);
v_a_1426_ = lean_ctor_get(v_fst_1424_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_fst_1424_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1428_ = v_fst_1424_;
v_isShared_1429_ = v_isSharedCheck_1440_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v_fst_1424_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1440_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1430_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_1431_ = lean_io_error_to_string(v_a_1426_);
v___x_1432_ = lean_string_append(v___x_1430_, v___x_1431_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = 3;
v___x_1434_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*1, v___x_1433_);
lean_inc_ref(v___y_1423_);
v___x_1435_ = lean_apply_2(v___y_1423_, v___x_1434_, lean_box(0));
v___x_1436_ = lean_box(0);
if (v_isShared_1429_ == 0)
{
lean_ctor_set_tag(v___x_1428_, 1);
lean_ctor_set(v___x_1428_, 0, v___x_1436_);
v___x_1438_ = v___x_1428_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec_ref(v_fst_1424_);
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v_snd_1425_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
v___jp_1446_:
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = lean_array_get_size(v___y_1448_);
v___x_1452_ = lean_nat_dec_lt(v___x_1445_, v___x_1451_);
if (v___x_1452_ == 0)
{
v___y_1423_ = v___y_1449_;
v_fst_1424_ = v_val_1450_;
v_snd_1425_ = v___y_1447_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1453_; size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
v___x_1453_ = lean_box(0);
v___x_1454_ = ((size_t)0ULL);
v___x_1455_ = lean_usize_of_nat(v___x_1451_);
v___x_1456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1448_, v___x_1454_, v___x_1455_, v___x_1453_, v___y_1449_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_dec_ref_known(v___x_1456_, 1);
v___y_1423_ = v___y_1449_;
v_fst_1424_ = v_val_1450_;
v_snd_1425_ = v___y_1447_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_val_1450_);
lean_dec(v___y_1447_);
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
v___jp_1465_:
{
if (lean_obj_tag(v___y_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_a_1470_ = lean_ctor_get(v___y_1469_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___y_1469_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___y_1469_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___y_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set_tag(v___x_1472_, 1);
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
v___y_1447_ = v___y_1466_;
v___y_1448_ = v___y_1467_;
v___y_1449_ = v___y_1468_;
v_val_1450_ = v___x_1475_;
goto v___jp_1446_;
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_a_1478_ = lean_ctor_get(v___y_1469_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___y_1469_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___y_1469_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___y_1469_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set_tag(v___x_1480_, 0);
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
v___y_1447_ = v___y_1466_;
v___y_1448_ = v___y_1467_;
v___y_1449_ = v___y_1468_;
v_val_1450_ = v___x_1483_;
goto v___jp_1446_;
}
}
}
}
v___jp_1491_:
{
lean_object* v_toWorkspaceConfig_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v_toWorkspaceConfig_1497_ = lean_ctor_get(v_config_1489_, 0);
v___x_1498_ = l_System_FilePath_normalize(v___y_1492_);
lean_inc_ref(v_toWorkspaceConfig_1497_);
v___x_1499_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1497_);
lean_inc_ref(v___x_1499_);
v___x_1500_ = l_System_FilePath_normalize(v___x_1499_);
v___x_1501_ = lean_string_dec_eq(v___x_1498_, v___x_1500_);
lean_dec_ref(v___x_1500_);
lean_dec_ref(v___x_1498_);
if (v___x_1501_ == 0)
{
if (v_fst_1495_ == 0)
{
lean_dec_ref(v___x_1499_);
lean_dec_ref(v___y_1494_);
v___y_1418_ = v_snd_1496_;
goto v___jp_1417_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1502_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_1503_ = lean_string_append(v___x_1502_, v___y_1494_);
v___x_1504_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_1505_ = lean_string_append(v___x_1503_, v___x_1504_);
lean_inc_ref(v_dir_1488_);
v___x_1506_ = l_Lake_joinRelative(v_dir_1488_, v___x_1499_);
v___x_1507_ = lean_string_append(v___x_1505_, v___x_1506_);
v___x_1508_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1509_ = lean_string_append(v___x_1507_, v___x_1508_);
v___x_1510_ = 1;
v___x_1511_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*1, v___x_1510_);
lean_inc_ref(v___y_1493_);
v___x_1512_ = lean_apply_2(v___y_1493_, v___x_1511_, lean_box(0));
v___x_1513_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_1506_);
v___x_1514_ = l_Lake_createParentDirs(v___x_1506_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v___x_1515_; 
lean_dec_ref_known(v___x_1514_, 1);
v___x_1515_ = lean_io_rename(v___y_1494_, v___x_1506_);
lean_dec_ref(v___x_1506_);
lean_dec_ref(v___y_1494_);
v___y_1466_ = v_snd_1496_;
v___y_1467_ = v___x_1513_;
v___y_1468_ = v___y_1493_;
v___y_1469_ = v___x_1515_;
goto v___jp_1465_;
}
else
{
lean_dec_ref(v___x_1506_);
lean_dec_ref(v___y_1494_);
v___y_1466_ = v_snd_1496_;
v___y_1467_ = v___x_1513_;
v___y_1468_ = v___y_1493_;
v___y_1469_ = v___x_1514_;
goto v___jp_1465_;
}
}
}
else
{
lean_dec_ref(v___x_1499_);
lean_dec_ref(v___y_1494_);
v___y_1418_ = v_snd_1496_;
goto v___jp_1417_;
}
}
v___jp_1516_:
{
if (lean_obj_tag(v_packagesDir_x3f_1517_) == 1)
{
lean_object* v_val_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; uint8_t v___x_1524_; 
v_val_1520_ = lean_ctor_get(v_packagesDir_x3f_1517_, 0);
lean_inc_n(v_val_1520_, 2);
lean_dec_ref_known(v_packagesDir_x3f_1517_, 1);
lean_inc_ref(v_dir_1488_);
v___x_1521_ = l_Lake_joinRelative(v_dir_1488_, v_val_1520_);
v___x_1522_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1523_ = l_System_FilePath_pathExists(v___x_1521_);
v___x_1524_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1524_ == 0)
{
v___y_1492_ = v_val_1520_;
v___y_1493_ = v___y_1519_;
v___y_1494_ = v___x_1521_;
v_fst_1495_ = v___x_1523_;
v_snd_1496_ = v___y_1518_;
goto v___jp_1491_;
}
else
{
lean_object* v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = ((size_t)0ULL);
v___x_1527_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1522_, v___x_1526_, v___x_1527_, v___x_1525_, v___y_1519_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_dec_ref_known(v___x_1528_, 1);
v___y_1492_ = v_val_1520_;
v___y_1493_ = v___y_1519_;
v___y_1494_ = v___x_1521_;
v_fst_1495_ = v___x_1523_;
v_snd_1496_ = v___y_1518_;
goto v___jp_1491_;
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec_ref(v___x_1521_);
lean_dec(v_val_1520_);
lean_dec(v___y_1518_);
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec(v_packagesDir_x3f_1517_);
v___x_1537_ = lean_box(0);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___y_1518_);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
}
v___jp_1540_:
{
if (lean_obj_tag(v___y_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v_snd_1544_; lean_object* v_packagesDir_x3f_1545_; 
v_a_1543_ = lean_ctor_get(v___y_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___y_1542_, 1);
v_snd_1544_ = lean_ctor_get(v_a_1543_, 1);
lean_inc(v_snd_1544_);
lean_dec(v_a_1543_);
v_packagesDir_x3f_1545_ = lean_ctor_get(v___y_1541_, 2);
lean_inc(v_packagesDir_x3f_1545_);
lean_dec_ref(v___y_1541_);
v_packagesDir_x3f_1517_ = v_packagesDir_x3f_1545_;
v___y_1518_ = v_snd_1544_;
v___y_1519_ = v_a_1415_;
goto v___jp_1516_;
}
else
{
lean_dec_ref(v___y_1541_);
return v___y_1542_;
}
}
v___jp_1548_:
{
if (lean_obj_tag(v_fst_1549_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1598_; 
v_a_1551_ = lean_ctor_get(v_fst_1549_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_fst_1549_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1553_ = v_fst_1549_;
v_isShared_1554_ = v_isSharedCheck_1598_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v_fst_1549_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1598_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
if (lean_obj_tag(v_a_1551_) == 11)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec_ref_known(v_a_1551_, 2);
lean_del_object(v___x_1553_);
v___x_1555_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_1556_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1413_, v___x_1486_, v___x_1445_, v___x_1555_, v_snd_1550_, v_a_1415_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1578_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1578_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1578_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_snd_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1576_; 
v_snd_1561_ = lean_ctor_get(v_a_1557_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v_a_1557_, 0);
lean_dec(v_unused_1577_);
v___x_1563_ = v_a_1557_;
v_isShared_1564_ = v_isSharedCheck_1576_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_snd_1561_);
lean_dec(v_a_1557_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1576_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1565_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8));
v___x_1566_ = lean_string_append(v_rootName_1547_, v___x_1565_);
v___x_1567_ = 1;
v___x_1568_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*1, v___x_1567_);
lean_inc_ref(v_a_1415_);
v___x_1569_ = lean_apply_2(v_a_1415_, v___x_1568_, lean_box(0));
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1569_);
v___x_1571_ = v___x_1563_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_snd_1561_);
v___x_1571_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1573_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1571_);
v___x_1573_ = v___x_1559_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_1547_);
return v___x_1556_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_1413_) == 0)
{
lean_object* v___x_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
lean_dec_ref_known(v_toUpdate_1413_, 5);
lean_dec(v_snd_1550_);
lean_dec_ref(v_rootName_1547_);
v___x_1579_ = lean_io_error_to_string(v_a_1551_);
v___x_1580_ = 3;
v___x_1581_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*1, v___x_1580_);
lean_inc_ref(v_a_1415_);
v___x_1582_ = lean_apply_2(v_a_1415_, v___x_1581_, lean_box(0));
v___x_1583_ = lean_box(0);
if (v_isShared_1554_ == 0)
{
lean_ctor_set_tag(v___x_1553_, 1);
lean_ctor_set(v___x_1553_, 0, v___x_1583_);
v___x_1585_ = v___x_1553_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1587_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_1588_ = lean_string_append(v_rootName_1547_, v___x_1587_);
v___x_1589_ = lean_io_error_to_string(v_a_1551_);
v___x_1590_ = lean_string_append(v___x_1588_, v___x_1589_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = 2;
v___x_1592_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set_uint8(v___x_1592_, sizeof(void*)*1, v___x_1591_);
lean_inc_ref(v_a_1415_);
v___x_1593_ = lean_apply_2(v_a_1415_, v___x_1592_, lean_box(0));
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v_snd_1550_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1594_);
v___x_1596_ = v___x_1553_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v_packagesDir_x3f_1600_; lean_object* v_packages_1601_; lean_object* v___x_1602_; 
lean_dec_ref(v_rootName_1547_);
v_a_1599_ = lean_ctor_get(v_fst_1549_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v_fst_1549_, 1);
v_packagesDir_x3f_1600_ = lean_ctor_get(v_a_1599_, 2);
v_packages_1601_ = lean_ctor_get(v_a_1599_, 3);
lean_inc(v_toUpdate_1413_);
v___x_1602_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1413_, v___x_1486_, v___x_1445_, v_packages_1601_, v_snd_1550_, v_a_1415_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1602_, 1);
if (lean_obj_tag(v_toUpdate_1413_) == 0)
{
lean_object* v_snd_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v_snd_1604_ = lean_ctor_get(v_a_1603_, 1);
lean_inc(v_snd_1604_);
lean_dec(v_a_1603_);
v___x_1605_ = lean_array_get_size(v_packages_1601_);
v___x_1606_ = lean_nat_dec_lt(v___x_1445_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_inc(v_packagesDir_x3f_1600_);
lean_dec_ref_known(v_toUpdate_1413_, 5);
lean_dec(v_a_1599_);
v_packagesDir_x3f_1517_ = v_packagesDir_x3f_1600_;
v___y_1518_ = v_snd_1604_;
v___y_1519_ = v_a_1415_;
goto v___jp_1516_;
}
else
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_nat_dec_le(v___x_1605_, v___x_1605_);
if (v___x_1608_ == 0)
{
if (v___x_1606_ == 0)
{
lean_inc(v_packagesDir_x3f_1600_);
lean_dec_ref_known(v_toUpdate_1413_, 5);
lean_dec(v_a_1599_);
v_packagesDir_x3f_1517_ = v_packagesDir_x3f_1600_;
v___y_1518_ = v_snd_1604_;
v___y_1519_ = v_a_1415_;
goto v___jp_1516_;
}
else
{
size_t v___x_1609_; size_t v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = ((size_t)0ULL);
v___x_1610_ = lean_usize_of_nat(v___x_1605_);
v___x_1611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1413_, v_packages_1601_, v___x_1609_, v___x_1610_, v___x_1607_, v_snd_1604_);
lean_dec_ref_known(v_toUpdate_1413_, 5);
v___y_1541_ = v_a_1599_;
v___y_1542_ = v___x_1611_;
goto v___jp_1540_;
}
}
else
{
size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = ((size_t)0ULL);
v___x_1613_ = lean_usize_of_nat(v___x_1605_);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1413_, v_packages_1601_, v___x_1612_, v___x_1613_, v___x_1607_, v_snd_1604_);
lean_dec_ref_known(v_toUpdate_1413_, 5);
v___y_1541_ = v_a_1599_;
v___y_1542_ = v___x_1614_;
goto v___jp_1540_;
}
}
}
else
{
lean_object* v_snd_1615_; 
lean_inc(v_packagesDir_x3f_1600_);
lean_dec(v_a_1599_);
v_snd_1615_ = lean_ctor_get(v_a_1603_, 1);
lean_inc(v_snd_1615_);
lean_dec(v_a_1603_);
v_packagesDir_x3f_1517_ = v_packagesDir_x3f_1600_;
v___y_1518_ = v_snd_1615_;
v___y_1519_ = v_a_1415_;
goto v___jp_1516_;
}
}
else
{
lean_dec(v_a_1599_);
lean_dec(v_toUpdate_1413_);
return v___x_1602_;
}
}
}
v___jp_1618_:
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1620_ == 0)
{
v_fst_1549_ = v_val_1619_;
v_snd_1550_ = v_a_1414_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1621_; size_t v___x_1622_; size_t v___x_1623_; lean_object* v___x_1624_; 
v___x_1621_ = lean_box(0);
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1617_, v___x_1622_, v___x_1623_, v___x_1621_, v_a_1415_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_dec_ref_known(v___x_1624_, 1);
v_fst_1549_ = v_val_1619_;
v_snd_1550_ = v_a_1414_;
goto v___jp_1548_;
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v_val_1619_);
lean_dec_ref(v_rootName_1547_);
lean_dec(v_a_1414_);
lean_dec(v_toUpdate_1413_);
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_1650_, lean_object* v_toUpdate_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1650_, v_toUpdate_1651_, v_a_1652_, v_a_1653_);
lean_dec_ref(v_a_1653_);
lean_dec_ref(v_ws_1650_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* v_as_1656_, size_t v_sz_1657_, size_t v_i_1658_, lean_object* v_b_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1656_, v_sz_1657_, v_i_1658_, v_b_1659_, v___y_1660_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* v_as_1664_, lean_object* v_sz_1665_, lean_object* v_i_1666_, lean_object* v_b_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
size_t v_sz_boxed_1671_; size_t v_i_boxed_1672_; lean_object* v_res_1673_; 
v_sz_boxed_1671_ = lean_unbox_usize(v_sz_1665_);
lean_dec(v_sz_1665_);
v_i_boxed_1672_ = lean_unbox_usize(v_i_1666_);
lean_dec(v_i_1666_);
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_1664_, v_sz_boxed_1671_, v_i_boxed_1672_, v_b_1667_, v___y_1668_, v___y_1669_);
lean_dec_ref(v___y_1669_);
lean_dec_ref(v_as_1664_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(lean_object* v_toUpdate_1674_, lean_object* v_as_1675_, size_t v_i_1676_, size_t v_stop_1677_, lean_object* v_b_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1674_, v_as_1675_, v_i_1676_, v_stop_1677_, v_b_1678_, v___y_1679_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___boxed(lean_object* v_toUpdate_1683_, lean_object* v_as_1684_, lean_object* v_i_1685_, lean_object* v_stop_1686_, lean_object* v_b_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
size_t v_i_boxed_1691_; size_t v_stop_boxed_1692_; lean_object* v_res_1693_; 
v_i_boxed_1691_ = lean_unbox_usize(v_i_1685_);
lean_dec(v_i_1685_);
v_stop_boxed_1692_ = lean_unbox_usize(v_stop_1686_);
lean_dec(v_stop_1686_);
v_res_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(v_toUpdate_1683_, v_as_1684_, v_i_boxed_1691_, v_stop_boxed_1692_, v_b_1687_, v___y_1688_, v___y_1689_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v_as_1684_);
lean_dec(v_toUpdate_1683_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_dep_1694_, lean_object* v_as_1695_, size_t v_i_1696_, size_t v_stop_1697_, lean_object* v_b_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_fst_1702_; lean_object* v_snd_1703_; lean_object* v___y_1708_; lean_object* v_name_1709_; uint8_t v___x_1712_; 
v___x_1712_ = lean_usize_dec_eq(v_i_1696_, v_stop_1697_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v_name_1714_; lean_object* v_scope_1715_; lean_object* v_configFile_1716_; lean_object* v_manifestFile_x3f_1717_; lean_object* v_src_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1745_; 
v___x_1713_ = lean_array_uget(v_as_1695_, v_i_1696_);
v_name_1714_ = lean_ctor_get(v___x_1713_, 0);
v_scope_1715_ = lean_ctor_get(v___x_1713_, 1);
v_configFile_1716_ = lean_ctor_get(v___x_1713_, 2);
v_manifestFile_x3f_1717_ = lean_ctor_get(v___x_1713_, 3);
v_src_1718_ = lean_ctor_get(v___x_1713_, 4);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1720_ = v___x_1713_;
v_isShared_1721_ = v_isSharedCheck_1745_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_src_1718_);
lean_inc(v_manifestFile_x3f_1717_);
lean_inc(v_configFile_1716_);
lean_inc(v_scope_1715_);
lean_inc(v_name_1714_);
lean_dec(v___x_1713_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1745_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
uint8_t v___x_1722_; 
v___x_1722_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1714_, v___y_1699_);
if (v___x_1722_ == 0)
{
uint8_t v___x_1723_; 
v___x_1723_ = 1;
if (lean_obj_tag(v_src_1718_) == 0)
{
uint8_t v_copy_1724_; 
v_copy_1724_ = lean_ctor_get_uint8(v_src_1718_, sizeof(void*)*1);
if (v_copy_1724_ == 0)
{
lean_object* v_dir_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1737_; 
v_dir_1725_ = lean_ctor_get(v_src_1718_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_src_1718_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1727_ = v_src_1718_;
v_isShared_1728_ = v_isSharedCheck_1737_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_dir_1725_);
lean_dec(v_src_1718_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1737_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_relPkgDir_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v_relPkgDir_1729_ = lean_ctor_get(v_dep_1694_, 1);
lean_inc_ref(v_relPkgDir_1729_);
v___x_1730_ = l_Lake_joinRelative(v_relPkgDir_1729_, v_dir_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1730_);
v___x_1732_ = v___x_1727_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1730_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*1, v_copy_1724_);
v___x_1732_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1734_; 
lean_inc(v_name_1714_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v___x_1732_);
v___x_1734_ = v___x_1720_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_name_1714_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_scope_1715_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_configFile_1716_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_manifestFile_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*5, v___x_1723_);
v___y_1708_ = v___x_1734_;
v_name_1709_ = v_name_1714_;
goto v___jp_1707_;
}
}
}
}
else
{
lean_object* v___x_1739_; 
lean_inc(v_name_1714_);
if (v_isShared_1721_ == 0)
{
v___x_1739_ = v___x_1720_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_name_1714_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_scope_1715_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_configFile_1716_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_manifestFile_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_src_1718_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*5, v___x_1723_);
v___y_1708_ = v___x_1739_;
v_name_1709_ = v_name_1714_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v___x_1742_; 
lean_inc(v_name_1714_);
if (v_isShared_1721_ == 0)
{
v___x_1742_ = v___x_1720_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_name_1714_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_scope_1715_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_configFile_1716_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v_manifestFile_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v_src_1718_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*5, v___x_1723_);
v___y_1708_ = v___x_1742_;
v_name_1709_ = v_name_1714_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v___x_1744_; 
lean_del_object(v___x_1720_);
lean_dec_ref(v_src_1718_);
lean_dec(v_manifestFile_x3f_1717_);
lean_dec_ref(v_configFile_1716_);
lean_dec_ref(v_scope_1715_);
lean_dec(v_name_1714_);
v___x_1744_ = lean_box(0);
v_fst_1702_ = v___x_1744_;
v_snd_1703_ = v___y_1699_;
goto v___jp_1701_;
}
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref(v_dep_1694_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_b_1698_);
lean_ctor_set(v___x_1746_, 1, v___y_1699_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
v___jp_1701_:
{
size_t v___x_1704_; size_t v___x_1705_; 
v___x_1704_ = ((size_t)1ULL);
v___x_1705_ = lean_usize_add(v_i_1696_, v___x_1704_);
v_i_1696_ = v___x_1705_;
v_b_1698_ = v_fst_1702_;
v___y_1699_ = v_snd_1703_;
goto _start;
}
v___jp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1709_, v___y_1708_, v___y_1699_);
v_fst_1702_ = v___x_1710_;
v_snd_1703_ = v___x_1711_;
goto v___jp_1701_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1748_, lean_object* v_as_1749_, lean_object* v_i_1750_, lean_object* v_stop_1751_, lean_object* v_b_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
size_t v_i_boxed_1755_; size_t v_stop_boxed_1756_; lean_object* v_res_1757_; 
v_i_boxed_1755_ = lean_unbox_usize(v_i_1750_);
lean_dec(v_i_1750_);
v_stop_boxed_1756_ = lean_unbox_usize(v_stop_1751_);
lean_dec(v_stop_1751_);
v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1748_, v_as_1749_, v_i_boxed_1755_, v_stop_boxed_1756_, v_b_1752_, v___y_1753_);
lean_dec_ref(v_as_1749_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_manifestEntry_1764_; lean_object* v_pkgDir_1765_; lean_object* v_name_1766_; lean_object* v_manifestFile_x3f_1767_; lean_object* v___y_1769_; lean_object* v_fst_1770_; lean_object* v_snd_1771_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v_val_1831_; lean_object* v___y_1847_; 
v_manifestEntry_1764_ = lean_ctor_get(v_dep_1760_, 4);
v_pkgDir_1765_ = lean_ctor_get(v_dep_1760_, 0);
v_name_1766_ = lean_ctor_get(v_manifestEntry_1764_, 0);
v_manifestFile_x3f_1767_ = lean_ctor_get(v_manifestEntry_1764_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1767_) == 0)
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1765_);
v___x_1868_ = l_Lake_joinRelative(v_pkgDir_1765_, v___x_1867_);
v___y_1847_ = v___x_1868_;
goto v___jp_1846_;
}
else
{
lean_object* v_val_1869_; lean_object* v___x_1870_; 
v_val_1869_ = lean_ctor_get(v_manifestFile_x3f_1767_, 0);
lean_inc(v_val_1869_);
lean_inc_ref(v_pkgDir_1765_);
v___x_1870_ = l_Lake_joinRelative(v_pkgDir_1765_, v_val_1869_);
v___y_1847_ = v___x_1870_;
goto v___jp_1846_;
}
v___jp_1768_:
{
if (lean_obj_tag(v_fst_1770_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1801_; 
lean_inc(v_name_1766_);
lean_dec_ref(v_dep_1760_);
v_a_1772_ = lean_ctor_get(v_fst_1770_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_fst_1770_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1774_ = v_fst_1770_;
v_isShared_1775_ = v_isSharedCheck_1801_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v_fst_1770_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1801_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
if (lean_obj_tag(v_a_1772_) == 11)
{
uint8_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec_ref_known(v_a_1772_, 2);
v___x_1776_ = 0;
v___x_1777_ = l_Lean_Name_toString(v_name_1766_, v___x_1776_);
v___x_1778_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1779_ = lean_string_append(v___x_1777_, v___x_1778_);
v___x_1780_ = lean_string_append(v___x_1779_, v___y_1769_);
lean_dec_ref(v___y_1769_);
v___x_1781_ = 2;
v___x_1782_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*1, v___x_1781_);
lean_inc_ref(v_a_1762_);
v___x_1783_ = lean_apply_2(v_a_1762_, v___x_1782_, lean_box(0));
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v_snd_1771_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1784_);
v___x_1786_ = v___x_1774_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
lean_dec_ref(v___y_1769_);
v___x_1788_ = 0;
v___x_1789_ = l_Lean_Name_toString(v_name_1766_, v___x_1788_);
v___x_1790_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
v___x_1792_ = lean_io_error_to_string(v_a_1772_);
v___x_1793_ = lean_string_append(v___x_1791_, v___x_1792_);
lean_dec_ref(v___x_1792_);
v___x_1794_ = 2;
v___x_1795_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
lean_ctor_set_uint8(v___x_1795_, sizeof(void*)*1, v___x_1794_);
lean_inc_ref(v_a_1762_);
v___x_1796_ = lean_apply_2(v_a_1762_, v___x_1795_, lean_box(0));
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v_snd_1771_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1797_);
v___x_1799_ = v___x_1774_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v___y_1769_);
v_a_1802_ = lean_ctor_get(v_fst_1770_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_fst_1770_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1804_ = v_fst_1770_;
v_isShared_1805_ = v_isSharedCheck_1826_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v_fst_1770_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1826_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_packages_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v_packages_1806_ = lean_ctor_get(v_a_1802_, 3);
lean_inc_ref(v_packages_1806_);
lean_dec(v_a_1802_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_array_get_size(v_packages_1806_);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_nat_dec_lt(v___x_1807_, v___x_1808_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
lean_dec_ref(v_packages_1806_);
lean_dec_ref(v_dep_1760_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v_snd_1771_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set_tag(v___x_1804_, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1811_);
v___x_1813_ = v___x_1804_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_nat_dec_le(v___x_1808_, v___x_1808_);
if (v___x_1815_ == 0)
{
if (v___x_1810_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
lean_dec_ref(v_packages_1806_);
lean_dec_ref(v_dep_1760_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1809_);
lean_ctor_set(v___x_1816_, 1, v_snd_1771_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set_tag(v___x_1804_, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1816_);
v___x_1818_ = v___x_1804_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
else
{
size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
lean_del_object(v___x_1804_);
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_of_nat(v___x_1808_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1760_, v_packages_1806_, v___x_1820_, v___x_1821_, v___x_1809_, v_snd_1771_);
lean_dec_ref(v_packages_1806_);
return v___x_1822_;
}
}
else
{
size_t v___x_1823_; size_t v___x_1824_; lean_object* v___x_1825_; 
lean_del_object(v___x_1804_);
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = lean_usize_of_nat(v___x_1808_);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1760_, v_packages_1806_, v___x_1823_, v___x_1824_, v___x_1809_, v_snd_1771_);
lean_dec_ref(v_packages_1806_);
return v___x_1825_;
}
}
}
}
}
v___jp_1827_:
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = lean_array_get_size(v___y_1828_);
v___x_1833_ = lean_nat_dec_lt(v___y_1830_, v___x_1832_);
if (v___x_1833_ == 0)
{
v___y_1769_ = v___y_1829_;
v_fst_1770_ = v_val_1831_;
v_snd_1771_ = v_a_1761_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1834_; size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1834_ = lean_box(0);
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1832_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1828_, v___x_1835_, v___x_1836_, v___x_1834_, v_a_1762_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_dec_ref_known(v___x_1837_, 1);
v___y_1769_ = v___y_1829_;
v_fst_1770_ = v_val_1831_;
v_snd_1771_ = v_a_1761_;
goto v___jp_1768_;
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref(v_val_1831_);
lean_dec_ref(v___y_1829_);
lean_dec(v_a_1761_);
lean_dec_ref(v_dep_1760_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
v___jp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1847_);
v___x_1850_ = l_Lake_Manifest_load(v___y_1847_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 1);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
v___y_1828_ = v___x_1849_;
v___y_1829_ = v___y_1847_;
v___y_1830_ = v___x_1848_;
v_val_1831_ = v___x_1856_;
goto v___jp_1827_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1859_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1850_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1850_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 0);
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
v___y_1828_ = v___x_1849_;
v___y_1829_ = v___y_1847_;
v___y_1830_ = v___x_1848_;
v_val_1831_ = v___x_1864_;
goto v___jp_1827_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1871_, v_a_1872_, v_a_1873_);
lean_dec_ref(v_a_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1876_, lean_object* v_as_1877_, size_t v_i_1878_, size_t v_stop_1879_, lean_object* v_b_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1876_, v_as_1877_, v_i_1878_, v_stop_1879_, v_b_1880_, v___y_1881_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1885_, lean_object* v_as_1886_, lean_object* v_i_1887_, lean_object* v_stop_1888_, lean_object* v_b_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
size_t v_i_boxed_1893_; size_t v_stop_boxed_1894_; lean_object* v_res_1895_; 
v_i_boxed_1893_ = lean_unbox_usize(v_i_1887_);
lean_dec(v_i_1887_);
v_stop_boxed_1894_ = lean_unbox_usize(v_stop_1888_);
lean_dec(v_stop_1888_);
v_res_1895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1885_, v_as_1886_, v_i_boxed_1893_, v_stop_boxed_1894_, v_b_1889_, v___y_1890_, v___y_1891_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v_as_1886_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1897_, lean_object* v_pkg_1898_, lean_object* v_dep_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
uint8_t v___y_1904_; lean_object* v___y_1905_; lean_object* v_name_1935_; lean_object* v___x_1936_; 
v_name_1935_ = lean_ctor_get(v_dep_1899_, 0);
v___x_1936_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1900_, v_name_1935_);
if (lean_obj_tag(v___x_1936_) == 1)
{
lean_object* v_val_1937_; lean_object* v_lakeEnv_1938_; lean_object* v_packages_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_config_1942_; lean_object* v_dir_1943_; lean_object* v_toWorkspaceConfig_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
lean_dec_ref(v_dep_1899_);
lean_dec_ref(v_pkg_1898_);
v_val_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v_lakeEnv_1938_ = lean_ctor_get(v_ws_1897_, 0);
lean_inc_ref(v_lakeEnv_1938_);
v_packages_1939_ = lean_ctor_get(v_ws_1897_, 4);
lean_inc_ref(v_packages_1939_);
lean_dec_ref(v_ws_1897_);
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = lean_array_fget(v_packages_1939_, v___x_1940_);
lean_dec_ref(v_packages_1939_);
v_config_1942_ = lean_ctor_get(v___x_1941_, 6);
lean_inc_ref(v_config_1942_);
v_dir_1943_ = lean_ctor_get(v___x_1941_, 4);
lean_inc_ref(v_dir_1943_);
lean_dec(v___x_1941_);
v_toWorkspaceConfig_1944_ = lean_ctor_get(v_config_1942_, 0);
lean_inc_ref(v_toWorkspaceConfig_1944_);
lean_dec_ref(v_config_1942_);
v___x_1945_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1944_);
v___x_1946_ = l_Lake_PackageEntry_materialize(v_val_1937_, v_lakeEnv_1938_, v_dir_1943_, v___x_1945_, v_a_1901_);
lean_dec_ref(v_lakeEnv_1938_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1955_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_a_1947_);
lean_ctor_set(v___x_1951_, 1, v_a_1900_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1951_);
v___x_1953_ = v___x_1949_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_a_1900_);
v_a_1956_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1946_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1946_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v_wsIdx_1964_; lean_object* v_relDir_1965_; uint8_t v___y_1967_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
lean_dec(v___x_1936_);
v_wsIdx_1964_ = lean_ctor_get(v_pkg_1898_, 0);
lean_inc(v_wsIdx_1964_);
v_relDir_1965_ = lean_ctor_get(v_pkg_1898_, 5);
lean_inc_ref(v_relDir_1965_);
lean_dec_ref(v_pkg_1898_);
v___x_1971_ = lean_unsigned_to_nat(0u);
v___x_1972_ = lean_nat_dec_eq(v_wsIdx_1964_, v___x_1971_);
lean_dec(v_wsIdx_1964_);
if (v___x_1972_ == 0)
{
uint8_t v___x_1973_; 
v___x_1973_ = 1;
v___y_1967_ = v___x_1973_;
goto v___jp_1966_;
}
else
{
uint8_t v___x_1974_; 
v___x_1974_ = 0;
v___y_1967_ = v___x_1974_;
goto v___jp_1966_;
}
v___jp_1966_:
{
lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1969_ = lean_string_dec_eq(v_relDir_1965_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lake_joinRelative(v_relDir_1965_, v___x_1968_);
v___y_1904_ = v___y_1967_;
v___y_1905_ = v___x_1970_;
goto v___jp_1903_;
}
else
{
v___y_1904_ = v___y_1967_;
v___y_1905_ = v_relDir_1965_;
goto v___jp_1903_;
}
}
}
v___jp_1903_:
{
lean_object* v_lakeEnv_1906_; lean_object* v_packages_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v_config_1910_; lean_object* v_dir_1911_; lean_object* v_toWorkspaceConfig_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_lakeEnv_1906_ = lean_ctor_get(v_ws_1897_, 0);
lean_inc_ref(v_lakeEnv_1906_);
v_packages_1907_ = lean_ctor_get(v_ws_1897_, 4);
lean_inc_ref(v_packages_1907_);
lean_dec_ref(v_ws_1897_);
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = lean_array_fget(v_packages_1907_, v___x_1908_);
lean_dec_ref(v_packages_1907_);
v_config_1910_ = lean_ctor_get(v___x_1909_, 6);
lean_inc_ref(v_config_1910_);
v_dir_1911_ = lean_ctor_get(v___x_1909_, 4);
lean_inc_ref(v_dir_1911_);
lean_dec(v___x_1909_);
v_toWorkspaceConfig_1912_ = lean_ctor_get(v_config_1910_, 0);
lean_inc_ref(v_toWorkspaceConfig_1912_);
lean_dec_ref(v_config_1910_);
v___x_1913_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1912_);
v___x_1914_ = l_Lake_Dependency_materialize(v_dep_1899_, v___y_1904_, v_lakeEnv_1906_, v_dir_1911_, v___x_1913_, v___y_1905_, v_a_1901_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1926_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1926_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1926_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_manifestEntry_1919_; lean_object* v_name_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v_manifestEntry_1919_ = lean_ctor_get(v_a_1915_, 4);
v_name_1920_ = lean_ctor_get(v_manifestEntry_1919_, 0);
lean_inc_ref(v_manifestEntry_1919_);
lean_inc(v_name_1920_);
v___x_1921_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1920_, v_manifestEntry_1919_, v_a_1900_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1915_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1922_);
v___x_1924_ = v___x_1917_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec(v_a_1900_);
v_a_1927_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1914_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1914_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_1975_, lean_object* v_pkg_1976_, lean_object* v_dep_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1975_, v_pkg_1976_, v_dep_1977_, v_a_1978_, v_a_1979_);
lean_dec_ref(v_a_1979_);
return v_res_1981_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_1982_; 
v___x_1982_ = 4;
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_1983_, lean_object* v_tc_x3f_1984_, uint8_t v_fixed_1985_, lean_object* v_self_1986_){
_start:
{
lean_object* v_clashes_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_clashes_1987_ = lean_ctor_get(v_self_1986_, 2);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_self_1986_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; lean_object* v_unused_1996_; 
v_unused_1995_ = lean_ctor_get(v_self_1986_, 1);
lean_dec(v_unused_1995_);
v_unused_1996_ = lean_ctor_get(v_self_1986_, 0);
lean_dec(v_unused_1996_);
v___x_1989_ = v_self_1986_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_clashes_1987_);
lean_dec(v_self_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 1, v_tc_x3f_1984_);
lean_ctor_set(v___x_1989_, 0, v_src_1983_);
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_src_1983_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_tc_x3f_1984_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_clashes_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*3, v_fixed_1985_);
return v___x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_1997_, lean_object* v_tc_x3f_1998_, lean_object* v_fixed_1999_, lean_object* v_self_2000_){
_start:
{
uint8_t v_fixed_boxed_2001_; lean_object* v_res_2002_; 
v_fixed_boxed_2001_ = lean_unbox(v_fixed_1999_);
v_res_2002_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_1997_, v_tc_x3f_1998_, v_fixed_boxed_2001_, v_self_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_2003_, lean_object* v_ver_2004_, uint8_t v_fixed_2005_, lean_object* v_self_2006_){
_start:
{
lean_object* v_src_2007_; lean_object* v_tc_x3f_2008_; lean_object* v_clashes_2009_; uint8_t v_fixed_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2019_; 
v_src_2007_ = lean_ctor_get(v_self_2006_, 0);
v_tc_x3f_2008_ = lean_ctor_get(v_self_2006_, 1);
v_clashes_2009_ = lean_ctor_get(v_self_2006_, 2);
v_fixed_2010_ = lean_ctor_get_uint8(v_self_2006_, sizeof(void*)*3);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_self_2006_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2012_ = v_self_2006_;
v_isShared_2013_ = v_isSharedCheck_2019_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_clashes_2009_);
lean_inc(v_tc_x3f_2008_);
lean_inc(v_src_2007_);
lean_dec(v_self_2006_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2019_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2014_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2014_, 0, v_src_2003_);
lean_ctor_set(v___x_2014_, 1, v_ver_2004_);
lean_ctor_set_uint8(v___x_2014_, sizeof(void*)*2, v_fixed_2005_);
v___x_2015_ = lean_array_push(v_clashes_2009_, v___x_2014_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 2, v___x_2015_);
v___x_2017_ = v___x_2012_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_src_2007_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_tc_x3f_2008_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v___x_2015_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*3, v_fixed_2010_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_2020_, lean_object* v_ver_2021_, lean_object* v_fixed_2022_, lean_object* v_self_2023_){
_start:
{
uint8_t v_fixed_boxed_2024_; lean_object* v_res_2025_; 
v_fixed_boxed_2024_ = lean_unbox(v_fixed_2022_);
v_res_2025_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_2020_, v_ver_2021_, v_fixed_boxed_2024_, v_self_2023_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v___x_2030_, lean_object* v_as_2031_, size_t v_i_2032_, size_t v_stop_2033_, lean_object* v_b_2034_){
_start:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_usize_dec_eq(v_i_2032_, v_stop_2033_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v_src_2037_; lean_object* v_ver_2038_; uint8_t v_fixed_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2056_; 
v___x_2036_ = lean_array_uget_borrowed(v_as_2031_, v_i_2032_);
v_src_2037_ = lean_ctor_get(v___x_2036_, 0);
v_ver_2038_ = lean_ctor_get(v___x_2036_, 1);
v_fixed_2039_ = lean_ctor_get_uint8(v___x_2036_, sizeof(void*)*2);
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = lean_nat_dec_lt(v___x_2040_, v___x_2030_);
if (v_fixed_2039_ == 0)
{
lean_object* v___x_2060_; 
v___x_2060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2056_ = v___x_2060_;
goto v___jp_2055_;
}
else
{
lean_object* v___x_2061_; 
v___x_2061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2056_ = v___x_2061_;
goto v___jp_2055_;
}
v___jp_2042_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; 
v___x_2046_ = lean_string_append(v___y_2044_, v___y_2045_);
lean_dec_ref(v___y_2045_);
v___x_2047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
lean_inc(v_src_2037_);
v___x_2049_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2037_, v___x_2041_);
v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = lean_string_append(v___x_2050_, v___y_2043_);
v___x_2052_ = ((size_t)1ULL);
v___x_2053_ = lean_usize_add(v_i_2032_, v___x_2052_);
v_i_2032_ = v___x_2053_;
v_b_2034_ = v___x_2051_;
goto _start;
}
v___jp_2055_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v_toString_2059_; 
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2058_ = lean_string_append(v_b_2034_, v___x_2057_);
v_toString_2059_ = lean_ctor_get(v_ver_2038_, 0);
lean_inc_ref(v_toString_2059_);
v___y_2043_ = v___y_2056_;
v___y_2044_ = v___x_2058_;
v___y_2045_ = v_toString_2059_;
goto v___jp_2042_;
}
}
else
{
return v_b_2034_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v___x_2062_, lean_object* v_as_2063_, lean_object* v_i_2064_, lean_object* v_stop_2065_, lean_object* v_b_2066_){
_start:
{
size_t v_i_boxed_2067_; size_t v_stop_boxed_2068_; lean_object* v_res_2069_; 
v_i_boxed_2067_ = lean_unbox_usize(v_i_2064_);
lean_dec(v_i_2064_);
v_stop_boxed_2068_ = lean_unbox_usize(v_stop_2065_);
lean_dec(v_stop_2065_);
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2062_, v_as_2063_, v_i_boxed_2067_, v_stop_boxed_2068_, v_b_2066_);
lean_dec_ref(v_as_2063_);
lean_dec(v___x_2062_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v___x_2070_, lean_object* v_as_2071_, size_t v_i_2072_, size_t v_stop_2073_, lean_object* v_b_2074_){
_start:
{
uint8_t v___x_2075_; 
v___x_2075_ = lean_usize_dec_eq(v_i_2072_, v_stop_2073_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v_src_2077_; lean_object* v_ver_2078_; uint8_t v_fixed_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2096_; 
v___x_2076_ = lean_array_uget_borrowed(v_as_2071_, v_i_2072_);
v_src_2077_ = lean_ctor_get(v___x_2076_, 0);
v_ver_2078_ = lean_ctor_get(v___x_2076_, 1);
v_fixed_2079_ = lean_ctor_get_uint8(v___x_2076_, sizeof(void*)*2);
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_nat_dec_lt(v___x_2080_, v___x_2070_);
if (v_fixed_2079_ == 0)
{
lean_object* v___x_2100_; 
v___x_2100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2096_ = v___x_2100_;
goto v___jp_2095_;
}
else
{
lean_object* v___x_2101_; 
v___x_2101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2096_ = v___x_2101_;
goto v___jp_2095_;
}
v___jp_2082_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2086_ = lean_string_append(v___y_2083_, v___y_2085_);
lean_dec_ref(v___y_2085_);
v___x_2087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2088_ = lean_string_append(v___x_2086_, v___x_2087_);
lean_inc(v_src_2077_);
v___x_2089_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2077_, v___x_2081_);
v___x_2090_ = lean_string_append(v___x_2088_, v___x_2089_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = lean_string_append(v___x_2090_, v___y_2084_);
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_add(v_i_2072_, v___x_2092_);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2070_, v_as_2071_, v___x_2093_, v_stop_2073_, v___x_2091_);
return v___x_2094_;
}
v___jp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v_toString_2099_; 
v___x_2097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2098_ = lean_string_append(v_b_2074_, v___x_2097_);
v_toString_2099_ = lean_ctor_get(v_ver_2078_, 0);
lean_inc_ref(v_toString_2099_);
v___y_2083_ = v___x_2098_;
v___y_2084_ = v___y_2096_;
v___y_2085_ = v_toString_2099_;
goto v___jp_2082_;
}
}
else
{
return v_b_2074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v___x_2102_, lean_object* v_as_2103_, lean_object* v_i_2104_, lean_object* v_stop_2105_, lean_object* v_b_2106_){
_start:
{
size_t v_i_boxed_2107_; size_t v_stop_boxed_2108_; lean_object* v_res_2109_; 
v_i_boxed_2107_ = lean_unbox_usize(v_i_2104_);
lean_dec(v_i_2104_);
v_stop_boxed_2108_ = lean_unbox_usize(v_stop_2105_);
lean_dec(v_stop_2105_);
v_res_2109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___x_2102_, v_as_2103_, v_i_boxed_2107_, v_stop_boxed_2108_, v_b_2106_);
lean_dec_ref(v_as_2103_);
lean_dec(v___x_2102_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_2110_, lean_object* v_as_2111_, size_t v_i_2112_, size_t v_stop_2113_, lean_object* v_b_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_a_2118_; uint8_t v___x_2122_; 
v___x_2122_ = lean_usize_dec_eq(v_i_2112_, v_stop_2113_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v_relPkgDir_2124_; lean_object* v_manifestEntry_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2123_ = lean_array_uget_borrowed(v_as_2111_, v_i_2112_);
v_relPkgDir_2124_ = lean_ctor_get(v___x_2123_, 1);
v_manifestEntry_2125_ = lean_ctor_get(v___x_2123_, 4);
lean_inc_ref(v_relPkgDir_2124_);
lean_inc_ref(v___x_2110_);
v___x_2126_ = l_Lake_joinRelative(v___x_2110_, v_relPkgDir_2124_);
v___x_2127_ = l_Lake_toolchainFileName;
v___x_2128_ = l_System_FilePath_join(v___x_2126_, v___x_2127_);
v___x_2129_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2128_);
lean_dec_ref(v___x_2128_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
if (lean_obj_tag(v_a_2130_) == 1)
{
lean_object* v_tc_x3f_2131_; 
v_tc_x3f_2131_ = lean_ctor_get(v_b_2114_, 1);
if (lean_obj_tag(v_tc_x3f_2131_) == 1)
{
lean_object* v_val_2132_; lean_object* v_src_2133_; lean_object* v_clashes_2134_; uint8_t v_fixed_2135_; lean_object* v_val_2136_; uint8_t v___x_2137_; uint8_t v___y_2139_; 
v_val_2132_ = lean_ctor_get(v_a_2130_, 0);
v_src_2133_ = lean_ctor_get(v_b_2114_, 0);
v_clashes_2134_ = lean_ctor_get(v_b_2114_, 2);
v_fixed_2135_ = lean_ctor_get_uint8(v_b_2114_, sizeof(void*)*3);
v_val_2136_ = lean_ctor_get(v_tc_x3f_2131_, 0);
v___x_2137_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2123_);
if (v___x_2137_ == 0)
{
uint8_t v___x_2148_; 
v___x_2148_ = l_Lake_ToolchainVer_ble(v_val_2132_, v_val_2136_);
if (v___x_2148_ == 0)
{
lean_inc_ref(v_clashes_2134_);
lean_inc(v_src_2133_);
lean_inc_ref(v_tc_x3f_2131_);
lean_dec_ref(v_b_2114_);
if (v_fixed_2135_ == 0)
{
goto v___jp_2146_;
}
else
{
if (v___x_2148_ == 0)
{
v___y_2139_ = v___x_2148_;
goto v___jp_2138_;
}
else
{
goto v___jp_2146_;
}
}
}
else
{
lean_dec_ref_known(v_a_2130_, 1);
v_a_2118_ = v_b_2114_;
goto v___jp_2117_;
}
}
else
{
if (v_fixed_2135_ == 0)
{
lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2163_; 
lean_inc_ref(v_clashes_2134_);
lean_inc(v_src_2133_);
lean_inc_ref(v_tc_x3f_2131_);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_b_2114_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; lean_object* v_unused_2165_; lean_object* v_unused_2166_; 
v_unused_2164_ = lean_ctor_get(v_b_2114_, 2);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_b_2114_, 1);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_b_2114_, 0);
lean_dec(v_unused_2166_);
v___x_2150_ = v_b_2114_;
v_isShared_2151_ = v_isSharedCheck_2163_;
goto v_resetjp_2149_;
}
else
{
lean_dec(v_b_2114_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2163_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
uint8_t v___x_2152_; 
v___x_2152_ = l_Lake_ToolchainVer_ble(v_val_2136_, v_val_2132_);
if (v___x_2152_ == 0)
{
lean_object* v_name_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_inc(v_val_2132_);
lean_dec_ref_known(v_a_2130_, 1);
v_name_2153_ = lean_ctor_get(v_manifestEntry_2125_, 0);
lean_inc(v_name_2153_);
v___x_2154_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2154_, 0, v_name_2153_);
lean_ctor_set(v___x_2154_, 1, v_val_2132_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*2, v___x_2137_);
v___x_2155_ = lean_array_push(v_clashes_2134_, v___x_2154_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 2, v___x_2155_);
v___x_2157_ = v___x_2150_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_src_2133_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_tc_x3f_2131_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v___x_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*3, v_fixed_2135_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
v_a_2118_ = v___x_2157_;
goto v___jp_2117_;
}
}
else
{
lean_object* v_name_2159_; lean_object* v___x_2161_; 
lean_dec(v_src_2133_);
lean_dec_ref_known(v_tc_x3f_2131_, 1);
v_name_2159_ = lean_ctor_get(v_manifestEntry_2125_, 0);
lean_inc(v_name_2159_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v_a_2130_);
lean_ctor_set(v___x_2150_, 0, v_name_2159_);
v___x_2161_ = v___x_2150_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_name_2159_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_a_2130_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_clashes_2134_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_ctor_set_uint8(v___x_2161_, sizeof(void*)*3, v___x_2137_);
v_a_2118_ = v___x_2161_;
goto v___jp_2117_;
}
}
}
}
else
{
uint8_t v___x_2167_; 
lean_inc_n(v_val_2132_, 2);
lean_dec_ref_known(v_a_2130_, 1);
lean_inc(v_val_2136_);
v___x_2167_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2136_, v_val_2132_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2177_; 
lean_inc_ref(v_clashes_2134_);
lean_inc(v_src_2133_);
lean_inc_ref(v_tc_x3f_2131_);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_b_2114_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; lean_object* v_unused_2179_; lean_object* v_unused_2180_; 
v_unused_2178_ = lean_ctor_get(v_b_2114_, 2);
lean_dec(v_unused_2178_);
v_unused_2179_ = lean_ctor_get(v_b_2114_, 1);
lean_dec(v_unused_2179_);
v_unused_2180_ = lean_ctor_get(v_b_2114_, 0);
lean_dec(v_unused_2180_);
v___x_2169_ = v_b_2114_;
v_isShared_2170_ = v_isSharedCheck_2177_;
goto v_resetjp_2168_;
}
else
{
lean_dec(v_b_2114_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2177_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v_name_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
v_name_2171_ = lean_ctor_get(v_manifestEntry_2125_, 0);
lean_inc(v_name_2171_);
v___x_2172_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2172_, 0, v_name_2171_);
lean_ctor_set(v___x_2172_, 1, v_val_2132_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*2, v___x_2137_);
v___x_2173_ = lean_array_push(v_clashes_2134_, v___x_2172_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 2, v___x_2173_);
v___x_2175_ = v___x_2169_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_src_2133_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_tc_x3f_2131_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v___x_2173_);
lean_ctor_set_uint8(v_reuseFailAlloc_2176_, sizeof(void*)*3, v_fixed_2135_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
v_a_2118_ = v___x_2175_;
goto v___jp_2117_;
}
}
}
else
{
lean_dec(v_val_2132_);
v_a_2118_ = v_b_2114_;
goto v___jp_2117_;
}
}
}
v___jp_2138_:
{
if (v___y_2139_ == 0)
{
lean_object* v_name_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_inc(v_val_2132_);
lean_dec_ref_known(v_a_2130_, 1);
v_name_2140_ = lean_ctor_get(v_manifestEntry_2125_, 0);
lean_inc(v_name_2140_);
v___x_2141_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2141_, 0, v_name_2140_);
lean_ctor_set(v___x_2141_, 1, v_val_2132_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*2, v___x_2137_);
v___x_2142_ = lean_array_push(v_clashes_2134_, v___x_2141_);
v___x_2143_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2143_, 0, v_src_2133_);
lean_ctor_set(v___x_2143_, 1, v_tc_x3f_2131_);
lean_ctor_set(v___x_2143_, 2, v___x_2142_);
lean_ctor_set_uint8(v___x_2143_, sizeof(void*)*3, v_fixed_2135_);
v_a_2118_ = v___x_2143_;
goto v___jp_2117_;
}
else
{
lean_object* v_name_2144_; lean_object* v___x_2145_; 
lean_dec(v_src_2133_);
lean_dec_ref_known(v_tc_x3f_2131_, 1);
v_name_2144_ = lean_ctor_get(v_manifestEntry_2125_, 0);
lean_inc(v_name_2144_);
v___x_2145_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2145_, 0, v_name_2144_);
lean_ctor_set(v___x_2145_, 1, v_a_2130_);
lean_ctor_set(v___x_2145_, 2, v_clashes_2134_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*3, v___x_2137_);
v_a_2118_ = v___x_2145_;
goto v___jp_2117_;
}
}
v___jp_2146_:
{
uint8_t v___x_2147_; 
v___x_2147_ = l_Lake_ToolchainVer_blt(v_val_2136_, v_val_2132_);
v___y_2139_ = v___x_2147_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_clashes_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2190_; 
v_clashes_2181_ = lean_ctor_get(v_b_2114_, 2);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_b_2114_);
if (v_isSharedCheck_2190_ == 0)
{
lean_object* v_unused_2191_; lean_object* v_unused_2192_; 
v_unused_2191_ = lean_ctor_get(v_b_2114_, 1);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_b_2114_, 0);
lean_dec(v_unused_2192_);
v___x_2183_ = v_b_2114_;
v_isShared_2184_ = v_isSharedCheck_2190_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_clashes_2181_);
lean_dec(v_b_2114_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2190_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_name_2185_; uint8_t v___x_2186_; lean_object* v___x_2188_; 
v_name_2185_ = lean_ctor_get(v_manifestEntry_2125_, 0);
v___x_2186_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2123_);
lean_inc(v_name_2185_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 1, v_a_2130_);
lean_ctor_set(v___x_2183_, 0, v_name_2185_);
v___x_2188_ = v___x_2183_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_name_2185_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_a_2130_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_clashes_2181_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_ctor_set_uint8(v___x_2188_, sizeof(void*)*3, v___x_2186_);
v_a_2118_ = v___x_2188_;
goto v___jp_2117_;
}
}
}
}
else
{
lean_dec(v_a_2130_);
v_a_2118_ = v_b_2114_;
goto v___jp_2117_;
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref(v_b_2114_);
lean_dec_ref(v___x_2110_);
v_a_2193_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2195_ = v___x_2129_;
v_isShared_2196_ = v_isSharedCheck_2205_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2129_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2205_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2197_ = lean_io_error_to_string(v_a_2193_);
v___x_2198_ = 3;
v___x_2199_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set_uint8(v___x_2199_, sizeof(void*)*1, v___x_2198_);
lean_inc_ref(v___y_2115_);
v___x_2200_ = lean_apply_2(v___y_2115_, v___x_2199_, lean_box(0));
v___x_2201_ = lean_box(0);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2201_);
v___x_2203_ = v___x_2195_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v___x_2206_; 
lean_dec_ref(v___x_2110_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v_b_2114_);
return v___x_2206_;
}
v___jp_2117_:
{
size_t v___x_2119_; size_t v___x_2120_; 
v___x_2119_ = ((size_t)1ULL);
v___x_2120_ = lean_usize_add(v_i_2112_, v___x_2119_);
v_i_2112_ = v___x_2120_;
v_b_2114_ = v_a_2118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2207_, lean_object* v_as_2208_, lean_object* v_i_2209_, lean_object* v_stop_2210_, lean_object* v_b_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
size_t v_i_boxed_2214_; size_t v_stop_boxed_2215_; lean_object* v_res_2216_; 
v_i_boxed_2214_ = lean_unbox_usize(v_i_2209_);
lean_dec(v_i_2209_);
v_stop_boxed_2215_ = lean_unbox_usize(v_stop_2210_);
lean_dec(v_stop_2210_);
v_res_2216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2207_, v_as_2208_, v_i_boxed_2214_, v_stop_boxed_2215_, v_b_2211_, v___y_2212_);
lean_dec_ref(v___y_2212_);
lean_dec_ref(v_as_2208_);
return v_res_2216_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2227_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2228_ = lean_unsigned_to_nat(4u);
v___x_2229_ = lean_mk_empty_array_with_capacity(v___x_2228_);
v___x_2230_ = lean_array_push(v___x_2229_, v___x_2227_);
return v___x_2230_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2232_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2233_ = lean_array_push(v___x_2232_, v___x_2231_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2254_, lean_object* v_rootDeps_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v___y_2259_; uint8_t v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; uint8_t v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2287_; uint8_t v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v_lakeEnv_2295_; lean_object* v_lakeArgs_x3f_2296_; lean_object* v_packages_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v_baseName_2300_; lean_object* v_dir_2301_; lean_object* v_config_2302_; lean_object* v___x_2303_; lean_object* v_rootToolchainFile_2304_; lean_object* v___y_2306_; uint8_t v___y_2307_; uint8_t v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2450_; uint8_t v___y_2451_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_lakeEnv_2295_ = lean_ctor_get(v_ws_2254_, 0);
lean_inc_ref(v_lakeEnv_2295_);
v_lakeArgs_x3f_2296_ = lean_ctor_get(v_ws_2254_, 3);
lean_inc(v_lakeArgs_x3f_2296_);
v_packages_2297_ = lean_ctor_get(v_ws_2254_, 4);
lean_inc_ref(v_packages_2297_);
lean_dec_ref(v_ws_2254_);
v___x_2298_ = lean_unsigned_to_nat(0u);
v___x_2299_ = lean_array_fget(v_packages_2297_, v___x_2298_);
lean_dec_ref(v_packages_2297_);
v_baseName_2300_ = lean_ctor_get(v___x_2299_, 1);
lean_inc(v_baseName_2300_);
v_dir_2301_ = lean_ctor_get(v___x_2299_, 4);
lean_inc_ref_n(v_dir_2301_, 3);
v_config_2302_ = lean_ctor_get(v___x_2299_, 6);
lean_inc_ref(v_config_2302_);
lean_dec(v___x_2299_);
v___x_2303_ = l_Lake_toolchainFileName;
v_rootToolchainFile_2304_ = l_Lake_joinRelative(v_dir_2301_, v___x_2303_);
v___x_2455_ = l_System_FilePath_join(v_dir_2301_, v___x_2303_);
v___x_2456_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2455_);
lean_dec_ref(v___x_2455_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2515_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2515_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2515_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v_src_2462_; lean_object* v_tc_x3f_2463_; lean_object* v_clashes_2464_; uint8_t v_fixed_2465_; lean_object* v___y_2489_; uint8_t v_fixedToolchain_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_fixedToolchain_2503_ = lean_ctor_get_uint8(v_config_2302_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_2302_);
v___x_2504_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___x_2505_ = lean_array_get_size(v_rootDeps_2255_);
v___x_2506_ = lean_nat_dec_lt(v___x_2298_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_dec_ref(v_dir_2301_);
lean_inc(v_a_2457_);
v_src_2462_ = v_baseName_2300_;
v_tc_x3f_2463_ = v_a_2457_;
v_clashes_2464_ = v___x_2504_;
v_fixed_2465_ = v_fixedToolchain_2503_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2507_; uint8_t v___x_2508_; 
lean_inc(v_a_2457_);
lean_inc(v_baseName_2300_);
v___x_2507_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2507_, 0, v_baseName_2300_);
lean_ctor_set(v___x_2507_, 1, v_a_2457_);
lean_ctor_set(v___x_2507_, 2, v___x_2504_);
lean_ctor_set_uint8(v___x_2507_, sizeof(void*)*3, v_fixedToolchain_2503_);
v___x_2508_ = lean_nat_dec_le(v___x_2505_, v___x_2505_);
if (v___x_2508_ == 0)
{
if (v___x_2506_ == 0)
{
lean_dec_ref_known(v___x_2507_, 3);
lean_dec_ref(v_dir_2301_);
lean_inc(v_a_2457_);
v_src_2462_ = v_baseName_2300_;
v_tc_x3f_2463_ = v_a_2457_;
v_clashes_2464_ = v___x_2504_;
v_fixed_2465_ = v_fixedToolchain_2503_;
goto v___jp_2461_;
}
else
{
size_t v___x_2509_; size_t v___x_2510_; lean_object* v___x_2511_; 
lean_dec(v_baseName_2300_);
v___x_2509_ = ((size_t)0ULL);
v___x_2510_ = lean_usize_of_nat(v___x_2505_);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2301_, v_rootDeps_2255_, v___x_2509_, v___x_2510_, v___x_2507_, v_a_2256_);
v___y_2489_ = v___x_2511_;
goto v___jp_2488_;
}
}
else
{
size_t v___x_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
lean_dec(v_baseName_2300_);
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = lean_usize_of_nat(v___x_2505_);
v___x_2514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2301_, v_rootDeps_2255_, v___x_2512_, v___x_2513_, v___x_2507_, v_a_2256_);
v___y_2489_ = v___x_2514_;
goto v___jp_2488_;
}
}
v___jp_2461_:
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = lean_array_get_size(v_clashes_2464_);
v___x_2467_ = lean_nat_dec_lt(v___x_2298_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_dec_ref(v_clashes_2464_);
lean_dec(v_src_2462_);
if (lean_obj_tag(v_tc_x3f_2463_) == 1)
{
if (lean_obj_tag(v_a_2457_) == 0)
{
lean_object* v_val_2468_; 
lean_del_object(v___x_2459_);
v_val_2468_ = lean_ctor_get(v_tc_x3f_2463_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v_tc_x3f_2463_, 1);
v___y_2450_ = v_val_2468_;
v___y_2451_ = v___x_2467_;
goto v___jp_2449_;
}
else
{
lean_object* v_val_2469_; lean_object* v_val_2470_; uint8_t v___x_2471_; 
v_val_2469_ = lean_ctor_get(v_tc_x3f_2463_, 0);
lean_inc_n(v_val_2469_, 2);
lean_dec_ref_known(v_tc_x3f_2463_, 1);
v_val_2470_ = lean_ctor_get(v_a_2457_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v_a_2457_, 1);
v___x_2471_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2470_, v_val_2469_);
if (v___x_2471_ == 0)
{
lean_del_object(v___x_2459_);
v___y_2450_ = v_val_2469_;
v___y_2451_ = v___x_2471_;
goto v___jp_2449_;
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
lean_dec(v_val_2469_);
lean_dec_ref(v_rootToolchainFile_2304_);
lean_dec(v_lakeArgs_x3f_2296_);
lean_dec_ref(v_lakeEnv_2295_);
v___x_2472_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15));
lean_inc_ref(v_a_2256_);
v___x_2473_ = lean_apply_2(v_a_2256_, v___x_2472_, lean_box(0));
v___x_2474_ = lean_box(0);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2474_);
v___x_2476_ = v___x_2459_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
lean_dec(v_tc_x3f_2463_);
lean_dec(v_a_2457_);
lean_dec_ref(v_rootToolchainFile_2304_);
lean_dec(v_lakeArgs_x3f_2296_);
lean_dec_ref(v_lakeEnv_2295_);
v___x_2478_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17));
lean_inc_ref(v_a_2256_);
v___x_2479_ = lean_apply_2(v_a_2256_, v___x_2478_, lean_box(0));
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2479_);
v___x_2481_ = v___x_2459_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
else
{
lean_del_object(v___x_2459_);
lean_dec(v_a_2457_);
lean_dec_ref(v_rootToolchainFile_2304_);
lean_dec(v_lakeArgs_x3f_2296_);
lean_dec_ref(v_lakeEnv_2295_);
if (lean_obj_tag(v_tc_x3f_2463_) == 1)
{
if (v_fixed_2465_ == 0)
{
lean_object* v_val_2483_; lean_object* v___x_2484_; 
v_val_2483_ = lean_ctor_get(v_tc_x3f_2463_, 0);
lean_inc(v_val_2483_);
lean_dec_ref_known(v_tc_x3f_2463_, 1);
v___x_2484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2287_ = v_val_2483_;
v___y_2288_ = v___x_2467_;
v___y_2289_ = v_src_2462_;
v___y_2290_ = v___x_2466_;
v___y_2291_ = v_clashes_2464_;
v___y_2292_ = v___x_2484_;
goto v___jp_2286_;
}
else
{
lean_object* v_val_2485_; lean_object* v___x_2486_; 
v_val_2485_ = lean_ctor_get(v_tc_x3f_2463_, 0);
lean_inc(v_val_2485_);
lean_dec_ref_known(v_tc_x3f_2463_, 1);
v___x_2486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2287_ = v_val_2485_;
v___y_2288_ = v___x_2467_;
v___y_2289_ = v_src_2462_;
v___y_2290_ = v___x_2466_;
v___y_2291_ = v_clashes_2464_;
v___y_2292_ = v___x_2486_;
goto v___jp_2286_;
}
}
else
{
lean_object* v___x_2487_; 
lean_dec(v_tc_x3f_2463_);
lean_dec(v_src_2462_);
v___x_2487_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
v___y_2265_ = v___x_2467_;
v___y_2266_ = v___x_2466_;
v___y_2267_ = v_clashes_2464_;
v___y_2268_ = v___x_2487_;
goto v___jp_2264_;
}
}
}
v___jp_2488_:
{
if (lean_obj_tag(v___y_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v_src_2491_; lean_object* v_tc_x3f_2492_; lean_object* v_clashes_2493_; uint8_t v_fixed_2494_; 
v_a_2490_ = lean_ctor_get(v___y_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___y_2489_, 1);
v_src_2491_ = lean_ctor_get(v_a_2490_, 0);
lean_inc(v_src_2491_);
v_tc_x3f_2492_ = lean_ctor_get(v_a_2490_, 1);
lean_inc(v_tc_x3f_2492_);
v_clashes_2493_ = lean_ctor_get(v_a_2490_, 2);
lean_inc_ref(v_clashes_2493_);
v_fixed_2494_ = lean_ctor_get_uint8(v_a_2490_, sizeof(void*)*3);
lean_dec(v_a_2490_);
v_src_2462_ = v_src_2491_;
v_tc_x3f_2463_ = v_tc_x3f_2492_;
v_clashes_2464_ = v_clashes_2493_;
v_fixed_2465_ = v_fixed_2494_;
goto v___jp_2461_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_del_object(v___x_2459_);
lean_dec(v_a_2457_);
lean_dec_ref(v_rootToolchainFile_2304_);
lean_dec(v_lakeArgs_x3f_2296_);
lean_dec_ref(v_lakeEnv_2295_);
v_a_2495_ = lean_ctor_get(v___y_2489_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___y_2489_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___y_2489_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___y_2489_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v_rootToolchainFile_2304_);
lean_dec_ref(v_config_2302_);
lean_dec_ref(v_dir_2301_);
lean_dec(v_baseName_2300_);
lean_dec(v_lakeArgs_x3f_2296_);
lean_dec_ref(v_lakeEnv_2295_);
v_a_2516_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2518_ = v___x_2456_;
v_isShared_2519_ = v_isSharedCheck_2528_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2456_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2528_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; uint8_t v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2520_ = lean_io_error_to_string(v_a_2516_);
v___x_2521_ = 3;
v___x_2522_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set_uint8(v___x_2522_, sizeof(void*)*1, v___x_2521_);
lean_inc_ref(v_a_2256_);
v___x_2523_ = lean_apply_2(v_a_2256_, v___x_2522_, lean_box(0));
v___x_2524_ = lean_box(0);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2524_);
v___x_2526_ = v___x_2518_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
v___jp_2258_:
{
uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2260_ = 2;
v___x_2261_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2261_, 0, v___y_2259_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*1, v___x_2260_);
lean_inc_ref(v_a_2256_);
v___x_2262_ = lean_apply_2(v_a_2256_, v___x_2261_, lean_box(0));
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
return v___x_2263_;
}
v___jp_2264_:
{
if (v___y_2265_ == 0)
{
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
v___y_2259_ = v___y_2268_;
goto v___jp_2258_;
}
else
{
size_t v___x_2269_; size_t v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = ((size_t)0ULL);
v___x_2270_ = lean_usize_of_nat(v___y_2266_);
v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2266_, v___y_2267_, v___x_2269_, v___x_2270_, v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
v___y_2259_ = v___x_2271_;
goto v___jp_2258_;
}
}
v___jp_2272_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_inc_ref(v___y_2278_);
v___x_2280_ = lean_string_append(v___y_2278_, v___y_2279_);
lean_dec_ref(v___y_2279_);
v___x_2281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2282_ = lean_string_append(v___x_2280_, v___x_2281_);
v___x_2283_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2275_, v___y_2273_);
v___x_2284_ = lean_string_append(v___x_2282_, v___x_2283_);
lean_dec_ref(v___x_2283_);
v___x_2285_ = lean_string_append(v___x_2284_, v___y_2277_);
v___y_2265_ = v___y_2273_;
v___y_2266_ = v___y_2274_;
v___y_2267_ = v___y_2276_;
v___y_2268_ = v___x_2285_;
goto v___jp_2264_;
}
v___jp_2286_:
{
lean_object* v___x_2293_; lean_object* v_toString_2294_; 
v___x_2293_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_2294_ = lean_ctor_get(v___y_2287_, 0);
lean_inc_ref(v_toString_2294_);
lean_dec_ref(v___y_2287_);
v___y_2273_ = v___y_2288_;
v___y_2274_ = v___y_2290_;
v___y_2275_ = v___y_2289_;
v___y_2276_ = v___y_2291_;
v___y_2277_ = v___y_2292_;
v___y_2278_ = v___x_2293_;
v___y_2279_ = v_toString_2294_;
goto v___jp_2272_;
}
v___jp_2305_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_inc_ref(v___y_2306_);
v___x_2310_ = lean_string_append(v___y_2306_, v___y_2309_);
v___x_2311_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2312_ = lean_string_append(v___x_2310_, v___x_2311_);
v___x_2313_ = 1;
v___x_2314_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*1, v___x_2313_);
lean_inc_ref(v_a_2256_);
v___x_2315_ = lean_apply_2(v_a_2256_, v___x_2314_, lean_box(0));
v___x_2316_ = l_IO_FS_writeFile(v_rootToolchainFile_2304_, v___y_2309_);
lean_dec_ref(v_rootToolchainFile_2304_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_dec_ref_known(v___x_2316_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2296_) == 1)
{
lean_object* v_elan_x3f_2317_; 
v_elan_x3f_2317_ = lean_ctor_get(v_lakeEnv_2295_, 2);
if (lean_obj_tag(v_elan_x3f_2317_) == 1)
{
lean_object* v_val_2318_; lean_object* v_val_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v_elan_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_val_2318_ = lean_ctor_get(v_lakeArgs_x3f_2296_, 0);
lean_inc(v_val_2318_);
lean_dec_ref_known(v_lakeArgs_x3f_2296_, 1);
v_val_2319_ = lean_ctor_get(v_elan_x3f_2317_, 0);
v___x_2320_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_2256_);
v___x_2321_ = lean_apply_2(v_a_2256_, v___x_2320_, lean_box(0));
v___x_2322_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_2323_ = lean_ctor_get(v_val_2319_, 1);
lean_inc_ref(v_elan_2323_);
v___x_2324_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_2325_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_2326_ = lean_array_push(v___x_2325_, v___y_2309_);
v___x_2327_ = lean_array_push(v___x_2326_, v___x_2324_);
v___x_2328_ = l_Array_append___redArg(v___x_2327_, v_val_2318_);
lean_dec(v_val_2318_);
v___x_2329_ = lean_box(0);
v___x_2330_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2295_);
v___x_2331_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2331_, 0, v___x_2322_);
lean_ctor_set(v___x_2331_, 1, v_elan_2323_);
lean_ctor_set(v___x_2331_, 2, v___x_2328_);
lean_ctor_set(v___x_2331_, 3, v___x_2329_);
lean_ctor_set(v___x_2331_, 4, v___x_2330_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*5, v___y_2307_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*5 + 1, v___y_2308_);
v___x_2332_ = lean_io_process_spawn(v___x_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = lean_io_process_child_wait(v___x_2322_, v_a_2333_);
lean_dec(v_a_2333_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; uint32_t v___x_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = lean_unbox_uint32(v_a_2335_);
lean_dec(v_a_2335_);
v___x_2337_ = lean_uint32_to_uint8(v___x_2336_);
v___x_2338_ = lean_io_exit(v___x_2337_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2359_; 
v_a_2347_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2349_ = v___x_2338_;
v_isShared_2350_ = v_isSharedCheck_2359_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2338_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2359_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2351_ = lean_io_error_to_string(v_a_2347_);
v___x_2352_ = 3;
v___x_2353_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*1, v___x_2352_);
lean_inc_ref(v_a_2256_);
v___x_2354_ = lean_apply_2(v_a_2256_, v___x_2353_, lean_box(0));
v___x_2355_ = lean_box(0);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2355_);
v___x_2357_ = v___x_2349_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2372_; 
v_a_2360_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2362_ = v___x_2334_;
v_isShared_2363_ = v_isSharedCheck_2372_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2334_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2372_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2364_ = lean_io_error_to_string(v_a_2360_);
v___x_2365_ = 3;
v___x_2366_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set_uint8(v___x_2366_, sizeof(void*)*1, v___x_2365_);
lean_inc_ref(v_a_2256_);
v___x_2367_ = lean_apply_2(v_a_2256_, v___x_2366_, lean_box(0));
v___x_2368_ = lean_box(0);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2368_);
v___x_2370_ = v___x_2362_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2385_; 
v_a_2373_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2375_ = v___x_2332_;
v_isShared_2376_ = v_isSharedCheck_2385_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2332_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2385_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2377_ = lean_io_error_to_string(v_a_2373_);
v___x_2378_ = 3;
v___x_2379_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*1, v___x_2378_);
lean_inc_ref(v_a_2256_);
v___x_2380_ = lean_apply_2(v_a_2256_, v___x_2379_, lean_box(0));
v___x_2381_ = lean_box(0);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2381_);
v___x_2383_ = v___x_2375_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
else
{
lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; 
lean_dec_ref_known(v_lakeArgs_x3f_2296_, 1);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_lakeEnv_2295_);
v___x_2386_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_2256_);
v___x_2387_ = lean_apply_2(v_a_2256_, v___x_2386_, lean_box(0));
v___x_2388_ = 4;
v___x_2389_ = lean_io_exit(v___x_2388_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2410_; 
v_a_2398_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2400_ = v___x_2389_;
v_isShared_2401_ = v_isSharedCheck_2410_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2389_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2410_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2402_ = lean_io_error_to_string(v_a_2398_);
v___x_2403_ = 3;
v___x_2404_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*1, v___x_2403_);
lean_inc_ref(v_a_2256_);
v___x_2405_ = lean_apply_2(v_a_2256_, v___x_2404_, lean_box(0));
v___x_2406_ = lean_box(0);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2406_);
v___x_2408_ = v___x_2400_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; lean_object* v___x_2414_; 
lean_dec_ref(v___y_2309_);
lean_dec(v_lakeArgs_x3f_2296_);
lean_dec_ref(v_lakeEnv_2295_);
v___x_2411_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2256_);
v___x_2412_ = lean_apply_2(v_a_2256_, v___x_2411_, lean_box(0));
v___x_2413_ = 4;
v___x_2414_ = lean_io_exit(v___x_2413_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2435_; 
v_a_2423_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2425_ = v___x_2414_;
v_isShared_2426_ = v_isSharedCheck_2435_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2414_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2435_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2427_ = lean_io_error_to_string(v_a_2423_);
v___x_2428_ = 3;
v___x_2429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set_uint8(v___x_2429_, sizeof(void*)*1, v___x_2428_);
lean_inc_ref(v_a_2256_);
v___x_2430_ = lean_apply_2(v_a_2256_, v___x_2429_, lean_box(0));
v___x_2431_ = lean_box(0);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2431_);
v___x_2433_ = v___x_2425_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2448_; 
lean_dec_ref(v___y_2309_);
lean_dec(v_lakeArgs_x3f_2296_);
lean_dec_ref(v_lakeEnv_2295_);
v_a_2436_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2438_ = v___x_2316_;
v_isShared_2439_ = v_isSharedCheck_2448_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2316_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2448_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2440_ = lean_io_error_to_string(v_a_2436_);
v___x_2441_ = 3;
v___x_2442_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set_uint8(v___x_2442_, sizeof(void*)*1, v___x_2441_);
lean_inc_ref(v_a_2256_);
v___x_2443_ = lean_apply_2(v_a_2256_, v___x_2442_, lean_box(0));
v___x_2444_ = lean_box(0);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2444_);
v___x_2446_ = v___x_2438_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
v___jp_2449_:
{
uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v_toString_2454_; 
v___x_2452_ = 1;
v___x_2453_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2454_ = lean_ctor_get(v___y_2450_, 0);
lean_inc_ref(v_toString_2454_);
lean_dec_ref(v___y_2450_);
v___y_2306_ = v___x_2453_;
v___y_2307_ = v___x_2452_;
v___y_2308_ = v___y_2451_;
v___y_2309_ = v_toString_2454_;
goto v___jp_2305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2529_, lean_object* v_rootDeps_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2529_, v_rootDeps_2530_, v_a_2531_);
lean_dec_ref(v_a_2531_);
lean_dec_ref(v_rootDeps_2530_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2534_, lean_object* v_dep_2535_, lean_object* v_ws_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2536_, v_pkg_2534_, v_dep_2535_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v_fst_2542_; lean_object* v_snd_2543_; lean_object* v___x_2544_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2540_, 1);
v_fst_2542_ = lean_ctor_get(v_a_2541_, 0);
lean_inc_n(v_fst_2542_, 2);
v_snd_2543_ = lean_ctor_get(v_a_2541_, 1);
lean_inc(v_snd_2543_);
lean_dec(v_a_2541_);
v___x_2544_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2542_, v_snd_2543_, v_a_2538_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2561_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2561_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2561_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_snd_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2559_; 
v_snd_2549_ = lean_ctor_get(v_a_2545_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_a_2545_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v_a_2545_, 0);
lean_dec(v_unused_2560_);
v___x_2551_ = v_a_2545_;
v_isShared_2552_ = v_isSharedCheck_2559_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_snd_2549_);
lean_dec(v_a_2545_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2559_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_fst_2542_);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_fst_2542_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_snd_2549_);
v___x_2554_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2556_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2554_);
v___x_2556_ = v___x_2547_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v_fst_2542_);
v_a_2562_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2544_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2544_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
return v___x_2540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2570_, lean_object* v_dep_2571_, lean_object* v_ws_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2570_, v_dep_2571_, v_ws_2572_, v_a_2573_, v_a_2574_);
lean_dec_ref(v_a_2574_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2577_, lean_object* v_ws_2578_, lean_object* v_pkg_2579_, lean_object* v_dep_2580_, lean_object* v_a_2581_){
_start:
{
uint8_t v___y_2584_; lean_object* v___y_2585_; lean_object* v_name_2615_; lean_object* v___x_2616_; 
v_name_2615_ = lean_ctor_get(v_dep_2580_, 0);
v___x_2616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2581_, v_name_2615_);
if (lean_obj_tag(v___x_2616_) == 1)
{
lean_object* v_val_2617_; lean_object* v_lakeEnv_2618_; lean_object* v_packages_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v_config_2622_; lean_object* v_dir_2623_; lean_object* v_toWorkspaceConfig_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec_ref(v_dep_2580_);
lean_dec_ref(v_pkg_2579_);
v_val_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_val_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v_lakeEnv_2618_ = lean_ctor_get(v_ws_2578_, 0);
lean_inc_ref(v_lakeEnv_2618_);
v_packages_2619_ = lean_ctor_get(v_ws_2578_, 4);
lean_inc_ref(v_packages_2619_);
lean_dec_ref(v_ws_2578_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_array_fget(v_packages_2619_, v___x_2620_);
lean_dec_ref(v_packages_2619_);
v_config_2622_ = lean_ctor_get(v___x_2621_, 6);
lean_inc_ref(v_config_2622_);
v_dir_2623_ = lean_ctor_get(v___x_2621_, 4);
lean_inc_ref(v_dir_2623_);
lean_dec(v___x_2621_);
v_toWorkspaceConfig_2624_ = lean_ctor_get(v_config_2622_, 0);
lean_inc_ref(v_toWorkspaceConfig_2624_);
lean_dec_ref(v_config_2622_);
v___x_2625_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2624_);
v___x_2626_ = l_Lake_PackageEntry_materialize(v_val_2617_, v_lakeEnv_2618_, v_dir_2623_, v___x_2625_, v___y_2577_);
lean_dec_ref(v_lakeEnv_2618_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2635_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2635_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2635_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v_a_2627_);
lean_ctor_set(v___x_2631_, 1, v_a_2581_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2631_);
v___x_2633_ = v___x_2629_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec(v_a_2581_);
v_a_2636_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2626_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2626_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
else
{
lean_object* v_wsIdx_2644_; lean_object* v_relDir_2645_; uint8_t v___y_2647_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
lean_dec(v___x_2616_);
v_wsIdx_2644_ = lean_ctor_get(v_pkg_2579_, 0);
lean_inc(v_wsIdx_2644_);
v_relDir_2645_ = lean_ctor_get(v_pkg_2579_, 5);
lean_inc_ref(v_relDir_2645_);
lean_dec_ref(v_pkg_2579_);
v___x_2651_ = lean_unsigned_to_nat(0u);
v___x_2652_ = lean_nat_dec_eq(v_wsIdx_2644_, v___x_2651_);
lean_dec(v_wsIdx_2644_);
if (v___x_2652_ == 0)
{
uint8_t v___x_2653_; 
v___x_2653_ = 1;
v___y_2647_ = v___x_2653_;
goto v___jp_2646_;
}
else
{
uint8_t v___x_2654_; 
v___x_2654_ = 0;
v___y_2647_ = v___x_2654_;
goto v___jp_2646_;
}
v___jp_2646_:
{
lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2649_ = lean_string_dec_eq(v_relDir_2645_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lake_joinRelative(v_relDir_2645_, v___x_2648_);
v___y_2584_ = v___y_2647_;
v___y_2585_ = v___x_2650_;
goto v___jp_2583_;
}
else
{
v___y_2584_ = v___y_2647_;
v___y_2585_ = v_relDir_2645_;
goto v___jp_2583_;
}
}
}
v___jp_2583_:
{
lean_object* v_lakeEnv_2586_; lean_object* v_packages_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v_config_2590_; lean_object* v_dir_2591_; lean_object* v_toWorkspaceConfig_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_lakeEnv_2586_ = lean_ctor_get(v_ws_2578_, 0);
lean_inc_ref(v_lakeEnv_2586_);
v_packages_2587_ = lean_ctor_get(v_ws_2578_, 4);
lean_inc_ref(v_packages_2587_);
lean_dec_ref(v_ws_2578_);
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_array_fget(v_packages_2587_, v___x_2588_);
lean_dec_ref(v_packages_2587_);
v_config_2590_ = lean_ctor_get(v___x_2589_, 6);
lean_inc_ref(v_config_2590_);
v_dir_2591_ = lean_ctor_get(v___x_2589_, 4);
lean_inc_ref(v_dir_2591_);
lean_dec(v___x_2589_);
v_toWorkspaceConfig_2592_ = lean_ctor_get(v_config_2590_, 0);
lean_inc_ref(v_toWorkspaceConfig_2592_);
lean_dec_ref(v_config_2590_);
v___x_2593_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2592_);
v___x_2594_ = l_Lake_Dependency_materialize(v_dep_2580_, v___y_2584_, v_lakeEnv_2586_, v_dir_2591_, v___x_2593_, v___y_2585_, v___y_2577_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2606_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2606_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2606_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v_manifestEntry_2599_; lean_object* v_name_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v_manifestEntry_2599_ = lean_ctor_get(v_a_2595_, 4);
v_name_2600_ = lean_ctor_get(v_manifestEntry_2599_, 0);
lean_inc_ref(v_manifestEntry_2599_);
lean_inc(v_name_2600_);
v___x_2601_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2600_, v_manifestEntry_2599_, v_a_2581_);
v___x_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2602_, 0, v_a_2595_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2602_);
v___x_2604_ = v___x_2597_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_a_2581_);
v_a_2607_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2594_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2594_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2655_, lean_object* v_ws_2656_, lean_object* v_pkg_2657_, lean_object* v_dep_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2655_, v_ws_2656_, v_pkg_2657_, v_dep_2658_, v_a_2659_);
lean_dec_ref(v___y_2655_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2662_, lean_object* v_dep_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_manifestEntry_2666_; lean_object* v_pkgDir_2667_; lean_object* v_name_2668_; lean_object* v_manifestFile_x3f_2669_; lean_object* v___y_2671_; lean_object* v_fst_2672_; lean_object* v_snd_2673_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v_val_2725_; lean_object* v___y_2741_; 
v_manifestEntry_2666_ = lean_ctor_get(v_dep_2663_, 4);
v_pkgDir_2667_ = lean_ctor_get(v_dep_2663_, 0);
v_name_2668_ = lean_ctor_get(v_manifestEntry_2666_, 0);
v_manifestFile_x3f_2669_ = lean_ctor_get(v_manifestEntry_2666_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2669_) == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2667_);
v___x_2762_ = l_Lake_joinRelative(v_pkgDir_2667_, v___x_2761_);
v___y_2741_ = v___x_2762_;
goto v___jp_2740_;
}
else
{
lean_object* v_val_2763_; lean_object* v___x_2764_; 
v_val_2763_ = lean_ctor_get(v_manifestFile_x3f_2669_, 0);
lean_inc(v_val_2763_);
lean_inc_ref(v_pkgDir_2667_);
v___x_2764_ = l_Lake_joinRelative(v_pkgDir_2667_, v_val_2763_);
v___y_2741_ = v___x_2764_;
goto v___jp_2740_;
}
v___jp_2670_:
{
if (lean_obj_tag(v_fst_2672_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2703_; 
lean_inc(v_name_2668_);
lean_dec_ref(v_dep_2663_);
v_a_2674_ = lean_ctor_get(v_fst_2672_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_fst_2672_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2676_ = v_fst_2672_;
v_isShared_2677_ = v_isSharedCheck_2703_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v_fst_2672_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2703_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
if (lean_obj_tag(v_a_2674_) == 11)
{
uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
lean_dec_ref_known(v_a_2674_, 2);
v___x_2678_ = 0;
v___x_2679_ = l_Lean_Name_toString(v_name_2668_, v___x_2678_);
v___x_2680_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2681_ = lean_string_append(v___x_2679_, v___x_2680_);
v___x_2682_ = lean_string_append(v___x_2681_, v___y_2671_);
lean_dec_ref(v___y_2671_);
v___x_2683_ = 2;
v___x_2684_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set_uint8(v___x_2684_, sizeof(void*)*1, v___x_2683_);
v___x_2685_ = lean_apply_2(v___y_2662_, v___x_2684_, lean_box(0));
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
lean_ctor_set(v___x_2686_, 1, v_snd_2673_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2686_);
v___x_2688_ = v___x_2676_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
else
{
uint8_t v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_dec_ref(v___y_2671_);
v___x_2690_ = 0;
v___x_2691_ = l_Lean_Name_toString(v_name_2668_, v___x_2690_);
v___x_2692_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2693_ = lean_string_append(v___x_2691_, v___x_2692_);
v___x_2694_ = lean_io_error_to_string(v_a_2674_);
v___x_2695_ = lean_string_append(v___x_2693_, v___x_2694_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = 2;
v___x_2697_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set_uint8(v___x_2697_, sizeof(void*)*1, v___x_2696_);
v___x_2698_ = lean_apply_2(v___y_2662_, v___x_2697_, lean_box(0));
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
lean_ctor_set(v___x_2699_, 1, v_snd_2673_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2699_);
v___x_2701_ = v___x_2676_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v___y_2671_);
lean_dec_ref(v___y_2662_);
v_a_2704_ = lean_ctor_get(v_fst_2672_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_fst_2672_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2706_ = v_fst_2672_;
v_isShared_2707_ = v_isSharedCheck_2720_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v_fst_2672_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2720_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v_packages_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; 
v_packages_2708_ = lean_ctor_get(v_a_2704_, 3);
lean_inc_ref(v_packages_2708_);
lean_dec(v_a_2704_);
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = lean_array_get_size(v_packages_2708_);
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_nat_dec_lt(v___x_2709_, v___x_2710_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2715_; 
lean_dec_ref(v_packages_2708_);
lean_dec_ref(v_dep_2663_);
v___x_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v_snd_2673_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2713_);
v___x_2715_ = v___x_2706_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
else
{
size_t v___x_2717_; size_t v___x_2718_; lean_object* v___x_2719_; 
lean_del_object(v___x_2706_);
v___x_2717_ = ((size_t)0ULL);
v___x_2718_ = lean_usize_of_nat(v___x_2710_);
v___x_2719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2663_, v_packages_2708_, v___x_2717_, v___x_2718_, v___x_2711_, v_snd_2673_);
lean_dec_ref(v_packages_2708_);
return v___x_2719_;
}
}
}
}
v___jp_2721_:
{
lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = lean_array_get_size(v___y_2724_);
v___x_2727_ = lean_nat_dec_lt(v___y_2723_, v___x_2726_);
if (v___x_2727_ == 0)
{
v___y_2671_ = v___y_2722_;
v_fst_2672_ = v_val_2725_;
v_snd_2673_ = v_a_2664_;
goto v___jp_2670_;
}
else
{
lean_object* v___x_2728_; size_t v___x_2729_; size_t v___x_2730_; lean_object* v___x_2731_; 
v___x_2728_ = lean_box(0);
v___x_2729_ = ((size_t)0ULL);
v___x_2730_ = lean_usize_of_nat(v___x_2726_);
v___x_2731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2724_, v___x_2729_, v___x_2730_, v___x_2728_, v___y_2662_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_dec_ref_known(v___x_2731_, 1);
v___y_2671_ = v___y_2722_;
v_fst_2672_ = v_val_2725_;
v_snd_2673_ = v_a_2664_;
goto v___jp_2670_;
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec_ref(v_val_2725_);
lean_dec_ref(v___y_2722_);
lean_dec(v_a_2664_);
lean_dec_ref(v_dep_2663_);
lean_dec_ref(v___y_2662_);
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
v___jp_2740_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2741_);
v___x_2744_ = l_Lake_Manifest_load(v___y_2741_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 1);
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
v___y_2722_ = v___y_2741_;
v___y_2723_ = v___x_2742_;
v___y_2724_ = v___x_2743_;
v_val_2725_ = v___x_2750_;
goto v___jp_2721_;
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
v_a_2753_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2744_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2744_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
lean_ctor_set_tag(v___x_2755_, 0);
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
v___y_2722_ = v___y_2741_;
v___y_2723_ = v___x_2742_;
v___y_2724_ = v___x_2743_;
v_val_2725_ = v___x_2758_;
goto v___jp_2721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2765_, lean_object* v_dep_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2765_, v_dep_2766_, v_a_2767_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2774_, v___y_2772_, v___y_2770_, v___y_2771_, v___y_2773_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v_fst_2778_; lean_object* v_snd_2779_; lean_object* v___x_2780_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v_fst_2778_ = lean_ctor_get(v_a_2777_, 0);
lean_inc_n(v_fst_2778_, 2);
v_snd_2779_ = lean_ctor_get(v_a_2777_, 1);
lean_inc(v_snd_2779_);
lean_dec(v_a_2777_);
v___x_2780_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2774_, v_fst_2778_, v_snd_2779_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2797_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2797_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2797_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v_snd_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2795_; 
v_snd_2785_ = lean_ctor_get(v_a_2781_, 1);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_a_2781_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; 
v_unused_2796_ = lean_ctor_get(v_a_2781_, 0);
lean_dec(v_unused_2796_);
v___x_2787_ = v_a_2781_;
v_isShared_2788_ = v_isSharedCheck_2795_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_snd_2785_);
lean_dec(v_a_2781_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2795_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v_fst_2778_);
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_fst_2778_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_snd_2785_);
v___x_2790_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2792_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2790_);
v___x_2792_ = v___x_2783_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec(v_fst_2778_);
v_a_2798_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2780_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2780_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_dec_ref(v___y_2774_);
return v___x_2776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(lean_object* v_toUpdate_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v_entries_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___y_2821_; 
if (lean_obj_tag(v_toUpdate_2813_) == 0)
{
lean_object* v_depConfigs_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v_depConfigs_2863_ = lean_ctor_get(v___x_2814_, 12);
v___x_2864_ = l_Lean_NameSet_empty;
v___x_2865_ = lean_array_get_size(v_depConfigs_2863_);
v___x_2866_ = lean_nat_dec_lt(v___x_2815_, v___x_2865_);
if (v___x_2866_ == 0)
{
v___y_2821_ = v___x_2864_;
goto v___jp_2820_;
}
else
{
size_t v___x_2867_; size_t v___x_2868_; lean_object* v___x_2869_; 
v___x_2867_ = ((size_t)0ULL);
v___x_2868_ = lean_usize_of_nat(v___x_2865_);
v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_2863_, v___x_2867_, v___x_2868_, v___x_2864_);
v___y_2821_ = v___x_2869_;
goto v___jp_2820_;
}
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2870_ = lean_box(0);
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
lean_ctor_set(v___x_2871_, 1, v___y_2817_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
v___jp_2820_:
{
size_t v_sz_2822_; size_t v___x_2823_; lean_object* v___x_2824_; 
v_sz_2822_ = lean_array_size(v_entries_2816_);
v___x_2823_ = ((size_t)0ULL);
v___x_2824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_entries_2816_, v_sz_2822_, v___x_2823_, v___y_2821_, v___y_2817_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v_fst_2826_; lean_object* v_snd_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
v_fst_2826_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_fst_2826_);
v_snd_2827_ = lean_ctor_get(v_a_2825_, 1);
lean_inc(v_snd_2827_);
lean_dec(v_a_2825_);
v___x_2828_ = lean_box(0);
v___x_2829_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_2826_, v___x_2828_, v_toUpdate_2813_, v_snd_2827_, v___y_2818_);
lean_dec(v_fst_2826_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2846_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2846_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2846_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v_snd_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2844_; 
v_snd_2834_ = lean_ctor_get(v_a_2830_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_a_2830_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v_a_2830_, 0);
lean_dec(v_unused_2845_);
v___x_2836_ = v_a_2830_;
v_isShared_2837_ = v_isSharedCheck_2844_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_snd_2834_);
lean_dec(v_a_2830_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2844_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2828_);
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2828_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_snd_2834_);
v___x_2839_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2841_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v___x_2839_);
v___x_2841_ = v___x_2832_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
v_a_2847_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2829_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2829_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_toUpdate_2813_);
v_a_2855_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2824_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2824_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0___boxed(lean_object* v_toUpdate_2873_, lean_object* v___x_2874_, lean_object* v___x_2875_, lean_object* v_entries_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2873_, v___x_2874_, v___x_2875_, v_entries_2876_, v___y_2877_, v___y_2878_);
lean_dec_ref(v___y_2878_);
lean_dec_ref(v_entries_2876_);
lean_dec(v___x_2875_);
lean_dec_ref(v___x_2874_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2881_, lean_object* v_ws_2882_, lean_object* v_toUpdate_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v___y_2887_; lean_object* v___y_2892_; lean_object* v_fst_2893_; lean_object* v_snd_2894_; lean_object* v_packages_2913_; lean_object* v___x_2914_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v_val_2919_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___x_2955_; lean_object* v_baseName_2956_; lean_object* v_dir_2957_; lean_object* v_config_2958_; lean_object* v_relManifestFile_2959_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; uint8_t v_fst_2964_; lean_object* v_snd_2965_; lean_object* v_packagesDir_x3f_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; uint8_t v___x_3009_; lean_object* v_rootName_3010_; lean_object* v_fst_3012_; lean_object* v_snd_3013_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v_val_3080_; lean_object* v___x_3094_; 
v_packages_2913_ = lean_ctor_get(v_ws_2882_, 4);
v___x_2914_ = lean_unsigned_to_nat(0u);
v___x_2955_ = lean_array_fget_borrowed(v_packages_2913_, v___x_2914_);
v_baseName_2956_ = lean_ctor_get(v___x_2955_, 1);
v_dir_2957_ = lean_ctor_get(v___x_2955_, 4);
v_config_2958_ = lean_ctor_get(v___x_2955_, 6);
v_relManifestFile_2959_ = lean_ctor_get(v___x_2955_, 9);
v___x_3009_ = 0;
lean_inc(v_baseName_2956_);
v_rootName_3010_ = l_Lean_Name_toString(v_baseName_2956_, v___x_3009_);
lean_inc_ref(v_relManifestFile_2959_);
lean_inc_ref(v_dir_2957_);
v___x_3077_ = l_Lake_joinRelative(v_dir_2957_, v_relManifestFile_2959_);
v___x_3078_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_3094_ = l_Lake_Manifest_load(v___x_3077_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set_tag(v___x_3097_, 1);
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
v_val_3080_ = v___x_3100_;
goto v___jp_3079_;
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_a_3103_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3094_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3094_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set_tag(v___x_3105_, 0);
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
v_val_3080_ = v___x_3108_;
goto v___jp_3079_;
}
}
}
v___jp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
lean_ctor_set(v___x_2889_, 1, v___y_2887_);
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
v___jp_2891_:
{
if (lean_obj_tag(v_fst_2893_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_snd_2894_);
v_a_2895_ = lean_ctor_get(v_fst_2893_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_fst_2893_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2897_ = v_fst_2893_;
v_isShared_2898_ = v_isSharedCheck_2909_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v_fst_2893_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2909_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2899_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2900_ = lean_io_error_to_string(v_a_2895_);
v___x_2901_ = lean_string_append(v___x_2899_, v___x_2900_);
lean_dec_ref(v___x_2900_);
v___x_2902_ = 3;
v___x_2903_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set_uint8(v___x_2903_, sizeof(void*)*1, v___x_2902_);
lean_inc_ref(v___y_2892_);
v___x_2904_ = lean_apply_2(v___y_2892_, v___x_2903_, lean_box(0));
v___x_2905_ = lean_box(0);
if (v_isShared_2898_ == 0)
{
lean_ctor_set_tag(v___x_2897_, 1);
lean_ctor_set(v___x_2897_, 0, v___x_2905_);
v___x_2907_ = v___x_2897_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
lean_dec_ref(v_fst_2893_);
v___x_2910_ = lean_box(0);
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
lean_ctor_set(v___x_2911_, 1, v_snd_2894_);
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
return v___x_2912_;
}
}
v___jp_2915_:
{
lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2920_ = lean_array_get_size(v___y_2917_);
v___x_2921_ = lean_nat_dec_lt(v___x_2914_, v___x_2920_);
if (v___x_2921_ == 0)
{
v___y_2892_ = v___y_2918_;
v_fst_2893_ = v_val_2919_;
v_snd_2894_ = v___y_2916_;
goto v___jp_2891_;
}
else
{
lean_object* v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v___x_2922_ = lean_box(0);
v___x_2923_ = ((size_t)0ULL);
v___x_2924_ = lean_usize_of_nat(v___x_2920_);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2917_, v___x_2923_, v___x_2924_, v___x_2922_, v___y_2918_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_dec_ref_known(v___x_2925_, 1);
v___y_2892_ = v___y_2918_;
v_fst_2893_ = v_val_2919_;
v_snd_2894_ = v___y_2916_;
goto v___jp_2891_;
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref(v_val_2919_);
lean_dec(v___y_2916_);
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2925_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2925_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
v___jp_2934_:
{
if (lean_obj_tag(v___y_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
v_a_2939_ = lean_ctor_get(v___y_2938_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___y_2938_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___y_2938_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___y_2938_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 1);
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
v___y_2916_ = v___y_2935_;
v___y_2917_ = v___y_2936_;
v___y_2918_ = v___y_2937_;
v_val_2919_ = v___x_2944_;
goto v___jp_2915_;
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
v_a_2947_ = lean_ctor_get(v___y_2938_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___y_2938_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___y_2938_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___y_2938_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set_tag(v___x_2949_, 0);
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
v___y_2916_ = v___y_2935_;
v___y_2917_ = v___y_2936_;
v___y_2918_ = v___y_2937_;
v_val_2919_ = v___x_2952_;
goto v___jp_2915_;
}
}
}
}
v___jp_2960_:
{
lean_object* v_toWorkspaceConfig_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; 
v_toWorkspaceConfig_2966_ = lean_ctor_get(v_config_2958_, 0);
v___x_2967_ = l_System_FilePath_normalize(v___y_2961_);
lean_inc_ref(v_toWorkspaceConfig_2966_);
v___x_2968_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2966_);
lean_inc_ref(v___x_2968_);
v___x_2969_ = l_System_FilePath_normalize(v___x_2968_);
v___x_2970_ = lean_string_dec_eq(v___x_2967_, v___x_2969_);
lean_dec_ref(v___x_2969_);
lean_dec_ref(v___x_2967_);
if (v___x_2970_ == 0)
{
if (v_fst_2964_ == 0)
{
lean_dec_ref(v___x_2968_);
lean_dec_ref(v___y_2962_);
v___y_2887_ = v_snd_2965_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2971_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2972_ = lean_string_append(v___x_2971_, v___y_2962_);
v___x_2973_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2974_ = lean_string_append(v___x_2972_, v___x_2973_);
lean_inc_ref(v_dir_2957_);
v___x_2975_ = l_Lake_joinRelative(v_dir_2957_, v___x_2968_);
v___x_2976_ = lean_string_append(v___x_2974_, v___x_2975_);
v___x_2977_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2978_ = lean_string_append(v___x_2976_, v___x_2977_);
v___x_2979_ = 1;
v___x_2980_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2980_, 0, v___x_2978_);
lean_ctor_set_uint8(v___x_2980_, sizeof(void*)*1, v___x_2979_);
lean_inc_ref(v___y_2963_);
v___x_2981_ = lean_apply_2(v___y_2963_, v___x_2980_, lean_box(0));
v___x_2982_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2975_);
v___x_2983_ = l_Lake_createParentDirs(v___x_2975_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v___x_2984_; 
lean_dec_ref_known(v___x_2983_, 1);
v___x_2984_ = lean_io_rename(v___y_2962_, v___x_2975_);
lean_dec_ref(v___x_2975_);
lean_dec_ref(v___y_2962_);
v___y_2935_ = v_snd_2965_;
v___y_2936_ = v___x_2982_;
v___y_2937_ = v___y_2963_;
v___y_2938_ = v___x_2984_;
goto v___jp_2934_;
}
else
{
lean_dec_ref(v___x_2975_);
lean_dec_ref(v___y_2962_);
v___y_2935_ = v_snd_2965_;
v___y_2936_ = v___x_2982_;
v___y_2937_ = v___y_2963_;
v___y_2938_ = v___x_2983_;
goto v___jp_2934_;
}
}
}
else
{
lean_dec_ref(v___x_2968_);
lean_dec_ref(v___y_2962_);
v___y_2887_ = v_snd_2965_;
goto v___jp_2886_;
}
}
v___jp_2985_:
{
if (lean_obj_tag(v_packagesDir_x3f_2986_) == 1)
{
lean_object* v_val_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; uint8_t v___x_2992_; uint8_t v___x_2993_; 
v_val_2989_ = lean_ctor_get(v_packagesDir_x3f_2986_, 0);
lean_inc_n(v_val_2989_, 2);
lean_dec_ref_known(v_packagesDir_x3f_2986_, 1);
lean_inc_ref(v_dir_2957_);
v___x_2990_ = l_Lake_joinRelative(v_dir_2957_, v_val_2989_);
v___x_2991_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2992_ = l_System_FilePath_pathExists(v___x_2990_);
v___x_2993_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2993_ == 0)
{
v___y_2961_ = v_val_2989_;
v___y_2962_ = v___x_2990_;
v___y_2963_ = v___y_2988_;
v_fst_2964_ = v___x_2992_;
v_snd_2965_ = v___y_2987_;
goto v___jp_2960_;
}
else
{
lean_object* v___x_2994_; size_t v___x_2995_; size_t v___x_2996_; lean_object* v___x_2997_; 
v___x_2994_ = lean_box(0);
v___x_2995_ = ((size_t)0ULL);
v___x_2996_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_2997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_2991_, v___x_2995_, v___x_2996_, v___x_2994_, v___y_2988_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_dec_ref_known(v___x_2997_, 1);
v___y_2961_ = v_val_2989_;
v___y_2962_ = v___x_2990_;
v___y_2963_ = v___y_2988_;
v_fst_2964_ = v___x_2992_;
v_snd_2965_ = v___y_2987_;
goto v___jp_2960_;
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v___x_2990_);
lean_dec(v_val_2989_);
lean_dec(v___y_2987_);
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_dec(v_packagesDir_x3f_2986_);
v___x_3006_ = lean_box(0);
v___x_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
lean_ctor_set(v___x_3007_, 1, v___y_2987_);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
v___jp_3011_:
{
if (lean_obj_tag(v_fst_3012_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3061_; 
v_a_3014_ = lean_ctor_get(v_fst_3012_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_fst_3012_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3016_ = v_fst_3012_;
v_isShared_3017_ = v_isSharedCheck_3061_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v_fst_3012_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3061_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
if (lean_obj_tag(v_a_3014_) == 11)
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_dec_ref_known(v_a_3014_, 2);
lean_del_object(v___x_3016_);
v___x_3018_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_3019_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2883_, v___x_2955_, v___x_2914_, v___x_3018_, v_snd_3013_, v_a_2881_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3041_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3041_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3041_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v_snd_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3039_; 
v_snd_3024_ = lean_ctor_get(v_a_3020_, 1);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_a_3020_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v_a_3020_, 0);
lean_dec(v_unused_3040_);
v___x_3026_ = v_a_3020_;
v_isShared_3027_ = v_isSharedCheck_3039_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_snd_3024_);
lean_dec(v_a_3020_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3039_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3028_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8));
v___x_3029_ = lean_string_append(v_rootName_3010_, v___x_3028_);
v___x_3030_ = 1;
v___x_3031_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set_uint8(v___x_3031_, sizeof(void*)*1, v___x_3030_);
lean_inc_ref(v_a_2881_);
v___x_3032_ = lean_apply_2(v_a_2881_, v___x_3031_, lean_box(0));
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3032_);
v___x_3034_ = v___x_3026_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_snd_3024_);
v___x_3034_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3036_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3034_);
v___x_3036_ = v___x_3022_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_3010_);
return v___x_3019_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2883_) == 0)
{
lean_object* v___x_3042_; uint8_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
lean_dec_ref_known(v_toUpdate_2883_, 5);
lean_dec(v_snd_3013_);
lean_dec_ref(v_rootName_3010_);
v___x_3042_ = lean_io_error_to_string(v_a_3014_);
v___x_3043_ = 3;
v___x_3044_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*1, v___x_3043_);
lean_inc_ref(v_a_2881_);
v___x_3045_ = lean_apply_2(v_a_2881_, v___x_3044_, lean_box(0));
v___x_3046_ = lean_box(0);
if (v_isShared_3017_ == 0)
{
lean_ctor_set_tag(v___x_3016_, 1);
lean_ctor_set(v___x_3016_, 0, v___x_3046_);
v___x_3048_ = v___x_3016_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v___x_3050_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_3051_ = lean_string_append(v_rootName_3010_, v___x_3050_);
v___x_3052_ = lean_io_error_to_string(v_a_3014_);
v___x_3053_ = lean_string_append(v___x_3051_, v___x_3052_);
lean_dec_ref(v___x_3052_);
v___x_3054_ = 2;
v___x_3055_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3055_, 0, v___x_3053_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*1, v___x_3054_);
lean_inc_ref(v_a_2881_);
v___x_3056_ = lean_apply_2(v_a_2881_, v___x_3055_, lean_box(0));
v___x_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
lean_ctor_set(v___x_3057_, 1, v_snd_3013_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3057_);
v___x_3059_ = v___x_3016_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3057_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v_packagesDir_x3f_3063_; lean_object* v_packages_3064_; lean_object* v___x_3065_; 
lean_dec_ref(v_rootName_3010_);
v_a_3062_ = lean_ctor_get(v_fst_3012_, 0);
lean_inc(v_a_3062_);
lean_dec_ref_known(v_fst_3012_, 1);
v_packagesDir_x3f_3063_ = lean_ctor_get(v_a_3062_, 2);
lean_inc(v_packagesDir_x3f_3063_);
v_packages_3064_ = lean_ctor_get(v_a_3062_, 3);
lean_inc_ref(v_packages_3064_);
lean_dec(v_a_3062_);
lean_inc(v_toUpdate_2883_);
v___x_3065_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2883_, v___x_2955_, v___x_2914_, v_packages_3064_, v_snd_3013_, v_a_2881_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
if (lean_obj_tag(v_toUpdate_2883_) == 0)
{
lean_object* v_snd_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v_snd_3067_ = lean_ctor_get(v_a_3066_, 1);
lean_inc(v_snd_3067_);
lean_dec(v_a_3066_);
v___x_3068_ = lean_array_get_size(v_packages_3064_);
v___x_3069_ = lean_nat_dec_lt(v___x_2914_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_dec_ref_known(v_toUpdate_2883_, 5);
lean_dec_ref(v_packages_3064_);
v_packagesDir_x3f_2986_ = v_packagesDir_x3f_3063_;
v___y_2987_ = v_snd_3067_;
v___y_2988_ = v_a_2881_;
goto v___jp_2985_;
}
else
{
lean_object* v___x_3070_; size_t v___x_3071_; size_t v___x_3072_; lean_object* v___x_3073_; 
v___x_3070_ = lean_box(0);
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = lean_usize_of_nat(v___x_3068_);
v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_2883_, v_packages_3064_, v___x_3071_, v___x_3072_, v___x_3070_, v_snd_3067_);
lean_dec_ref(v_packages_3064_);
lean_dec_ref_known(v_toUpdate_2883_, 5);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v_snd_3075_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___x_3073_, 1);
v_snd_3075_ = lean_ctor_get(v_a_3074_, 1);
lean_inc(v_snd_3075_);
lean_dec(v_a_3074_);
v_packagesDir_x3f_2986_ = v_packagesDir_x3f_3063_;
v___y_2987_ = v_snd_3075_;
v___y_2988_ = v_a_2881_;
goto v___jp_2985_;
}
else
{
lean_dec(v_packagesDir_x3f_3063_);
return v___x_3073_;
}
}
}
else
{
lean_object* v_snd_3076_; 
lean_dec_ref(v_packages_3064_);
v_snd_3076_ = lean_ctor_get(v_a_3066_, 1);
lean_inc(v_snd_3076_);
lean_dec(v_a_3066_);
v_packagesDir_x3f_2986_ = v_packagesDir_x3f_3063_;
v___y_2987_ = v_snd_3076_;
v___y_2988_ = v_a_2881_;
goto v___jp_2985_;
}
}
else
{
lean_dec_ref(v_packages_3064_);
lean_dec(v_packagesDir_x3f_3063_);
lean_dec(v_toUpdate_2883_);
return v___x_3065_;
}
}
}
v___jp_3079_:
{
uint8_t v___x_3081_; 
v___x_3081_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_3081_ == 0)
{
v_fst_3012_ = v_val_3080_;
v_snd_3013_ = v_a_2884_;
goto v___jp_3011_;
}
else
{
lean_object* v___x_3082_; size_t v___x_3083_; size_t v___x_3084_; lean_object* v___x_3085_; 
v___x_3082_ = lean_box(0);
v___x_3083_ = ((size_t)0ULL);
v___x_3084_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_3085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_3078_, v___x_3083_, v___x_3084_, v___x_3082_, v_a_2881_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_dec_ref_known(v___x_3085_, 1);
v_fst_3012_ = v_val_3080_;
v_snd_3013_ = v_a_2884_;
goto v___jp_3011_;
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref(v_val_3080_);
lean_dec_ref(v_rootName_3010_);
lean_dec(v_a_2884_);
lean_dec(v_toUpdate_2883_);
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_3111_, lean_object* v_ws_3112_, lean_object* v_toUpdate_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_3111_, v_ws_3112_, v_toUpdate_3113_, v_a_3114_);
lean_dec_ref(v_ws_3112_);
lean_dec_ref(v_a_3111_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_a_3117_, lean_object* v_ws_3118_, lean_object* v_rootDeps_3119_){
_start:
{
lean_object* v___y_3122_; lean_object* v___y_3128_; uint8_t v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; uint8_t v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3150_; lean_object* v___y_3151_; uint8_t v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v_lakeEnv_3158_; lean_object* v_lakeArgs_x3f_3159_; lean_object* v_packages_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_baseName_3163_; lean_object* v_dir_3164_; lean_object* v_config_3165_; lean_object* v___x_3166_; lean_object* v_rootToolchainFile_3167_; uint8_t v___y_3169_; lean_object* v___y_3170_; uint8_t v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3315_; uint8_t v___y_3316_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_lakeEnv_3158_ = lean_ctor_get(v_ws_3118_, 0);
lean_inc_ref(v_lakeEnv_3158_);
v_lakeArgs_x3f_3159_ = lean_ctor_get(v_ws_3118_, 3);
lean_inc(v_lakeArgs_x3f_3159_);
v_packages_3160_ = lean_ctor_get(v_ws_3118_, 4);
lean_inc_ref(v_packages_3160_);
lean_dec_ref(v_ws_3118_);
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = lean_array_fget(v_packages_3160_, v___x_3161_);
lean_dec_ref(v_packages_3160_);
v_baseName_3163_ = lean_ctor_get(v___x_3162_, 1);
lean_inc(v_baseName_3163_);
v_dir_3164_ = lean_ctor_get(v___x_3162_, 4);
lean_inc_ref_n(v_dir_3164_, 3);
v_config_3165_ = lean_ctor_get(v___x_3162_, 6);
lean_inc_ref(v_config_3165_);
lean_dec(v___x_3162_);
v___x_3166_ = l_Lake_toolchainFileName;
v_rootToolchainFile_3167_ = l_Lake_joinRelative(v_dir_3164_, v___x_3166_);
v___x_3320_ = l_System_FilePath_join(v_dir_3164_, v___x_3166_);
v___x_3321_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3320_);
lean_dec_ref(v___x_3320_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3374_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3374_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3374_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_src_3327_; lean_object* v_tc_x3f_3328_; lean_object* v_clashes_3329_; uint8_t v_fixed_3330_; uint8_t v_fixedToolchain_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v_fixedToolchain_3353_ = lean_ctor_get_uint8(v_config_3165_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_3165_);
v___x_3354_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___x_3355_ = lean_array_get_size(v_rootDeps_3119_);
v___x_3356_ = lean_nat_dec_lt(v___x_3161_, v___x_3355_);
if (v___x_3356_ == 0)
{
lean_dec_ref(v_dir_3164_);
lean_inc(v_a_3322_);
v_src_3327_ = v_baseName_3163_;
v_tc_x3f_3328_ = v_a_3322_;
v_clashes_3329_ = v___x_3354_;
v_fixed_3330_ = v_fixedToolchain_3353_;
goto v___jp_3326_;
}
else
{
lean_object* v___x_3357_; size_t v___x_3358_; size_t v___x_3359_; lean_object* v___x_3360_; 
lean_inc(v_a_3322_);
v___x_3357_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3357_, 0, v_baseName_3163_);
lean_ctor_set(v___x_3357_, 1, v_a_3322_);
lean_ctor_set(v___x_3357_, 2, v___x_3354_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*3, v_fixedToolchain_3353_);
v___x_3358_ = ((size_t)0ULL);
v___x_3359_ = lean_usize_of_nat(v___x_3355_);
v___x_3360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3164_, v_rootDeps_3119_, v___x_3358_, v___x_3359_, v___x_3357_, v_a_3117_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v_src_3362_; lean_object* v_tc_x3f_3363_; lean_object* v_clashes_3364_; uint8_t v_fixed_3365_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___x_3360_, 1);
v_src_3362_ = lean_ctor_get(v_a_3361_, 0);
lean_inc(v_src_3362_);
v_tc_x3f_3363_ = lean_ctor_get(v_a_3361_, 1);
lean_inc(v_tc_x3f_3363_);
v_clashes_3364_ = lean_ctor_get(v_a_3361_, 2);
lean_inc_ref(v_clashes_3364_);
v_fixed_3365_ = lean_ctor_get_uint8(v_a_3361_, sizeof(void*)*3);
lean_dec(v_a_3361_);
v_src_3327_ = v_src_3362_;
v_tc_x3f_3328_ = v_tc_x3f_3363_;
v_clashes_3329_ = v_clashes_3364_;
v_fixed_3330_ = v_fixed_3365_;
goto v___jp_3326_;
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_del_object(v___x_3324_);
lean_dec(v_a_3322_);
lean_dec_ref(v_rootToolchainFile_3167_);
lean_dec(v_lakeArgs_x3f_3159_);
lean_dec_ref(v_lakeEnv_3158_);
v_a_3366_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3360_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3360_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
v___jp_3326_:
{
lean_object* v___x_3331_; uint8_t v___x_3332_; 
v___x_3331_ = lean_array_get_size(v_clashes_3329_);
v___x_3332_ = lean_nat_dec_lt(v___x_3161_, v___x_3331_);
if (v___x_3332_ == 0)
{
lean_dec_ref(v_clashes_3329_);
lean_dec(v_src_3327_);
if (lean_obj_tag(v_tc_x3f_3328_) == 1)
{
if (lean_obj_tag(v_a_3322_) == 0)
{
lean_object* v_val_3333_; 
lean_del_object(v___x_3324_);
v_val_3333_ = lean_ctor_get(v_tc_x3f_3328_, 0);
lean_inc(v_val_3333_);
lean_dec_ref_known(v_tc_x3f_3328_, 1);
v___y_3315_ = v_val_3333_;
v___y_3316_ = v___x_3332_;
goto v___jp_3314_;
}
else
{
lean_object* v_val_3334_; lean_object* v_val_3335_; uint8_t v___x_3336_; 
v_val_3334_ = lean_ctor_get(v_tc_x3f_3328_, 0);
lean_inc_n(v_val_3334_, 2);
lean_dec_ref_known(v_tc_x3f_3328_, 1);
v_val_3335_ = lean_ctor_get(v_a_3322_, 0);
lean_inc(v_val_3335_);
lean_dec_ref_known(v_a_3322_, 1);
v___x_3336_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3335_, v_val_3334_);
if (v___x_3336_ == 0)
{
lean_del_object(v___x_3324_);
v___y_3315_ = v_val_3334_;
v___y_3316_ = v___x_3336_;
goto v___jp_3314_;
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3341_; 
lean_dec(v_val_3334_);
lean_dec_ref(v_rootToolchainFile_3167_);
lean_dec(v_lakeArgs_x3f_3159_);
lean_dec_ref(v_lakeEnv_3158_);
v___x_3337_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15));
lean_inc_ref(v_a_3117_);
v___x_3338_ = lean_apply_2(v_a_3117_, v___x_3337_, lean_box(0));
v___x_3339_ = lean_box(0);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3339_);
v___x_3341_ = v___x_3324_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
lean_dec(v_tc_x3f_3328_);
lean_dec(v_a_3322_);
lean_dec_ref(v_rootToolchainFile_3167_);
lean_dec(v_lakeArgs_x3f_3159_);
lean_dec_ref(v_lakeEnv_3158_);
v___x_3343_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17));
lean_inc_ref(v_a_3117_);
v___x_3344_ = lean_apply_2(v_a_3117_, v___x_3343_, lean_box(0));
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3344_);
v___x_3346_ = v___x_3324_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
else
{
lean_del_object(v___x_3324_);
lean_dec(v_a_3322_);
lean_dec_ref(v_rootToolchainFile_3167_);
lean_dec(v_lakeArgs_x3f_3159_);
lean_dec_ref(v_lakeEnv_3158_);
if (lean_obj_tag(v_tc_x3f_3328_) == 1)
{
if (v_fixed_3330_ == 0)
{
lean_object* v_val_3348_; lean_object* v___x_3349_; 
v_val_3348_ = lean_ctor_get(v_tc_x3f_3328_, 0);
lean_inc(v_val_3348_);
lean_dec_ref_known(v_tc_x3f_3328_, 1);
v___x_3349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3150_ = v_val_3348_;
v___y_3151_ = v___x_3331_;
v___y_3152_ = v___x_3332_;
v___y_3153_ = v_src_3327_;
v___y_3154_ = v_clashes_3329_;
v___y_3155_ = v___x_3349_;
goto v___jp_3149_;
}
else
{
lean_object* v_val_3350_; lean_object* v___x_3351_; 
v_val_3350_ = lean_ctor_get(v_tc_x3f_3328_, 0);
lean_inc(v_val_3350_);
lean_dec_ref_known(v_tc_x3f_3328_, 1);
v___x_3351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3150_ = v_val_3350_;
v___y_3151_ = v___x_3331_;
v___y_3152_ = v___x_3332_;
v___y_3153_ = v_src_3327_;
v___y_3154_ = v_clashes_3329_;
v___y_3155_ = v___x_3351_;
goto v___jp_3149_;
}
}
else
{
lean_object* v___x_3352_; 
lean_dec(v_tc_x3f_3328_);
lean_dec(v_src_3327_);
v___x_3352_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
v___y_3128_ = v___x_3331_;
v___y_3129_ = v___x_3332_;
v___y_3130_ = v_clashes_3329_;
v___y_3131_ = v___x_3352_;
goto v___jp_3127_;
}
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3387_; 
lean_dec_ref(v_rootToolchainFile_3167_);
lean_dec_ref(v_config_3165_);
lean_dec_ref(v_dir_3164_);
lean_dec(v_baseName_3163_);
lean_dec(v_lakeArgs_x3f_3159_);
lean_dec_ref(v_lakeEnv_3158_);
v_a_3375_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3377_ = v___x_3321_;
v_isShared_3378_ = v_isSharedCheck_3387_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3321_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3387_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3379_; uint8_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3379_ = lean_io_error_to_string(v_a_3375_);
v___x_3380_ = 3;
v___x_3381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3381_, 0, v___x_3379_);
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*1, v___x_3380_);
lean_inc_ref(v_a_3117_);
v___x_3382_ = lean_apply_2(v_a_3117_, v___x_3381_, lean_box(0));
v___x_3383_ = lean_box(0);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v___x_3383_);
v___x_3385_ = v___x_3377_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
v___jp_3121_:
{
uint8_t v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3123_ = 2;
v___x_3124_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3124_, 0, v___y_3122_);
lean_ctor_set_uint8(v___x_3124_, sizeof(void*)*1, v___x_3123_);
lean_inc_ref(v_a_3117_);
v___x_3125_ = lean_apply_2(v_a_3117_, v___x_3124_, lean_box(0));
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
return v___x_3126_;
}
v___jp_3127_:
{
if (v___y_3129_ == 0)
{
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3128_);
v___y_3122_ = v___y_3131_;
goto v___jp_3121_;
}
else
{
size_t v___x_3132_; size_t v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = ((size_t)0ULL);
v___x_3133_ = lean_usize_of_nat(v___y_3128_);
v___x_3134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3128_, v___y_3130_, v___x_3132_, v___x_3133_, v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3128_);
v___y_3122_ = v___x_3134_;
goto v___jp_3121_;
}
}
v___jp_3135_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_inc_ref(v___y_3137_);
v___x_3143_ = lean_string_append(v___y_3137_, v___y_3142_);
lean_dec_ref(v___y_3142_);
v___x_3144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3145_ = lean_string_append(v___x_3143_, v___x_3144_);
v___x_3146_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3141_, v___y_3139_);
v___x_3147_ = lean_string_append(v___x_3145_, v___x_3146_);
lean_dec_ref(v___x_3146_);
v___x_3148_ = lean_string_append(v___x_3147_, v___y_3136_);
v___y_3128_ = v___y_3138_;
v___y_3129_ = v___y_3139_;
v___y_3130_ = v___y_3140_;
v___y_3131_ = v___x_3148_;
goto v___jp_3127_;
}
v___jp_3149_:
{
lean_object* v___x_3156_; lean_object* v_toString_3157_; 
v___x_3156_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_3157_ = lean_ctor_get(v___y_3150_, 0);
lean_inc_ref(v_toString_3157_);
lean_dec_ref(v___y_3150_);
v___y_3136_ = v___y_3155_;
v___y_3137_ = v___x_3156_;
v___y_3138_ = v___y_3151_;
v___y_3139_ = v___y_3152_;
v___y_3140_ = v___y_3154_;
v___y_3141_ = v___y_3153_;
v___y_3142_ = v_toString_3157_;
goto v___jp_3135_;
}
v___jp_3168_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_inc_ref(v___y_3170_);
v___x_3173_ = lean_string_append(v___y_3170_, v___y_3172_);
v___x_3174_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_3175_ = lean_string_append(v___x_3173_, v___x_3174_);
v___x_3176_ = 1;
v___x_3177_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set_uint8(v___x_3177_, sizeof(void*)*1, v___x_3176_);
lean_inc_ref(v_a_3117_);
v___x_3178_ = lean_apply_2(v_a_3117_, v___x_3177_, lean_box(0));
v___x_3179_ = l_IO_FS_writeFile(v_rootToolchainFile_3167_, v___y_3172_);
lean_dec_ref(v_rootToolchainFile_3167_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_dec_ref_known(v___x_3179_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_3159_) == 1)
{
lean_object* v_elan_x3f_3180_; 
v_elan_x3f_3180_ = lean_ctor_get(v_lakeEnv_3158_, 2);
if (lean_obj_tag(v_elan_x3f_3180_) == 1)
{
lean_object* v_val_3181_; lean_object* v_val_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v_elan_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_val_3181_ = lean_ctor_get(v_lakeArgs_x3f_3159_, 0);
lean_inc(v_val_3181_);
lean_dec_ref_known(v_lakeArgs_x3f_3159_, 1);
v_val_3182_ = lean_ctor_get(v_elan_x3f_3180_, 0);
v___x_3183_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_3117_);
v___x_3184_ = lean_apply_2(v_a_3117_, v___x_3183_, lean_box(0));
v___x_3185_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_3186_ = lean_ctor_get(v_val_3182_, 1);
lean_inc_ref(v_elan_3186_);
v___x_3187_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_3188_ = lean_unsigned_to_nat(4u);
v___x_3189_ = lean_mk_empty_array_with_capacity(v___x_3188_);
lean_dec_ref(v___x_3189_);
v___x_3190_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_3191_ = lean_array_push(v___x_3190_, v___y_3172_);
v___x_3192_ = lean_array_push(v___x_3191_, v___x_3187_);
v___x_3193_ = l_Array_append___redArg(v___x_3192_, v_val_3181_);
lean_dec(v_val_3181_);
v___x_3194_ = lean_box(0);
v___x_3195_ = l_Lake_Env_noToolchainVars(v_lakeEnv_3158_);
v___x_3196_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3196_, 0, v___x_3185_);
lean_ctor_set(v___x_3196_, 1, v_elan_3186_);
lean_ctor_set(v___x_3196_, 2, v___x_3193_);
lean_ctor_set(v___x_3196_, 3, v___x_3194_);
lean_ctor_set(v___x_3196_, 4, v___x_3195_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*5, v___y_3171_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*5 + 1, v___y_3169_);
v___x_3197_ = lean_io_process_spawn(v___x_3196_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3199_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3197_, 1);
v___x_3199_ = lean_io_process_child_wait(v___x_3185_, v_a_3198_);
lean_dec(v_a_3198_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; uint32_t v___x_3201_; uint8_t v___x_3202_; lean_object* v___x_3203_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = lean_unbox_uint32(v_a_3200_);
lean_dec(v_a_3200_);
v___x_3202_ = lean_uint32_to_uint8(v___x_3201_);
v___x_3203_ = lean_io_exit(v___x_3202_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3224_; 
v_a_3212_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3214_ = v___x_3203_;
v_isShared_3215_ = v_isSharedCheck_3224_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3203_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3224_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; uint8_t v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3216_ = lean_io_error_to_string(v_a_3212_);
v___x_3217_ = 3;
v___x_3218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*1, v___x_3217_);
lean_inc_ref(v_a_3117_);
v___x_3219_ = lean_apply_2(v_a_3117_, v___x_3218_, lean_box(0));
v___x_3220_ = lean_box(0);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v___x_3220_);
v___x_3222_ = v___x_3214_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3237_; 
v_a_3225_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3227_ = v___x_3199_;
v_isShared_3228_ = v_isSharedCheck_3237_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3199_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3237_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3229_ = lean_io_error_to_string(v_a_3225_);
v___x_3230_ = 3;
v___x_3231_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3231_, 0, v___x_3229_);
lean_ctor_set_uint8(v___x_3231_, sizeof(void*)*1, v___x_3230_);
lean_inc_ref(v_a_3117_);
v___x_3232_ = lean_apply_2(v_a_3117_, v___x_3231_, lean_box(0));
v___x_3233_ = lean_box(0);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3233_);
v___x_3235_ = v___x_3227_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3250_; 
v_a_3238_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3240_ = v___x_3197_;
v_isShared_3241_ = v_isSharedCheck_3250_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3197_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3250_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; uint8_t v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3242_ = lean_io_error_to_string(v_a_3238_);
v___x_3243_ = 3;
v___x_3244_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*1, v___x_3243_);
lean_inc_ref(v_a_3117_);
v___x_3245_ = lean_apply_2(v_a_3117_, v___x_3244_, lean_box(0));
v___x_3246_ = lean_box(0);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3246_);
v___x_3248_ = v___x_3240_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; 
lean_dec_ref_known(v_lakeArgs_x3f_3159_, 1);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v_lakeEnv_3158_);
v___x_3251_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_3117_);
v___x_3252_ = lean_apply_2(v_a_3117_, v___x_3251_, lean_box(0));
v___x_3253_ = 4;
v___x_3254_ = lean_io_exit(v___x_3253_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3275_; 
v_a_3263_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3265_ = v___x_3254_;
v_isShared_3266_ = v_isSharedCheck_3275_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3254_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3275_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3267_; uint8_t v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3267_ = lean_io_error_to_string(v_a_3263_);
v___x_3268_ = 3;
v___x_3269_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set_uint8(v___x_3269_, sizeof(void*)*1, v___x_3268_);
lean_inc_ref(v_a_3117_);
v___x_3270_ = lean_apply_2(v_a_3117_, v___x_3269_, lean_box(0));
v___x_3271_ = lean_box(0);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v___x_3271_);
v___x_3273_ = v___x_3265_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; lean_object* v___x_3279_; 
lean_dec_ref(v___y_3172_);
lean_dec(v_lakeArgs_x3f_3159_);
lean_dec_ref(v_lakeEnv_3158_);
v___x_3276_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_3117_);
v___x_3277_ = lean_apply_2(v_a_3117_, v___x_3276_, lean_box(0));
v___x_3278_ = 4;
v___x_3279_ = lean_io_exit(v___x_3278_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3300_; 
v_a_3288_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3290_ = v___x_3279_;
v_isShared_3291_ = v_isSharedCheck_3300_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3279_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3300_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; uint8_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3292_ = lean_io_error_to_string(v_a_3288_);
v___x_3293_ = 3;
v___x_3294_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*1, v___x_3293_);
lean_inc_ref(v_a_3117_);
v___x_3295_ = lean_apply_2(v_a_3117_, v___x_3294_, lean_box(0));
v___x_3296_ = lean_box(0);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v___x_3296_);
v___x_3298_ = v___x_3290_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3313_; 
lean_dec_ref(v___y_3172_);
lean_dec(v_lakeArgs_x3f_3159_);
lean_dec_ref(v_lakeEnv_3158_);
v_a_3301_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3303_ = v___x_3179_;
v_isShared_3304_ = v_isSharedCheck_3313_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3179_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3313_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3305_ = lean_io_error_to_string(v_a_3301_);
v___x_3306_ = 3;
v___x_3307_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*1, v___x_3306_);
lean_inc_ref(v_a_3117_);
v___x_3308_ = lean_apply_2(v_a_3117_, v___x_3307_, lean_box(0));
v___x_3309_ = lean_box(0);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3309_);
v___x_3311_ = v___x_3303_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
v___jp_3314_:
{
uint8_t v___x_3317_; lean_object* v___x_3318_; lean_object* v_toString_3319_; 
v___x_3317_ = 1;
v___x_3318_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_3319_ = lean_ctor_get(v___y_3315_, 0);
lean_inc_ref(v_toString_3319_);
lean_dec_ref(v___y_3315_);
v___y_3169_ = v___y_3316_;
v___y_3170_ = v___x_3318_;
v___y_3171_ = v___x_3317_;
v___y_3172_ = v_toString_3319_;
goto v___jp_3168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_a_3388_, lean_object* v_ws_3389_, lean_object* v_rootDeps_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3388_, v_ws_3389_, v_rootDeps_3390_);
lean_dec_ref(v_rootDeps_3390_);
lean_dec_ref(v_a_3388_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(lean_object* v_msg_3393_){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = lean_box(1);
v___x_3395_ = lean_panic_fn_borrowed(v___x_3394_, v_msg_3393_);
return v___x_3395_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3399_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3400_ = lean_unsigned_to_nat(35u);
v___x_3401_ = lean_unsigned_to_nat(182u);
v___x_3402_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3403_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3404_ = l_mkPanicMessageWithDecl(v___x_3403_, v___x_3402_, v___x_3401_, v___x_3400_, v___x_3399_);
return v___x_3404_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3405_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3406_ = lean_unsigned_to_nat(21u);
v___x_3407_ = lean_unsigned_to_nat(183u);
v___x_3408_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3409_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3410_ = l_mkPanicMessageWithDecl(v___x_3409_, v___x_3408_, v___x_3407_, v___x_3406_, v___x_3405_);
return v___x_3410_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3413_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3414_ = lean_unsigned_to_nat(35u);
v___x_3415_ = lean_unsigned_to_nat(276u);
v___x_3416_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3417_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3418_ = l_mkPanicMessageWithDecl(v___x_3417_, v___x_3416_, v___x_3415_, v___x_3414_, v___x_3413_);
return v___x_3418_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3419_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3420_ = lean_unsigned_to_nat(21u);
v___x_3421_ = lean_unsigned_to_nat(277u);
v___x_3422_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3423_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3424_ = l_mkPanicMessageWithDecl(v___x_3423_, v___x_3422_, v___x_3421_, v___x_3420_, v___x_3419_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(lean_object* v_k_3425_, lean_object* v_v_3426_, lean_object* v_t_3427_){
_start:
{
if (lean_obj_tag(v_t_3427_) == 0)
{
lean_object* v_size_3428_; lean_object* v_k_3429_; lean_object* v_v_3430_; lean_object* v_l_3431_; lean_object* v_r_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3788_; 
v_size_3428_ = lean_ctor_get(v_t_3427_, 0);
v_k_3429_ = lean_ctor_get(v_t_3427_, 1);
v_v_3430_ = lean_ctor_get(v_t_3427_, 2);
v_l_3431_ = lean_ctor_get(v_t_3427_, 3);
v_r_3432_ = lean_ctor_get(v_t_3427_, 4);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_t_3427_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3434_ = v_t_3427_;
v_isShared_3435_ = v_isSharedCheck_3788_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_r_3432_);
lean_inc(v_l_3431_);
lean_inc(v_v_3430_);
lean_inc(v_k_3429_);
lean_inc(v_size_3428_);
lean_dec(v_t_3427_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3788_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
uint8_t v___x_3436_; 
v___x_3436_ = lean_string_compare(v_k_3425_, v_k_3429_);
switch(v___x_3436_)
{
case 0:
{
lean_object* v___x_3437_; 
lean_dec(v_size_3428_);
v___x_3437_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3425_, v_v_3426_, v_l_3431_);
if (lean_obj_tag(v_r_3432_) == 0)
{
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_size_3438_; lean_object* v_size_3439_; lean_object* v_k_3440_; lean_object* v_v_3441_; lean_object* v_l_3442_; lean_object* v_r_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v_size_3438_ = lean_ctor_get(v_r_3432_, 0);
v_size_3439_ = lean_ctor_get(v___x_3437_, 0);
v_k_3440_ = lean_ctor_get(v___x_3437_, 1);
v_v_3441_ = lean_ctor_get(v___x_3437_, 2);
v_l_3442_ = lean_ctor_get(v___x_3437_, 3);
v_r_3443_ = lean_ctor_get(v___x_3437_, 4);
lean_inc(v_r_3443_);
v___x_3444_ = lean_unsigned_to_nat(3u);
v___x_3445_ = lean_nat_mul(v___x_3444_, v_size_3438_);
v___x_3446_ = lean_nat_dec_lt(v___x_3445_, v_size_3439_);
lean_dec(v___x_3445_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3451_; 
lean_dec(v_r_3443_);
v___x_3447_ = lean_unsigned_to_nat(1u);
v___x_3448_ = lean_nat_add(v___x_3447_, v_size_3439_);
v___x_3449_ = lean_nat_add(v___x_3448_, v_size_3438_);
lean_dec(v___x_3448_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 3, v___x_3437_);
lean_ctor_set(v___x_3434_, 0, v___x_3449_);
v___x_3451_ = v___x_3434_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3452_, 3, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_r_3432_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
else
{
lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3524_; 
lean_inc(v_l_3442_);
lean_inc(v_v_3441_);
lean_inc(v_k_3440_);
lean_inc(v_size_3439_);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3524_ == 0)
{
lean_object* v_unused_3525_; lean_object* v_unused_3526_; lean_object* v_unused_3527_; lean_object* v_unused_3528_; lean_object* v_unused_3529_; 
v_unused_3525_ = lean_ctor_get(v___x_3437_, 4);
lean_dec(v_unused_3525_);
v_unused_3526_ = lean_ctor_get(v___x_3437_, 3);
lean_dec(v_unused_3526_);
v_unused_3527_ = lean_ctor_get(v___x_3437_, 2);
lean_dec(v_unused_3527_);
v_unused_3528_ = lean_ctor_get(v___x_3437_, 1);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v___x_3437_, 0);
lean_dec(v_unused_3529_);
v___x_3454_ = v___x_3437_;
v_isShared_3455_ = v_isSharedCheck_3524_;
goto v_resetjp_3453_;
}
else
{
lean_dec(v___x_3437_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3524_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
if (lean_obj_tag(v_l_3442_) == 0)
{
if (lean_obj_tag(v_r_3443_) == 0)
{
lean_object* v_size_3456_; lean_object* v_size_3457_; lean_object* v_k_3458_; lean_object* v_v_3459_; lean_object* v_l_3460_; lean_object* v_r_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v_size_3456_ = lean_ctor_get(v_l_3442_, 0);
v_size_3457_ = lean_ctor_get(v_r_3443_, 0);
v_k_3458_ = lean_ctor_get(v_r_3443_, 1);
v_v_3459_ = lean_ctor_get(v_r_3443_, 2);
v_l_3460_ = lean_ctor_get(v_r_3443_, 3);
v_r_3461_ = lean_ctor_get(v_r_3443_, 4);
v___x_3462_ = lean_unsigned_to_nat(2u);
v___x_3463_ = lean_nat_mul(v___x_3462_, v_size_3456_);
v___x_3464_ = lean_nat_dec_lt(v_size_3457_, v___x_3463_);
lean_dec(v___x_3463_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3494_; 
lean_inc(v_r_3461_);
lean_inc(v_l_3460_);
lean_inc(v_v_3459_);
lean_inc(v_k_3458_);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_r_3443_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; lean_object* v_unused_3496_; lean_object* v_unused_3497_; lean_object* v_unused_3498_; lean_object* v_unused_3499_; 
v_unused_3495_ = lean_ctor_get(v_r_3443_, 4);
lean_dec(v_unused_3495_);
v_unused_3496_ = lean_ctor_get(v_r_3443_, 3);
lean_dec(v_unused_3496_);
v_unused_3497_ = lean_ctor_get(v_r_3443_, 2);
lean_dec(v_unused_3497_);
v_unused_3498_ = lean_ctor_get(v_r_3443_, 1);
lean_dec(v_unused_3498_);
v_unused_3499_ = lean_ctor_get(v_r_3443_, 0);
lean_dec(v_unused_3499_);
v___x_3466_ = v_r_3443_;
v_isShared_3467_ = v_isSharedCheck_3494_;
goto v_resetjp_3465_;
}
else
{
lean_dec(v_r_3443_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3494_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___x_3482_; lean_object* v___y_3484_; 
v___x_3468_ = lean_unsigned_to_nat(1u);
v___x_3469_ = lean_nat_add(v___x_3468_, v_size_3439_);
lean_dec(v_size_3439_);
v___x_3470_ = lean_nat_add(v___x_3469_, v_size_3438_);
lean_dec(v___x_3469_);
v___x_3482_ = lean_nat_add(v___x_3468_, v_size_3456_);
if (lean_obj_tag(v_l_3460_) == 0)
{
lean_object* v_size_3492_; 
v_size_3492_ = lean_ctor_get(v_l_3460_, 0);
lean_inc(v_size_3492_);
v___y_3484_ = v_size_3492_;
goto v___jp_3483_;
}
else
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_unsigned_to_nat(0u);
v___y_3484_ = v___x_3493_;
goto v___jp_3483_;
}
v___jp_3471_:
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3475_ = lean_nat_add(v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 4, v_r_3432_);
lean_ctor_set(v___x_3466_, 3, v_r_3461_);
lean_ctor_set(v___x_3466_, 2, v_v_3430_);
lean_ctor_set(v___x_3466_, 1, v_k_3429_);
lean_ctor_set(v___x_3466_, 0, v___x_3475_);
v___x_3477_ = v___x_3466_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3481_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3481_, 3, v_r_3461_);
lean_ctor_set(v_reuseFailAlloc_3481_, 4, v_r_3432_);
v___x_3477_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3479_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 4, v___x_3477_);
lean_ctor_set(v___x_3454_, 3, v___y_3472_);
lean_ctor_set(v___x_3454_, 2, v_v_3459_);
lean_ctor_set(v___x_3454_, 1, v_k_3458_);
lean_ctor_set(v___x_3454_, 0, v___x_3470_);
v___x_3479_ = v___x_3454_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_k_3458_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_v_3459_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v___y_3472_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
v___jp_3483_:
{
lean_object* v___x_3485_; lean_object* v___x_3487_; 
v___x_3485_ = lean_nat_add(v___x_3482_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec(v___x_3482_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v_l_3460_);
lean_ctor_set(v___x_3434_, 3, v_l_3442_);
lean_ctor_set(v___x_3434_, 2, v_v_3441_);
lean_ctor_set(v___x_3434_, 1, v_k_3440_);
lean_ctor_set(v___x_3434_, 0, v___x_3485_);
v___x_3487_ = v___x_3434_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_k_3440_);
lean_ctor_set(v_reuseFailAlloc_3491_, 2, v_v_3441_);
lean_ctor_set(v_reuseFailAlloc_3491_, 3, v_l_3442_);
lean_ctor_set(v_reuseFailAlloc_3491_, 4, v_l_3460_);
v___x_3487_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_nat_add(v___x_3468_, v_size_3438_);
if (lean_obj_tag(v_r_3461_) == 0)
{
lean_object* v_size_3489_; 
v_size_3489_ = lean_ctor_get(v_r_3461_, 0);
lean_inc(v_size_3489_);
v___y_3472_ = v___x_3487_;
v___y_3473_ = v___x_3488_;
v___y_3474_ = v_size_3489_;
goto v___jp_3471_;
}
else
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_unsigned_to_nat(0u);
v___y_3472_ = v___x_3487_;
v___y_3473_ = v___x_3488_;
v___y_3474_ = v___x_3490_;
goto v___jp_3471_;
}
}
}
}
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3506_; 
lean_del_object(v___x_3434_);
v___x_3500_ = lean_unsigned_to_nat(1u);
v___x_3501_ = lean_nat_add(v___x_3500_, v_size_3439_);
lean_dec(v_size_3439_);
v___x_3502_ = lean_nat_add(v___x_3501_, v_size_3438_);
lean_dec(v___x_3501_);
v___x_3503_ = lean_nat_add(v___x_3500_, v_size_3438_);
v___x_3504_ = lean_nat_add(v___x_3503_, v_size_3457_);
lean_dec(v___x_3503_);
lean_inc_ref(v_r_3432_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 4, v_r_3432_);
lean_ctor_set(v___x_3454_, 3, v_r_3443_);
lean_ctor_set(v___x_3454_, 2, v_v_3430_);
lean_ctor_set(v___x_3454_, 1, v_k_3429_);
lean_ctor_set(v___x_3454_, 0, v___x_3504_);
v___x_3506_ = v___x_3454_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3519_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3519_, 3, v_r_3443_);
lean_ctor_set(v_reuseFailAlloc_3519_, 4, v_r_3432_);
v___x_3506_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
v_isSharedCheck_3513_ = !lean_is_exclusive(v_r_3432_);
if (v_isSharedCheck_3513_ == 0)
{
lean_object* v_unused_3514_; lean_object* v_unused_3515_; lean_object* v_unused_3516_; lean_object* v_unused_3517_; lean_object* v_unused_3518_; 
v_unused_3514_ = lean_ctor_get(v_r_3432_, 4);
lean_dec(v_unused_3514_);
v_unused_3515_ = lean_ctor_get(v_r_3432_, 3);
lean_dec(v_unused_3515_);
v_unused_3516_ = lean_ctor_get(v_r_3432_, 2);
lean_dec(v_unused_3516_);
v_unused_3517_ = lean_ctor_get(v_r_3432_, 1);
lean_dec(v_unused_3517_);
v_unused_3518_ = lean_ctor_get(v_r_3432_, 0);
lean_dec(v_unused_3518_);
v___x_3508_ = v_r_3432_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_dec(v_r_3432_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 4, v___x_3506_);
lean_ctor_set(v___x_3508_, 3, v_l_3442_);
lean_ctor_set(v___x_3508_, 2, v_v_3441_);
lean_ctor_set(v___x_3508_, 1, v_k_3440_);
lean_ctor_set(v___x_3508_, 0, v___x_3502_);
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_k_3440_);
lean_ctor_set(v_reuseFailAlloc_3512_, 2, v_v_3441_);
lean_ctor_set(v_reuseFailAlloc_3512_, 3, v_l_3442_);
lean_ctor_set(v_reuseFailAlloc_3512_, 4, v___x_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
lean_dec_ref_known(v_l_3442_, 5);
lean_del_object(v___x_3454_);
lean_dec(v_v_3441_);
lean_dec(v_k_3440_);
lean_dec(v_size_3439_);
lean_dec_ref_known(v_r_3432_, 5);
lean_del_object(v___x_3434_);
lean_dec(v_v_3430_);
lean_dec(v_k_3429_);
v___x_3520_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3);
v___x_3521_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3520_);
return v___x_3521_;
}
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_del_object(v___x_3454_);
lean_dec(v_r_3443_);
lean_dec(v_v_3441_);
lean_dec(v_k_3440_);
lean_dec(v_size_3439_);
lean_dec_ref_known(v_r_3432_, 5);
lean_del_object(v___x_3434_);
lean_dec(v_v_3430_);
lean_dec(v_k_3429_);
v___x_3522_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4);
v___x_3523_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3522_);
return v___x_3523_;
}
}
}
}
else
{
lean_object* v_size_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3534_; 
v_size_3530_ = lean_ctor_get(v_r_3432_, 0);
v___x_3531_ = lean_unsigned_to_nat(1u);
v___x_3532_ = lean_nat_add(v___x_3531_, v_size_3530_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 3, v___x_3437_);
lean_ctor_set(v___x_3434_, 0, v___x_3532_);
v___x_3534_ = v___x_3434_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3535_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3535_, 3, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3535_, 4, v_r_3432_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
else
{
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_l_3536_; 
v_l_3536_ = lean_ctor_get(v___x_3437_, 3);
if (lean_obj_tag(v_l_3536_) == 0)
{
lean_object* v_r_3537_; 
lean_inc_ref(v_l_3536_);
v_r_3537_ = lean_ctor_get(v___x_3437_, 4);
lean_inc(v_r_3537_);
if (lean_obj_tag(v_r_3537_) == 0)
{
lean_object* v_size_3538_; lean_object* v_k_3539_; lean_object* v_v_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3554_; 
v_size_3538_ = lean_ctor_get(v___x_3437_, 0);
v_k_3539_ = lean_ctor_get(v___x_3437_, 1);
v_v_3540_ = lean_ctor_get(v___x_3437_, 2);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3554_ == 0)
{
lean_object* v_unused_3555_; lean_object* v_unused_3556_; 
v_unused_3555_ = lean_ctor_get(v___x_3437_, 4);
lean_dec(v_unused_3555_);
v_unused_3556_ = lean_ctor_get(v___x_3437_, 3);
lean_dec(v_unused_3556_);
v___x_3542_ = v___x_3437_;
v_isShared_3543_ = v_isSharedCheck_3554_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_v_3540_);
lean_inc(v_k_3539_);
lean_inc(v_size_3538_);
lean_dec(v___x_3437_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3554_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_size_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3549_; 
v_size_3544_ = lean_ctor_get(v_r_3537_, 0);
v___x_3545_ = lean_unsigned_to_nat(1u);
v___x_3546_ = lean_nat_add(v___x_3545_, v_size_3538_);
lean_dec(v_size_3538_);
v___x_3547_ = lean_nat_add(v___x_3545_, v_size_3544_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v_r_3432_);
lean_ctor_set(v___x_3542_, 3, v_r_3537_);
lean_ctor_set(v___x_3542_, 2, v_v_3430_);
lean_ctor_set(v___x_3542_, 1, v_k_3429_);
lean_ctor_set(v___x_3542_, 0, v___x_3547_);
v___x_3549_ = v___x_3542_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3553_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3553_, 3, v_r_3537_);
lean_ctor_set(v_reuseFailAlloc_3553_, 4, v_r_3432_);
v___x_3549_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3551_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v___x_3549_);
lean_ctor_set(v___x_3434_, 3, v_l_3536_);
lean_ctor_set(v___x_3434_, 2, v_v_3540_);
lean_ctor_set(v___x_3434_, 1, v_k_3539_);
lean_ctor_set(v___x_3434_, 0, v___x_3546_);
v___x_3551_ = v___x_3434_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_k_3539_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_v_3540_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v_l_3536_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
else
{
lean_object* v_k_3557_; lean_object* v_v_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3570_; 
v_k_3557_ = lean_ctor_get(v___x_3437_, 1);
v_v_3558_ = lean_ctor_get(v___x_3437_, 2);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; lean_object* v_unused_3572_; lean_object* v_unused_3573_; 
v_unused_3571_ = lean_ctor_get(v___x_3437_, 4);
lean_dec(v_unused_3571_);
v_unused_3572_ = lean_ctor_get(v___x_3437_, 3);
lean_dec(v_unused_3572_);
v_unused_3573_ = lean_ctor_get(v___x_3437_, 0);
lean_dec(v_unused_3573_);
v___x_3560_ = v___x_3437_;
v_isShared_3561_ = v_isSharedCheck_3570_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_v_3558_);
lean_inc(v_k_3557_);
lean_dec(v___x_3437_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3570_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3565_; 
v___x_3562_ = lean_unsigned_to_nat(3u);
v___x_3563_ = lean_unsigned_to_nat(1u);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 3, v_r_3537_);
lean_ctor_set(v___x_3560_, 2, v_v_3430_);
lean_ctor_set(v___x_3560_, 1, v_k_3429_);
lean_ctor_set(v___x_3560_, 0, v___x_3563_);
v___x_3565_ = v___x_3560_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3569_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3569_, 3, v_r_3537_);
lean_ctor_set(v_reuseFailAlloc_3569_, 4, v_r_3537_);
v___x_3565_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_object* v___x_3567_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v___x_3565_);
lean_ctor_set(v___x_3434_, 3, v_l_3536_);
lean_ctor_set(v___x_3434_, 2, v_v_3558_);
lean_ctor_set(v___x_3434_, 1, v_k_3557_);
lean_ctor_set(v___x_3434_, 0, v___x_3562_);
v___x_3567_ = v___x_3434_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_k_3557_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_v_3558_);
lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_l_3536_);
lean_ctor_set(v_reuseFailAlloc_3568_, 4, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
else
{
lean_object* v_r_3574_; 
v_r_3574_ = lean_ctor_get(v___x_3437_, 4);
lean_inc(v_r_3574_);
if (lean_obj_tag(v_r_3574_) == 0)
{
lean_object* v_k_3575_; lean_object* v_v_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3600_; 
lean_inc(v_l_3536_);
v_k_3575_ = lean_ctor_get(v___x_3437_, 1);
v_v_3576_ = lean_ctor_get(v___x_3437_, 2);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; lean_object* v_unused_3602_; lean_object* v_unused_3603_; 
v_unused_3601_ = lean_ctor_get(v___x_3437_, 4);
lean_dec(v_unused_3601_);
v_unused_3602_ = lean_ctor_get(v___x_3437_, 3);
lean_dec(v_unused_3602_);
v_unused_3603_ = lean_ctor_get(v___x_3437_, 0);
lean_dec(v_unused_3603_);
v___x_3578_ = v___x_3437_;
v_isShared_3579_ = v_isSharedCheck_3600_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_v_3576_);
lean_inc(v_k_3575_);
lean_dec(v___x_3437_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3600_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v_k_3580_; lean_object* v_v_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3596_; 
v_k_3580_ = lean_ctor_get(v_r_3574_, 1);
v_v_3581_ = lean_ctor_get(v_r_3574_, 2);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_r_3574_);
if (v_isSharedCheck_3596_ == 0)
{
lean_object* v_unused_3597_; lean_object* v_unused_3598_; lean_object* v_unused_3599_; 
v_unused_3597_ = lean_ctor_get(v_r_3574_, 4);
lean_dec(v_unused_3597_);
v_unused_3598_ = lean_ctor_get(v_r_3574_, 3);
lean_dec(v_unused_3598_);
v_unused_3599_ = lean_ctor_get(v_r_3574_, 0);
lean_dec(v_unused_3599_);
v___x_3583_ = v_r_3574_;
v_isShared_3584_ = v_isSharedCheck_3596_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_v_3581_);
lean_inc(v_k_3580_);
lean_dec(v_r_3574_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3596_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3585_ = lean_unsigned_to_nat(3u);
v___x_3586_ = lean_unsigned_to_nat(1u);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 4, v_l_3536_);
lean_ctor_set(v___x_3583_, 3, v_l_3536_);
lean_ctor_set(v___x_3583_, 2, v_v_3576_);
lean_ctor_set(v___x_3583_, 1, v_k_3575_);
lean_ctor_set(v___x_3583_, 0, v___x_3586_);
v___x_3588_ = v___x_3583_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_k_3575_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v_v_3576_);
lean_ctor_set(v_reuseFailAlloc_3595_, 3, v_l_3536_);
lean_ctor_set(v_reuseFailAlloc_3595_, 4, v_l_3536_);
v___x_3588_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3590_; 
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 4, v_l_3536_);
lean_ctor_set(v___x_3578_, 2, v_v_3430_);
lean_ctor_set(v___x_3578_, 1, v_k_3429_);
lean_ctor_set(v___x_3578_, 0, v___x_3586_);
v___x_3590_ = v___x_3578_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3594_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3594_, 3, v_l_3536_);
lean_ctor_set(v_reuseFailAlloc_3594_, 4, v_l_3536_);
v___x_3590_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3592_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v___x_3590_);
lean_ctor_set(v___x_3434_, 3, v___x_3588_);
lean_ctor_set(v___x_3434_, 2, v_v_3581_);
lean_ctor_set(v___x_3434_, 1, v_k_3580_);
lean_ctor_set(v___x_3434_, 0, v___x_3585_);
v___x_3592_ = v___x_3434_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_k_3580_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v_v_3581_);
lean_ctor_set(v_reuseFailAlloc_3593_, 3, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3593_, 4, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
}
}
else
{
lean_object* v___x_3604_; lean_object* v___x_3606_; 
v___x_3604_ = lean_unsigned_to_nat(2u);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v_r_3574_);
lean_ctor_set(v___x_3434_, 3, v___x_3437_);
lean_ctor_set(v___x_3434_, 0, v___x_3604_);
v___x_3606_ = v___x_3434_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3607_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3607_, 3, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3607_, 4, v_r_3574_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3608_ = lean_unsigned_to_nat(1u);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v___x_3437_);
lean_ctor_set(v___x_3434_, 3, v___x_3437_);
lean_ctor_set(v___x_3434_, 0, v___x_3608_);
v___x_3610_ = v___x_3434_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3611_, 3, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3611_, 4, v___x_3437_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
case 1:
{
lean_object* v___x_3613_; 
lean_dec(v_v_3430_);
lean_dec(v_k_3429_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 2, v_v_3426_);
lean_ctor_set(v___x_3434_, 1, v_k_3425_);
v___x_3613_ = v___x_3434_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_size_3428_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_k_3425_);
lean_ctor_set(v_reuseFailAlloc_3614_, 2, v_v_3426_);
lean_ctor_set(v_reuseFailAlloc_3614_, 3, v_l_3431_);
lean_ctor_set(v_reuseFailAlloc_3614_, 4, v_r_3432_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
default: 
{
lean_object* v___x_3615_; 
lean_dec(v_size_3428_);
v___x_3615_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3425_, v_v_3426_, v_r_3432_);
if (lean_obj_tag(v_l_3431_) == 0)
{
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_size_3616_; lean_object* v_size_3617_; lean_object* v_k_3618_; lean_object* v_v_3619_; lean_object* v_l_3620_; lean_object* v_r_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v_size_3616_ = lean_ctor_get(v_l_3431_, 0);
v_size_3617_ = lean_ctor_get(v___x_3615_, 0);
v_k_3618_ = lean_ctor_get(v___x_3615_, 1);
v_v_3619_ = lean_ctor_get(v___x_3615_, 2);
v_l_3620_ = lean_ctor_get(v___x_3615_, 3);
lean_inc(v_l_3620_);
v_r_3621_ = lean_ctor_get(v___x_3615_, 4);
v___x_3622_ = lean_unsigned_to_nat(3u);
v___x_3623_ = lean_nat_mul(v___x_3622_, v_size_3616_);
v___x_3624_ = lean_nat_dec_lt(v___x_3623_, v_size_3617_);
lean_dec(v___x_3623_);
if (v___x_3624_ == 0)
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3629_; 
lean_dec(v_l_3620_);
v___x_3625_ = lean_unsigned_to_nat(1u);
v___x_3626_ = lean_nat_add(v___x_3625_, v_size_3616_);
v___x_3627_ = lean_nat_add(v___x_3626_, v_size_3617_);
lean_dec(v___x_3626_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v___x_3615_);
lean_ctor_set(v___x_3434_, 0, v___x_3627_);
v___x_3629_ = v___x_3434_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3627_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_l_3431_);
lean_ctor_set(v_reuseFailAlloc_3630_, 4, v___x_3615_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
else
{
lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3700_; 
lean_inc(v_r_3621_);
lean_inc(v_v_3619_);
lean_inc(v_k_3618_);
lean_inc(v_size_3617_);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3700_ == 0)
{
lean_object* v_unused_3701_; lean_object* v_unused_3702_; lean_object* v_unused_3703_; lean_object* v_unused_3704_; lean_object* v_unused_3705_; 
v_unused_3701_ = lean_ctor_get(v___x_3615_, 4);
lean_dec(v_unused_3701_);
v_unused_3702_ = lean_ctor_get(v___x_3615_, 3);
lean_dec(v_unused_3702_);
v_unused_3703_ = lean_ctor_get(v___x_3615_, 2);
lean_dec(v_unused_3703_);
v_unused_3704_ = lean_ctor_get(v___x_3615_, 1);
lean_dec(v_unused_3704_);
v_unused_3705_ = lean_ctor_get(v___x_3615_, 0);
lean_dec(v_unused_3705_);
v___x_3632_ = v___x_3615_;
v_isShared_3633_ = v_isSharedCheck_3700_;
goto v_resetjp_3631_;
}
else
{
lean_dec(v___x_3615_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3700_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
if (lean_obj_tag(v_l_3620_) == 0)
{
if (lean_obj_tag(v_r_3621_) == 0)
{
lean_object* v_size_3634_; lean_object* v_k_3635_; lean_object* v_v_3636_; lean_object* v_l_3637_; lean_object* v_r_3638_; lean_object* v_size_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v_size_3634_ = lean_ctor_get(v_l_3620_, 0);
v_k_3635_ = lean_ctor_get(v_l_3620_, 1);
v_v_3636_ = lean_ctor_get(v_l_3620_, 2);
v_l_3637_ = lean_ctor_get(v_l_3620_, 3);
v_r_3638_ = lean_ctor_get(v_l_3620_, 4);
v_size_3639_ = lean_ctor_get(v_r_3621_, 0);
v___x_3640_ = lean_unsigned_to_nat(2u);
v___x_3641_ = lean_nat_mul(v___x_3640_, v_size_3639_);
v___x_3642_ = lean_nat_dec_lt(v_size_3634_, v___x_3641_);
lean_dec(v___x_3641_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3671_; 
lean_inc(v_r_3638_);
lean_inc(v_l_3637_);
lean_inc(v_v_3636_);
lean_inc(v_k_3635_);
v_isSharedCheck_3671_ = !lean_is_exclusive(v_l_3620_);
if (v_isSharedCheck_3671_ == 0)
{
lean_object* v_unused_3672_; lean_object* v_unused_3673_; lean_object* v_unused_3674_; lean_object* v_unused_3675_; lean_object* v_unused_3676_; 
v_unused_3672_ = lean_ctor_get(v_l_3620_, 4);
lean_dec(v_unused_3672_);
v_unused_3673_ = lean_ctor_get(v_l_3620_, 3);
lean_dec(v_unused_3673_);
v_unused_3674_ = lean_ctor_get(v_l_3620_, 2);
lean_dec(v_unused_3674_);
v_unused_3675_ = lean_ctor_get(v_l_3620_, 1);
lean_dec(v_unused_3675_);
v_unused_3676_ = lean_ctor_get(v_l_3620_, 0);
lean_dec(v_unused_3676_);
v___x_3644_ = v_l_3620_;
v_isShared_3645_ = v_isSharedCheck_3671_;
goto v_resetjp_3643_;
}
else
{
lean_dec(v_l_3620_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3671_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3661_; 
v___x_3646_ = lean_unsigned_to_nat(1u);
v___x_3647_ = lean_nat_add(v___x_3646_, v_size_3616_);
v___x_3648_ = lean_nat_add(v___x_3647_, v_size_3617_);
lean_dec(v_size_3617_);
if (lean_obj_tag(v_l_3637_) == 0)
{
lean_object* v_size_3669_; 
v_size_3669_ = lean_ctor_get(v_l_3637_, 0);
lean_inc(v_size_3669_);
v___y_3661_ = v_size_3669_;
goto v___jp_3660_;
}
else
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_unsigned_to_nat(0u);
v___y_3661_ = v___x_3670_;
goto v___jp_3660_;
}
v___jp_3649_:
{
lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3653_ = lean_nat_add(v___y_3650_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec(v___y_3650_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 4, v_r_3621_);
lean_ctor_set(v___x_3644_, 3, v_r_3638_);
lean_ctor_set(v___x_3644_, 2, v_v_3619_);
lean_ctor_set(v___x_3644_, 1, v_k_3618_);
lean_ctor_set(v___x_3644_, 0, v___x_3653_);
v___x_3655_ = v___x_3644_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3659_, 3, v_r_3638_);
lean_ctor_set(v_reuseFailAlloc_3659_, 4, v_r_3621_);
v___x_3655_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3657_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 4, v___x_3655_);
lean_ctor_set(v___x_3632_, 3, v___y_3651_);
lean_ctor_set(v___x_3632_, 2, v_v_3636_);
lean_ctor_set(v___x_3632_, 1, v_k_3635_);
lean_ctor_set(v___x_3632_, 0, v___x_3648_);
v___x_3657_ = v___x_3632_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_k_3635_);
lean_ctor_set(v_reuseFailAlloc_3658_, 2, v_v_3636_);
lean_ctor_set(v_reuseFailAlloc_3658_, 3, v___y_3651_);
lean_ctor_set(v_reuseFailAlloc_3658_, 4, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
v___jp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
v___x_3662_ = lean_nat_add(v___x_3647_, v___y_3661_);
lean_dec(v___y_3661_);
lean_dec(v___x_3647_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v_l_3637_);
lean_ctor_set(v___x_3434_, 0, v___x_3662_);
v___x_3664_ = v___x_3434_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3668_, 3, v_l_3431_);
lean_ctor_set(v_reuseFailAlloc_3668_, 4, v_l_3637_);
v___x_3664_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3665_; 
v___x_3665_ = lean_nat_add(v___x_3646_, v_size_3639_);
if (lean_obj_tag(v_r_3638_) == 0)
{
lean_object* v_size_3666_; 
v_size_3666_ = lean_ctor_get(v_r_3638_, 0);
lean_inc(v_size_3666_);
v___y_3650_ = v___x_3665_;
v___y_3651_ = v___x_3664_;
v___y_3652_ = v_size_3666_;
goto v___jp_3649_;
}
else
{
lean_object* v___x_3667_; 
v___x_3667_ = lean_unsigned_to_nat(0u);
v___y_3650_ = v___x_3665_;
v___y_3651_ = v___x_3664_;
v___y_3652_ = v___x_3667_;
goto v___jp_3649_;
}
}
}
}
}
else
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
lean_del_object(v___x_3434_);
v___x_3677_ = lean_unsigned_to_nat(1u);
v___x_3678_ = lean_nat_add(v___x_3677_, v_size_3616_);
v___x_3679_ = lean_nat_add(v___x_3678_, v_size_3617_);
lean_dec(v_size_3617_);
v___x_3680_ = lean_nat_add(v___x_3678_, v_size_3634_);
lean_dec(v___x_3678_);
lean_inc_ref(v_l_3431_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 4, v_l_3620_);
lean_ctor_set(v___x_3632_, 3, v_l_3431_);
lean_ctor_set(v___x_3632_, 2, v_v_3430_);
lean_ctor_set(v___x_3632_, 1, v_k_3429_);
lean_ctor_set(v___x_3632_, 0, v___x_3680_);
v___x_3682_ = v___x_3632_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3680_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3695_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3695_, 3, v_l_3431_);
lean_ctor_set(v_reuseFailAlloc_3695_, 4, v_l_3620_);
v___x_3682_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
v_isSharedCheck_3689_ = !lean_is_exclusive(v_l_3431_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; lean_object* v_unused_3691_; lean_object* v_unused_3692_; lean_object* v_unused_3693_; lean_object* v_unused_3694_; 
v_unused_3690_ = lean_ctor_get(v_l_3431_, 4);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_l_3431_, 3);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_l_3431_, 2);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_l_3431_, 1);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_l_3431_, 0);
lean_dec(v_unused_3694_);
v___x_3684_ = v_l_3431_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_dec(v_l_3431_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 4, v_r_3621_);
lean_ctor_set(v___x_3684_, 3, v___x_3682_);
lean_ctor_set(v___x_3684_, 2, v_v_3619_);
lean_ctor_set(v___x_3684_, 1, v_k_3618_);
lean_ctor_set(v___x_3684_, 0, v___x_3679_);
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3688_, 3, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3688_, 4, v_r_3621_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_dec_ref_known(v_l_3620_, 5);
lean_del_object(v___x_3632_);
lean_dec(v_v_3619_);
lean_dec(v_k_3618_);
lean_dec(v_size_3617_);
lean_dec_ref_known(v_l_3431_, 5);
lean_del_object(v___x_3434_);
lean_dec(v_v_3430_);
lean_dec(v_k_3429_);
v___x_3696_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7);
v___x_3697_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3696_);
return v___x_3697_;
}
}
else
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_del_object(v___x_3632_);
lean_dec(v_r_3621_);
lean_dec(v_v_3619_);
lean_dec(v_k_3618_);
lean_dec(v_size_3617_);
lean_dec_ref_known(v_l_3431_, 5);
lean_del_object(v___x_3434_);
lean_dec(v_v_3430_);
lean_dec(v_k_3429_);
v___x_3698_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8);
v___x_3699_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3698_);
return v___x_3699_;
}
}
}
}
else
{
lean_object* v_size_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
v_size_3706_ = lean_ctor_get(v_l_3431_, 0);
v___x_3707_ = lean_unsigned_to_nat(1u);
v___x_3708_ = lean_nat_add(v___x_3707_, v_size_3706_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v___x_3615_);
lean_ctor_set(v___x_3434_, 0, v___x_3708_);
v___x_3710_ = v___x_3434_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3711_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3711_, 3, v_l_3431_);
lean_ctor_set(v_reuseFailAlloc_3711_, 4, v___x_3615_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
else
{
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_l_3712_; 
v_l_3712_ = lean_ctor_get(v___x_3615_, 3);
lean_inc(v_l_3712_);
if (lean_obj_tag(v_l_3712_) == 0)
{
lean_object* v_r_3713_; 
v_r_3713_ = lean_ctor_get(v___x_3615_, 4);
lean_inc(v_r_3713_);
if (lean_obj_tag(v_r_3713_) == 0)
{
lean_object* v_size_3714_; lean_object* v_k_3715_; lean_object* v_v_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3730_; 
v_size_3714_ = lean_ctor_get(v___x_3615_, 0);
v_k_3715_ = lean_ctor_get(v___x_3615_, 1);
v_v_3716_ = lean_ctor_get(v___x_3615_, 2);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; lean_object* v_unused_3732_; 
v_unused_3731_ = lean_ctor_get(v___x_3615_, 4);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v___x_3615_, 3);
lean_dec(v_unused_3732_);
v___x_3718_ = v___x_3615_;
v_isShared_3719_ = v_isSharedCheck_3730_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_v_3716_);
lean_inc(v_k_3715_);
lean_inc(v_size_3714_);
lean_dec(v___x_3615_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3730_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v_size_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3725_; 
v_size_3720_ = lean_ctor_get(v_l_3712_, 0);
v___x_3721_ = lean_unsigned_to_nat(1u);
v___x_3722_ = lean_nat_add(v___x_3721_, v_size_3714_);
lean_dec(v_size_3714_);
v___x_3723_ = lean_nat_add(v___x_3721_, v_size_3720_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 4, v_l_3712_);
lean_ctor_set(v___x_3718_, 3, v_l_3431_);
lean_ctor_set(v___x_3718_, 2, v_v_3430_);
lean_ctor_set(v___x_3718_, 1, v_k_3429_);
lean_ctor_set(v___x_3718_, 0, v___x_3723_);
v___x_3725_ = v___x_3718_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_l_3431_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_l_3712_);
v___x_3725_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3727_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v_r_3713_);
lean_ctor_set(v___x_3434_, 3, v___x_3725_);
lean_ctor_set(v___x_3434_, 2, v_v_3716_);
lean_ctor_set(v___x_3434_, 1, v_k_3715_);
lean_ctor_set(v___x_3434_, 0, v___x_3722_);
v___x_3727_ = v___x_3434_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_k_3715_);
lean_ctor_set(v_reuseFailAlloc_3728_, 2, v_v_3716_);
lean_ctor_set(v_reuseFailAlloc_3728_, 3, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3728_, 4, v_r_3713_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_object* v_k_3733_; lean_object* v_v_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3758_; 
v_k_3733_ = lean_ctor_get(v___x_3615_, 1);
v_v_3734_ = lean_ctor_get(v___x_3615_, 2);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3759_ = lean_ctor_get(v___x_3615_, 4);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v___x_3615_, 3);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v___x_3615_, 0);
lean_dec(v_unused_3761_);
v___x_3736_ = v___x_3615_;
v_isShared_3737_ = v_isSharedCheck_3758_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_v_3734_);
lean_inc(v_k_3733_);
lean_dec(v___x_3615_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3758_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v_k_3738_; lean_object* v_v_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3754_; 
v_k_3738_ = lean_ctor_get(v_l_3712_, 1);
v_v_3739_ = lean_ctor_get(v_l_3712_, 2);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_l_3712_);
if (v_isSharedCheck_3754_ == 0)
{
lean_object* v_unused_3755_; lean_object* v_unused_3756_; lean_object* v_unused_3757_; 
v_unused_3755_ = lean_ctor_get(v_l_3712_, 4);
lean_dec(v_unused_3755_);
v_unused_3756_ = lean_ctor_get(v_l_3712_, 3);
lean_dec(v_unused_3756_);
v_unused_3757_ = lean_ctor_get(v_l_3712_, 0);
lean_dec(v_unused_3757_);
v___x_3741_ = v_l_3712_;
v_isShared_3742_ = v_isSharedCheck_3754_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_v_3739_);
lean_inc(v_k_3738_);
lean_dec(v_l_3712_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3754_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3743_ = lean_unsigned_to_nat(3u);
v___x_3744_ = lean_unsigned_to_nat(1u);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 4, v_r_3713_);
lean_ctor_set(v___x_3741_, 3, v_r_3713_);
lean_ctor_set(v___x_3741_, 2, v_v_3430_);
lean_ctor_set(v___x_3741_, 1, v_k_3429_);
lean_ctor_set(v___x_3741_, 0, v___x_3744_);
v___x_3746_ = v___x_3741_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3753_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3753_, 3, v_r_3713_);
lean_ctor_set(v_reuseFailAlloc_3753_, 4, v_r_3713_);
v___x_3746_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 3, v_r_3713_);
lean_ctor_set(v___x_3736_, 0, v___x_3744_);
v___x_3748_ = v___x_3736_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_k_3733_);
lean_ctor_set(v_reuseFailAlloc_3752_, 2, v_v_3734_);
lean_ctor_set(v_reuseFailAlloc_3752_, 3, v_r_3713_);
lean_ctor_set(v_reuseFailAlloc_3752_, 4, v_r_3713_);
v___x_3748_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3750_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v___x_3748_);
lean_ctor_set(v___x_3434_, 3, v___x_3746_);
lean_ctor_set(v___x_3434_, 2, v_v_3739_);
lean_ctor_set(v___x_3434_, 1, v_k_3738_);
lean_ctor_set(v___x_3434_, 0, v___x_3743_);
v___x_3750_ = v___x_3434_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3743_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_k_3738_);
lean_ctor_set(v_reuseFailAlloc_3751_, 2, v_v_3739_);
lean_ctor_set(v_reuseFailAlloc_3751_, 3, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3751_, 4, v___x_3748_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3762_; 
v_r_3762_ = lean_ctor_get(v___x_3615_, 4);
lean_inc(v_r_3762_);
if (lean_obj_tag(v_r_3762_) == 0)
{
lean_object* v_k_3763_; lean_object* v_v_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3776_; 
v_k_3763_ = lean_ctor_get(v___x_3615_, 1);
v_v_3764_ = lean_ctor_get(v___x_3615_, 2);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3776_ == 0)
{
lean_object* v_unused_3777_; lean_object* v_unused_3778_; lean_object* v_unused_3779_; 
v_unused_3777_ = lean_ctor_get(v___x_3615_, 4);
lean_dec(v_unused_3777_);
v_unused_3778_ = lean_ctor_get(v___x_3615_, 3);
lean_dec(v_unused_3778_);
v_unused_3779_ = lean_ctor_get(v___x_3615_, 0);
lean_dec(v_unused_3779_);
v___x_3766_ = v___x_3615_;
v_isShared_3767_ = v_isSharedCheck_3776_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_v_3764_);
lean_inc(v_k_3763_);
lean_dec(v___x_3615_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3776_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3771_; 
v___x_3768_ = lean_unsigned_to_nat(3u);
v___x_3769_ = lean_unsigned_to_nat(1u);
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 4, v_l_3712_);
lean_ctor_set(v___x_3766_, 2, v_v_3430_);
lean_ctor_set(v___x_3766_, 1, v_k_3429_);
lean_ctor_set(v___x_3766_, 0, v___x_3769_);
v___x_3771_ = v___x_3766_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3775_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3775_, 3, v_l_3712_);
lean_ctor_set(v_reuseFailAlloc_3775_, 4, v_l_3712_);
v___x_3771_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3773_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v_r_3762_);
lean_ctor_set(v___x_3434_, 3, v___x_3771_);
lean_ctor_set(v___x_3434_, 2, v_v_3764_);
lean_ctor_set(v___x_3434_, 1, v_k_3763_);
lean_ctor_set(v___x_3434_, 0, v___x_3768_);
v___x_3773_ = v___x_3434_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_k_3763_);
lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_v_3764_);
lean_ctor_set(v_reuseFailAlloc_3774_, 3, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3774_, 4, v_r_3762_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3780_ = lean_unsigned_to_nat(2u);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v___x_3615_);
lean_ctor_set(v___x_3434_, 3, v_r_3762_);
lean_ctor_set(v___x_3434_, 0, v___x_3780_);
v___x_3782_ = v___x_3434_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3783_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3783_, 3, v_r_3762_);
lean_ctor_set(v_reuseFailAlloc_3783_, 4, v___x_3615_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
lean_object* v___x_3784_; lean_object* v___x_3786_; 
v___x_3784_ = lean_unsigned_to_nat(1u);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 4, v___x_3615_);
lean_ctor_set(v___x_3434_, 3, v___x_3615_);
lean_ctor_set(v___x_3434_, 0, v___x_3784_);
v___x_3786_ = v___x_3434_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3787_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3787_, 3, v___x_3615_);
lean_ctor_set(v_reuseFailAlloc_3787_, 4, v___x_3615_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = lean_unsigned_to_nat(1u);
v___x_3790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
lean_ctor_set(v___x_3790_, 1, v_k_3425_);
lean_ctor_set(v___x_3790_, 2, v_v_3426_);
lean_ctor_set(v___x_3790_, 3, v_t_3427_);
lean_ctor_set(v___x_3790_, 4, v_t_3427_);
return v___x_3790_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(lean_object* v_init_3791_, lean_object* v_x_3792_){
_start:
{
if (lean_obj_tag(v_x_3792_) == 0)
{
lean_object* v_k_3793_; lean_object* v_v_3794_; lean_object* v_l_3795_; lean_object* v_r_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v_k_3793_ = lean_ctor_get(v_x_3792_, 1);
lean_inc(v_k_3793_);
v_v_3794_ = lean_ctor_get(v_x_3792_, 2);
lean_inc(v_v_3794_);
v_l_3795_ = lean_ctor_get(v_x_3792_, 3);
lean_inc(v_l_3795_);
v_r_3796_ = lean_ctor_get(v_x_3792_, 4);
lean_inc(v_r_3796_);
lean_dec_ref_known(v_x_3792_, 5);
v___x_3797_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_3791_, v_l_3795_);
v___x_3798_ = 1;
v___x_3799_ = l_Lean_Name_toString(v_k_3793_, v___x_3798_);
v___x_3800_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3800_, 0, v_v_3794_);
v___x_3801_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v___x_3799_, v___x_3800_, v___x_3797_);
v_init_3791_ = v___x_3801_;
v_x_3792_ = v_r_3796_;
goto _start;
}
else
{
return v_init_3791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_m_3803_){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = lean_box(1);
v___x_3805_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v___x_3804_, v_m_3803_);
v___x_3806_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v___x_3809_, uint8_t v_updateToolchain_3810_, lean_object* v_ws_3811_, lean_object* v_dep_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_baseName_3816_; lean_object* v_name_3817_; lean_object* v_opts_3818_; uint8_t v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v_baseName_3816_ = lean_ctor_get(v___x_3809_, 1);
v_name_3817_ = lean_ctor_get(v_dep_3812_, 0);
v_opts_3818_ = lean_ctor_get(v_dep_3812_, 4);
v___x_3819_ = 0;
lean_inc(v_baseName_3816_);
v___x_3820_ = l_Lean_Name_toString(v_baseName_3816_, v___x_3819_);
v___x_3821_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3822_ = lean_string_append(v___x_3820_, v___x_3821_);
lean_inc(v_name_3817_);
v___x_3823_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3817_, v_updateToolchain_3810_);
v___x_3824_ = lean_string_append(v___x_3822_, v___x_3823_);
lean_dec_ref(v___x_3823_);
v___x_3825_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3826_ = lean_string_append(v___x_3824_, v___x_3825_);
lean_inc(v_opts_3818_);
v___x_3827_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_opts_3818_);
v___x_3828_ = lean_unsigned_to_nat(80u);
v___x_3829_ = l_Lean_Json_pretty(v___x_3827_, v___x_3828_);
v___x_3830_ = lean_string_append(v___x_3826_, v___x_3829_);
lean_dec_ref(v___x_3829_);
v___x_3831_ = 0;
v___x_3832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3832_, 0, v___x_3830_);
lean_ctor_set_uint8(v___x_3832_, sizeof(void*)*1, v___x_3831_);
lean_inc_ref(v___y_3814_);
v___x_3833_ = lean_apply_2(v___y_3814_, v___x_3832_, lean_box(0));
v___x_3834_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3811_, v___x_3809_, v_dep_3812_, v___y_3813_, v___y_3814_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v___x_3835_, lean_object* v_updateToolchain_3836_, lean_object* v_ws_3837_, lean_object* v_dep_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
uint8_t v_updateToolchain_boxed_3842_; lean_object* v_res_3843_; 
v_updateToolchain_boxed_3842_ = lean_unbox(v_updateToolchain_3836_);
v_res_3843_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v___x_3835_, v_updateToolchain_boxed_3842_, v_ws_3837_, v_dep_3838_, v___y_3839_, v___y_3840_);
lean_dec_ref(v___y_3840_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_a_3844_, lean_object* v_b_3845_){
_start:
{
lean_object* v_next_3846_; 
v_next_3846_ = lean_ctor_get(v_a_3844_, 0);
lean_inc(v_next_3846_);
if (lean_obj_tag(v_next_3846_) == 0)
{
lean_dec_ref(v_a_3844_);
return v_b_3845_;
}
else
{
lean_object* v_upperBound_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3867_; 
v_upperBound_3847_ = lean_ctor_get(v_a_3844_, 1);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_a_3844_);
if (v_isSharedCheck_3867_ == 0)
{
lean_object* v_unused_3868_; 
v_unused_3868_ = lean_ctor_get(v_a_3844_, 0);
lean_dec(v_unused_3868_);
v___x_3849_ = v_a_3844_;
v_isShared_3850_ = v_isSharedCheck_3867_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_upperBound_3847_);
lean_dec(v_a_3844_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3867_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v_val_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3866_; 
v_val_3851_ = lean_ctor_get(v_next_3846_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_next_3846_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3853_ = v_next_3846_;
v_isShared_3854_ = v_isSharedCheck_3866_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_val_3851_);
lean_dec(v_next_3846_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3866_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
uint8_t v___x_3855_; 
v___x_3855_ = lean_nat_dec_lt(v_val_3851_, v_upperBound_3847_);
if (v___x_3855_ == 0)
{
lean_del_object(v___x_3853_);
lean_dec(v_val_3851_);
lean_del_object(v___x_3849_);
lean_dec(v_upperBound_3847_);
return v_b_3845_;
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3859_; 
v___x_3856_ = lean_unsigned_to_nat(1u);
v___x_3857_ = lean_nat_add(v_val_3851_, v___x_3856_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 0, v___x_3857_);
v___x_3859_ = v___x_3853_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3857_);
v___x_3859_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3861_; 
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3859_);
v___x_3861_ = v___x_3849_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_upperBound_3847_);
v___x_3861_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_array_push(v_b_3845_, v_val_3851_);
v_a_3844_ = v___x_3861_;
v_b_3845_ = v___x_3862_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_n_3869_, lean_object* v_f_3870_, lean_object* v_xs_3871_, lean_object* v_k_3872_, lean_object* v_acc_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
uint8_t v___x_3877_; 
v___x_3877_ = lean_nat_dec_lt(v_k_3872_, v_n_3869_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_dec(v_k_3872_);
lean_dec_ref(v_f_3870_);
v___x_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3878_, 0, v_acc_3873_);
lean_ctor_set(v___x_3878_, 1, v___y_3874_);
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
return v___x_3879_;
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = lean_array_fget_borrowed(v_xs_3871_, v_k_3872_);
lean_inc_ref(v_f_3870_);
lean_inc_ref(v___y_3875_);
lean_inc(v___x_3880_);
v___x_3881_ = lean_apply_4(v_f_3870_, v___x_3880_, v___y_3874_, v___y_3875_, lean_box(0));
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v_fst_3883_; lean_object* v_snd_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v_fst_3883_ = lean_ctor_get(v_a_3882_, 0);
lean_inc(v_fst_3883_);
v_snd_3884_ = lean_ctor_get(v_a_3882_, 1);
lean_inc(v_snd_3884_);
lean_dec(v_a_3882_);
v___x_3885_ = lean_unsigned_to_nat(1u);
v___x_3886_ = lean_nat_add(v_k_3872_, v___x_3885_);
lean_dec(v_k_3872_);
v___x_3887_ = lean_array_push(v_acc_3873_, v_fst_3883_);
v_k_3872_ = v___x_3886_;
v_acc_3873_ = v___x_3887_;
v___y_3874_ = v_snd_3884_;
goto _start;
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec_ref(v_acc_3873_);
lean_dec(v_k_3872_);
lean_dec_ref(v_f_3870_);
v_a_3889_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3881_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3881_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object* v_n_3897_, lean_object* v_f_3898_, lean_object* v_xs_3899_, lean_object* v_k_3900_, lean_object* v_acc_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_3897_, v_f_3898_, v_xs_3899_, v_k_3900_, v_acc_3901_, v___y_3902_, v___y_3903_);
lean_dec_ref(v___y_3903_);
lean_dec_ref(v_xs_3899_);
lean_dec(v_n_3897_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object* v_upperBound_3906_, lean_object* v_fst_3907_, lean_object* v___x_3908_, lean_object* v_leanOpts_3909_, lean_object* v_a_3910_, lean_object* v_b_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_fst_3916_; lean_object* v_snd_3917_; uint8_t v___x_3921_; 
v___x_3921_ = lean_nat_dec_lt(v_a_3910_, v_upperBound_3906_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
lean_dec(v_a_3910_);
lean_dec_ref(v_leanOpts_3909_);
v___x_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3922_, 0, v_b_3911_);
lean_ctor_set(v___x_3922_, 1, v___y_3912_);
v___x_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
return v___x_3923_;
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = lean_array_fget_borrowed(v_fst_3907_, v_a_3910_);
lean_inc(v___x_3924_);
v___x_3925_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_3924_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3979_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3928_ = v___x_3925_;
v_isShared_3929_ = v_isSharedCheck_3979_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3925_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3979_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v_snd_3930_; lean_object* v___x_3931_; lean_object* v_opts_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_snd_3930_ = lean_ctor_get(v_a_3926_, 1);
lean_inc(v_snd_3930_);
lean_dec(v_a_3926_);
v___x_3931_ = lean_array_fget_borrowed(v___x_3908_, v_a_3910_);
v_opts_3932_ = lean_ctor_get(v___x_3931_, 4);
v___x_3933_ = lean_unsigned_to_nat(0u);
v___x_3934_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3909_);
lean_inc(v_opts_3932_);
lean_inc(v___x_3924_);
v___x_3935_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_3911_, v___x_3924_, v_opts_3932_, v_leanOpts_3909_, v___x_3921_, v___x_3934_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v_a_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
lean_del_object(v___x_3928_);
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
v_a_3937_ = lean_ctor_get(v___x_3935_, 1);
lean_inc(v_a_3937_);
lean_dec_ref_known(v___x_3935_, 2);
v___x_3938_ = lean_array_get_size(v_a_3937_);
v___x_3939_ = lean_nat_dec_lt(v___x_3933_, v___x_3938_);
if (v___x_3939_ == 0)
{
lean_dec(v_a_3937_);
v_fst_3916_ = v_a_3936_;
v_snd_3917_ = v_snd_3930_;
goto v___jp_3915_;
}
else
{
lean_object* v___x_3940_; size_t v___x_3941_; size_t v___x_3942_; lean_object* v___x_3943_; 
v___x_3940_ = lean_box(0);
v___x_3941_ = ((size_t)0ULL);
v___x_3942_ = lean_usize_of_nat(v___x_3938_);
v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3937_, v___x_3941_, v___x_3942_, v___x_3940_, v___y_3913_);
lean_dec(v_a_3937_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_dec_ref_known(v___x_3943_, 1);
v_fst_3916_ = v_a_3936_;
v_snd_3917_ = v_snd_3930_;
goto v___jp_3915_;
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
lean_dec(v_a_3936_);
lean_dec(v_snd_3930_);
lean_dec(v_a_3910_);
lean_dec_ref(v_leanOpts_3909_);
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3943_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3943_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
}
else
{
lean_object* v_a_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
lean_dec(v_snd_3930_);
lean_dec(v_a_3910_);
lean_dec_ref(v_leanOpts_3909_);
v_a_3952_ = lean_ctor_get(v___x_3935_, 1);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3935_, 2);
v___x_3953_ = lean_array_get_size(v_a_3952_);
v___x_3954_ = lean_nat_dec_lt(v___x_3933_, v___x_3953_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; lean_object* v___x_3957_; 
lean_dec(v_a_3952_);
v___x_3955_ = lean_box(0);
if (v_isShared_3929_ == 0)
{
lean_ctor_set_tag(v___x_3928_, 1);
lean_ctor_set(v___x_3928_, 0, v___x_3955_);
v___x_3957_ = v___x_3928_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3955_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
else
{
lean_object* v___x_3959_; size_t v___x_3960_; size_t v___x_3961_; lean_object* v___x_3962_; 
lean_del_object(v___x_3928_);
v___x_3959_ = lean_box(0);
v___x_3960_ = ((size_t)0ULL);
v___x_3961_ = lean_usize_of_nat(v___x_3953_);
v___x_3962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3952_, v___x_3960_, v___x_3961_, v___x_3959_, v___y_3913_);
lean_dec(v_a_3952_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3969_ == 0)
{
lean_object* v_unused_3970_; 
v_unused_3970_ = lean_ctor_get(v___x_3962_, 0);
lean_dec(v_unused_3970_);
v___x_3964_ = v___x_3962_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_dec(v___x_3962_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
lean_ctor_set_tag(v___x_3964_, 1);
lean_ctor_set(v___x_3964_, 0, v___x_3959_);
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3959_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
v_a_3971_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3962_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3962_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec_ref(v_b_3911_);
lean_dec(v_a_3910_);
lean_dec_ref(v_leanOpts_3909_);
v_a_3980_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3925_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3925_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
v___jp_3915_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = lean_unsigned_to_nat(1u);
v___x_3919_ = lean_nat_add(v_a_3910_, v___x_3918_);
lean_dec(v_a_3910_);
v_a_3910_ = v___x_3919_;
v_b_3911_ = v_fst_3916_;
v___y_3912_ = v_snd_3917_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object* v_upperBound_3988_, lean_object* v_fst_3989_, lean_object* v___x_3990_, lean_object* v_leanOpts_3991_, lean_object* v_a_3992_, lean_object* v_b_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_3988_, v_fst_3989_, v___x_3990_, v_leanOpts_3991_, v_a_3992_, v_b_3993_, v___y_3994_, v___y_3995_);
lean_dec_ref(v___y_3995_);
lean_dec_ref(v___x_3990_);
lean_dec_ref(v_fst_3989_);
lean_dec(v_upperBound_3988_);
return v_res_3997_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(lean_object* v___x_3998_, lean_object* v_x_3999_){
_start:
{
lean_object* v_baseName_4000_; lean_object* v_name_4001_; uint8_t v___x_4002_; 
v_baseName_4000_ = lean_ctor_get(v_x_3999_, 1);
v_name_4001_ = lean_ctor_get(v___x_3998_, 0);
v___x_4002_ = lean_name_eq(v_baseName_4000_, v_name_4001_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___x_4003_, lean_object* v_x_4004_){
_start:
{
uint8_t v_res_4005_; lean_object* v_r_4006_; 
v_res_4005_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(v___x_4003_, v_x_4004_);
lean_dec_ref(v_x_4004_);
lean_dec_ref(v___x_4003_);
v_r_4006_ = lean_box(v_res_4005_);
return v_r_4006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object* v_pkg_4007_, lean_object* v_leanOpts_4008_, uint8_t v_reconfigure_4009_, lean_object* v_as_4010_, size_t v_i_4011_, size_t v_stop_4012_, lean_object* v_b_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
uint8_t v___x_4017_; 
v___x_4017_ = lean_usize_dec_eq(v_i_4011_, v_stop_4012_);
if (v___x_4017_ == 0)
{
lean_object* v_ws_4018_; lean_object* v_depIdxs_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4116_; 
v_ws_4018_ = lean_ctor_get(v_b_4013_, 0);
v_depIdxs_4019_ = lean_ctor_get(v_b_4013_, 1);
v_isSharedCheck_4116_ = !lean_is_exclusive(v_b_4013_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4021_ = v_b_4013_;
v_isShared_4022_ = v_isSharedCheck_4116_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_depIdxs_4019_);
lean_inc(v_ws_4018_);
lean_dec(v_b_4013_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4116_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v_packages_4023_; size_t v___x_4024_; size_t v___x_4025_; lean_object* v___x_4026_; lean_object* v___f_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_packages_4023_ = lean_ctor_get(v_ws_4018_, 4);
v___x_4024_ = ((size_t)1ULL);
v___x_4025_ = lean_usize_sub(v_i_4011_, v___x_4024_);
v___x_4026_ = lean_array_uget_borrowed(v_as_4010_, v___x_4025_);
lean_inc(v___x_4026_);
v___f_4027_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4027_, 0, v___x_4026_);
v___x_4028_ = lean_unsigned_to_nat(0u);
v___x_4029_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_4027_, v_packages_4023_, v___x_4028_);
if (lean_obj_tag(v___x_4029_) == 1)
{
lean_object* v_val_4030_; lean_object* v___x_4031_; lean_object* v___x_4033_; 
v_val_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_val_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v___x_4031_ = lean_array_push(v_depIdxs_4019_, v_val_4030_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 1, v___x_4031_);
v___x_4033_ = v___x_4021_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_ws_4018_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
v_i_4011_ = v___x_4025_;
v_b_4013_ = v___x_4033_;
goto _start;
}
}
else
{
lean_object* v_baseName_4036_; lean_object* v_name_4037_; lean_object* v_opts_4038_; uint8_t v___x_4039_; 
lean_dec(v___x_4029_);
v_baseName_4036_ = lean_ctor_get(v_pkg_4007_, 1);
v_name_4037_ = lean_ctor_get(v___x_4026_, 0);
v_opts_4038_ = lean_ctor_get(v___x_4026_, 4);
v___x_4039_ = lean_name_eq(v_baseName_4036_, v_name_4037_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; 
lean_inc_ref(v___y_4015_);
lean_inc_ref(v_ws_4018_);
lean_inc(v___x_4026_);
lean_inc_ref(v_pkg_4007_);
v___x_4040_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_4007_, v___x_4026_, v_ws_4018_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4099_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4043_ = v___x_4040_;
v_isShared_4044_ = v_isSharedCheck_4099_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4040_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4099_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v_fst_4045_; lean_object* v_snd_4046_; lean_object* v___x_4047_; lean_object* v_wsIdx_4048_; lean_object* v___x_4049_; 
v_fst_4045_ = lean_ctor_get(v_a_4041_, 0);
lean_inc(v_fst_4045_);
v_snd_4046_ = lean_ctor_get(v_a_4041_, 1);
lean_inc(v_snd_4046_);
lean_dec(v_a_4041_);
v___x_4047_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_4048_ = lean_array_get_size(v_packages_4023_);
lean_inc_ref(v_leanOpts_4008_);
lean_inc(v_opts_4038_);
v___x_4049_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_4018_, v_fst_4045_, v_opts_4038_, v_leanOpts_4008_, v_reconfigure_4009_, v___x_4047_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v_a_4051_; lean_object* v___x_4052_; lean_object* v___x_4054_; 
lean_del_object(v___x_4043_);
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
v_a_4051_ = lean_ctor_get(v___x_4049_, 1);
lean_inc(v_a_4051_);
lean_dec_ref_known(v___x_4049_, 2);
v___x_4052_ = lean_array_push(v_depIdxs_4019_, v_wsIdx_4048_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 1, v___x_4052_);
lean_ctor_set(v___x_4021_, 0, v_a_4050_);
v___x_4054_ = v___x_4021_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4050_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; uint8_t v___x_4056_; 
v___x_4055_ = lean_array_get_size(v_a_4051_);
v___x_4056_ = lean_nat_dec_lt(v___x_4028_, v___x_4055_);
if (v___x_4056_ == 0)
{
lean_dec(v_a_4051_);
v_i_4011_ = v___x_4025_;
v_b_4013_ = v___x_4054_;
v___y_4014_ = v_snd_4046_;
goto _start;
}
else
{
lean_object* v___x_4058_; size_t v___x_4059_; size_t v___x_4060_; lean_object* v___x_4061_; 
v___x_4058_ = lean_box(0);
v___x_4059_ = ((size_t)0ULL);
v___x_4060_ = lean_usize_of_nat(v___x_4055_);
v___x_4061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4051_, v___x_4059_, v___x_4060_, v___x_4058_, v___y_4015_);
lean_dec(v_a_4051_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_dec_ref_known(v___x_4061_, 1);
v_i_4011_ = v___x_4025_;
v_b_4013_ = v___x_4054_;
v___y_4014_ = v_snd_4046_;
goto _start;
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec_ref(v___x_4054_);
lean_dec(v_snd_4046_);
lean_dec_ref(v_leanOpts_4008_);
lean_dec_ref(v_pkg_4007_);
v_a_4063_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4061_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4061_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
}
}
else
{
lean_object* v_a_4072_; lean_object* v___x_4073_; uint8_t v___x_4074_; 
lean_dec(v_snd_4046_);
lean_del_object(v___x_4021_);
lean_dec_ref(v_depIdxs_4019_);
lean_dec_ref(v_leanOpts_4008_);
lean_dec_ref(v_pkg_4007_);
v_a_4072_ = lean_ctor_get(v___x_4049_, 1);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4049_, 2);
v___x_4073_ = lean_array_get_size(v_a_4072_);
v___x_4074_ = lean_nat_dec_lt(v___x_4028_, v___x_4073_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; lean_object* v___x_4077_; 
lean_dec(v_a_4072_);
v___x_4075_ = lean_box(0);
if (v_isShared_4044_ == 0)
{
lean_ctor_set_tag(v___x_4043_, 1);
lean_ctor_set(v___x_4043_, 0, v___x_4075_);
v___x_4077_ = v___x_4043_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
else
{
lean_object* v___x_4079_; size_t v___x_4080_; size_t v___x_4081_; lean_object* v___x_4082_; 
lean_del_object(v___x_4043_);
v___x_4079_ = lean_box(0);
v___x_4080_ = ((size_t)0ULL);
v___x_4081_ = lean_usize_of_nat(v___x_4073_);
v___x_4082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4072_, v___x_4080_, v___x_4081_, v___x_4079_, v___y_4015_);
lean_dec(v_a_4072_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v___x_4082_, 0);
lean_dec(v_unused_4090_);
v___x_4084_ = v___x_4082_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_dec(v___x_4082_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
lean_ctor_set_tag(v___x_4084_, 1);
lean_ctor_set(v___x_4084_, 0, v___x_4079_);
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4079_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
v_a_4091_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4082_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4082_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_del_object(v___x_4021_);
lean_dec_ref(v_depIdxs_4019_);
lean_dec_ref(v_ws_4018_);
lean_dec_ref(v_leanOpts_4008_);
lean_dec_ref(v_pkg_4007_);
v_a_4100_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4040_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4040_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
lean_inc(v_baseName_4036_);
lean_del_object(v___x_4021_);
lean_dec_ref(v_depIdxs_4019_);
lean_dec_ref(v_ws_4018_);
lean_dec(v___y_4014_);
lean_dec_ref(v_leanOpts_4008_);
lean_dec_ref(v_pkg_4007_);
v___x_4108_ = l_Lean_Name_toString(v_baseName_4036_, v___x_4017_);
v___x_4109_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_4110_ = lean_string_append(v___x_4108_, v___x_4109_);
v___x_4111_ = 3;
v___x_4112_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4112_, 0, v___x_4110_);
lean_ctor_set_uint8(v___x_4112_, sizeof(void*)*1, v___x_4111_);
lean_inc_ref(v___y_4015_);
v___x_4113_ = lean_apply_2(v___y_4015_, v___x_4112_, lean_box(0));
v___x_4114_ = lean_box(0);
v___x_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
return v___x_4115_;
}
}
}
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_dec_ref(v_leanOpts_4008_);
lean_dec_ref(v_pkg_4007_);
v___x_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4117_, 0, v_b_4013_);
lean_ctor_set(v___x_4117_, 1, v___y_4014_);
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
return v___x_4118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___boxed(lean_object* v_pkg_4119_, lean_object* v_leanOpts_4120_, lean_object* v_reconfigure_4121_, lean_object* v_as_4122_, lean_object* v_i_4123_, lean_object* v_stop_4124_, lean_object* v_b_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
uint8_t v_reconfigure_boxed_4129_; size_t v_i_boxed_4130_; size_t v_stop_boxed_4131_; lean_object* v_res_4132_; 
v_reconfigure_boxed_4129_ = lean_unbox(v_reconfigure_4121_);
v_i_boxed_4130_ = lean_unbox_usize(v_i_4123_);
lean_dec(v_i_4123_);
v_stop_boxed_4131_ = lean_unbox_usize(v_stop_4124_);
lean_dec(v_stop_4124_);
v_res_4132_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4119_, v_leanOpts_4120_, v_reconfigure_boxed_4129_, v_as_4122_, v_i_boxed_4130_, v_stop_boxed_4131_, v_b_4125_, v___y_4126_, v___y_4127_);
lean_dec_ref(v___y_4127_);
lean_dec_ref(v_as_4122_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object* v_leanOpts_4133_, uint8_t v_reconfigure_4134_, lean_object* v_ws_4135_, lean_object* v_i_4136_, lean_object* v_next_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_packages_4141_; lean_object* v_pkg_4142_; lean_object* v_ws_4144_; lean_object* v_depIdxs_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v_____x_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v_depConfigs_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v_s_4166_; lean_object* v___x_4167_; uint8_t v___x_4168_; 
v_packages_4141_ = lean_ctor_get(v_ws_4135_, 4);
v_pkg_4142_ = lean_array_fget(v_packages_4141_, v_i_4136_);
lean_dec(v_i_4136_);
v_depConfigs_4163_ = lean_ctor_get(v_pkg_4142_, 12);
v___x_4164_ = lean_array_get_size(v_depConfigs_4163_);
v___x_4165_ = lean_mk_empty_array_with_capacity(v___x_4164_);
lean_inc_ref(v___x_4165_);
lean_inc_ref(v_ws_4135_);
v_s_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_4166_, 0, v_ws_4135_);
lean_ctor_set(v_s_4166_, 1, v___x_4165_);
v___x_4167_ = lean_unsigned_to_nat(0u);
v___x_4168_ = lean_nat_dec_le(v___x_4164_, v___x_4164_);
if (v___x_4168_ == 0)
{
uint8_t v___x_4169_; 
v___x_4169_ = lean_nat_dec_lt(v___x_4167_, v___x_4164_);
if (v___x_4169_ == 0)
{
lean_object* v_ws_4170_; lean_object* v_packages_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; 
lean_dec_ref_known(v_s_4166_, 2);
v_ws_4170_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4135_, v_pkg_4142_, v___x_4165_);
v_packages_4171_ = lean_ctor_get(v_ws_4170_, 4);
v___x_4172_ = lean_array_get_size(v_packages_4171_);
v___x_4173_ = lean_nat_dec_lt(v_next_4137_, v___x_4172_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
lean_dec(v_next_4137_);
lean_dec_ref(v_leanOpts_4133_);
v___x_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4174_, 0, v_ws_4170_);
lean_ctor_set(v___x_4174_, 1, v___y_4138_);
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
return v___x_4175_;
}
else
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4176_ = lean_unsigned_to_nat(1u);
v___x_4177_ = lean_nat_add(v_next_4137_, v___x_4176_);
v_ws_4135_ = v_ws_4170_;
v_i_4136_ = v_next_4137_;
v_next_4137_ = v___x_4177_;
goto _start;
}
}
else
{
size_t v___x_4179_; size_t v___x_4180_; lean_object* v___x_4181_; 
lean_dec_ref(v___x_4165_);
lean_dec_ref(v_ws_4135_);
v___x_4179_ = lean_usize_of_nat(v___x_4164_);
v___x_4180_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4133_);
lean_inc(v_pkg_4142_);
v___x_4181_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4142_, v_leanOpts_4133_, v_reconfigure_4134_, v_depConfigs_4163_, v___x_4179_, v___x_4180_, v_s_4166_, v___y_4138_, v___y_4139_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v_fst_4183_; lean_object* v_snd_4184_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4181_, 1);
v_fst_4183_ = lean_ctor_get(v_a_4182_, 0);
lean_inc(v_fst_4183_);
v_snd_4184_ = lean_ctor_get(v_a_4182_, 1);
lean_inc(v_snd_4184_);
lean_dec(v_a_4182_);
v_____x_4158_ = v_fst_4183_;
v___y_4159_ = v_snd_4184_;
v___y_4160_ = v___y_4139_;
goto v___jp_4157_;
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_dec(v_pkg_4142_);
lean_dec(v_next_4137_);
lean_dec_ref(v_leanOpts_4133_);
v_a_4185_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4181_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4181_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
}
else
{
uint8_t v___x_4193_; 
v___x_4193_ = lean_nat_dec_lt(v___x_4167_, v___x_4164_);
if (v___x_4193_ == 0)
{
lean_dec_ref_known(v_s_4166_, 2);
v_ws_4144_ = v_ws_4135_;
v_depIdxs_4145_ = v___x_4165_;
v___y_4146_ = v___y_4138_;
v___y_4147_ = v___y_4139_;
goto v___jp_4143_;
}
else
{
size_t v___x_4194_; size_t v___x_4195_; lean_object* v___x_4196_; 
lean_dec_ref(v___x_4165_);
lean_dec_ref(v_ws_4135_);
v___x_4194_ = lean_usize_of_nat(v___x_4164_);
v___x_4195_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4133_);
lean_inc(v_pkg_4142_);
v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4142_, v_leanOpts_4133_, v_reconfigure_4134_, v_depConfigs_4163_, v___x_4194_, v___x_4195_, v_s_4166_, v___y_4138_, v___y_4139_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v_fst_4198_; lean_object* v_snd_4199_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v_fst_4198_ = lean_ctor_get(v_a_4197_, 0);
lean_inc(v_fst_4198_);
v_snd_4199_ = lean_ctor_get(v_a_4197_, 1);
lean_inc(v_snd_4199_);
lean_dec(v_a_4197_);
v_____x_4158_ = v_fst_4198_;
v___y_4159_ = v_snd_4199_;
v___y_4160_ = v___y_4139_;
goto v___jp_4157_;
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec(v_pkg_4142_);
lean_dec(v_next_4137_);
lean_dec_ref(v_leanOpts_4133_);
v_a_4200_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4196_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4196_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
v___jp_4143_:
{
lean_object* v_ws_4148_; lean_object* v_packages_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; 
v_ws_4148_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4144_, v_pkg_4142_, v_depIdxs_4145_);
v_packages_4149_ = lean_ctor_get(v_ws_4148_, 4);
v___x_4150_ = lean_array_get_size(v_packages_4149_);
v___x_4151_ = lean_nat_dec_lt(v_next_4137_, v___x_4150_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
lean_dec(v_next_4137_);
lean_dec_ref(v_leanOpts_4133_);
v___x_4152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4152_, 0, v_ws_4148_);
lean_ctor_set(v___x_4152_, 1, v___y_4146_);
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
return v___x_4153_;
}
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = lean_unsigned_to_nat(1u);
v___x_4155_ = lean_nat_add(v_next_4137_, v___x_4154_);
v_ws_4135_ = v_ws_4148_;
v_i_4136_ = v_next_4137_;
v_next_4137_ = v___x_4155_;
v___y_4138_ = v___y_4146_;
v___y_4139_ = v___y_4147_;
goto _start;
}
}
v___jp_4157_:
{
lean_object* v_ws_4161_; lean_object* v_depIdxs_4162_; 
v_ws_4161_ = lean_ctor_get(v_____x_4158_, 0);
lean_inc_ref(v_ws_4161_);
v_depIdxs_4162_ = lean_ctor_get(v_____x_4158_, 1);
lean_inc_ref(v_depIdxs_4162_);
lean_dec_ref(v_____x_4158_);
v_ws_4144_ = v_ws_4161_;
v_depIdxs_4145_ = v_depIdxs_4162_;
v___y_4146_ = v___y_4159_;
v___y_4147_ = v___y_4160_;
goto v___jp_4143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object* v_leanOpts_4208_, lean_object* v_reconfigure_4209_, lean_object* v_ws_4210_, lean_object* v_i_4211_, lean_object* v_next_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
uint8_t v_reconfigure_boxed_4216_; lean_object* v_res_4217_; 
v_reconfigure_boxed_4216_ = lean_unbox(v_reconfigure_4209_);
v_res_4217_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4208_, v_reconfigure_boxed_4216_, v_ws_4210_, v_i_4211_, v_next_4212_, v___y_4213_, v___y_4214_);
lean_dec_ref(v___y_4214_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4220_, lean_object* v_toUpdate_4221_, lean_object* v_leanOpts_4222_, uint8_t v_updateToolchain_4223_, lean_object* v_a_4224_){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = lean_box(1);
v___x_4227_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4224_, v_ws_4220_, v_toUpdate_4221_, v___x_4226_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v_snd_4229_; uint8_t v___x_4230_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v_snd_4229_ = lean_ctor_get(v_a_4228_, 1);
lean_inc(v_snd_4229_);
lean_dec(v_a_4228_);
v___x_4230_ = 1;
if (v_updateToolchain_4223_ == 0)
{
lean_object* v_packages_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v_wsIdx_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v_packages_4231_ = lean_ctor_get(v_ws_4220_, 4);
v___x_4232_ = lean_unsigned_to_nat(0u);
v___x_4233_ = lean_array_fget_borrowed(v_packages_4231_, v___x_4232_);
v_wsIdx_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_wsIdx_4234_);
v___x_4235_ = lean_array_get_size(v_packages_4231_);
v___x_4236_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4222_, v___x_4230_, v_ws_4220_, v_wsIdx_4234_, v___x_4235_, v_snd_4229_, v_a_4224_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4254_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4254_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4254_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v_fst_4241_; lean_object* v_snd_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4253_; 
v_fst_4241_ = lean_ctor_get(v_a_4237_, 0);
v_snd_4242_ = lean_ctor_get(v_a_4237_, 1);
v_isSharedCheck_4253_ = !lean_is_exclusive(v_a_4237_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4244_ = v_a_4237_;
v_isShared_4245_ = v_isSharedCheck_4253_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_snd_4242_);
lean_inc(v_fst_4241_);
lean_dec(v_a_4237_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4253_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; lean_object* v___x_4248_; 
v___x_4246_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4241_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4246_);
v___x_4248_ = v___x_4244_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_snd_4242_);
v___x_4248_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
lean_object* v___x_4250_; 
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4248_);
v___x_4250_ = v___x_4239_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
else
{
return v___x_4236_;
}
}
else
{
lean_object* v_packages_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v_depConfigs_4258_; lean_object* v___x_4259_; lean_object* v___f_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_packages_4255_ = lean_ctor_get(v_ws_4220_, 4);
v___x_4256_ = lean_unsigned_to_nat(0u);
v___x_4257_ = lean_array_fget_borrowed(v_packages_4255_, v___x_4256_);
v_depConfigs_4258_ = lean_ctor_get(v___x_4257_, 12);
v___x_4259_ = lean_box(v_updateToolchain_4223_);
lean_inc_ref(v_ws_4220_);
lean_inc(v___x_4257_);
v___f_4260_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4260_, 0, v___x_4257_);
lean_closure_set(v___f_4260_, 1, v___x_4259_);
lean_closure_set(v___f_4260_, 2, v_ws_4220_);
v___x_4261_ = lean_array_get_size(v_depConfigs_4258_);
lean_inc_ref(v_depConfigs_4258_);
v___x_4262_ = l_Array_reverse___redArg(v_depConfigs_4258_);
v___x_4263_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4264_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4261_, v___f_4260_, v___x_4262_, v___x_4256_, v___x_4263_, v_snd_4229_, v_a_4224_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v_fst_4266_; lean_object* v_snd_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4339_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4264_, 1);
v_fst_4266_ = lean_ctor_get(v_a_4265_, 0);
v_snd_4267_ = lean_ctor_get(v_a_4265_, 1);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_a_4265_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4269_ = v_a_4265_;
v_isShared_4270_ = v_isSharedCheck_4339_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_snd_4267_);
lean_inc(v_fst_4266_);
lean_dec(v_a_4265_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4339_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4271_; 
lean_inc_ref(v_ws_4220_);
v___x_4271_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4224_, v_ws_4220_, v_fst_4266_);
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_dec_ref_known(v___x_4271_, 1);
v___x_4272_ = lean_array_get_size(v_packages_4255_);
lean_inc_ref(v_leanOpts_4222_);
v___x_4273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4261_, v_fst_4266_, v___x_4262_, v_leanOpts_4222_, v___x_4256_, v_ws_4220_, v_snd_4267_, v_a_4224_);
lean_dec_ref(v___x_4262_);
lean_dec(v_fst_4266_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4322_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4276_ = v___x_4273_;
v_isShared_4277_ = v_isSharedCheck_4322_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4273_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4322_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v_fst_4278_; lean_object* v_snd_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4321_; 
v_fst_4278_ = lean_ctor_get(v_a_4274_, 0);
v_snd_4279_ = lean_ctor_get(v_a_4274_, 1);
v_isSharedCheck_4321_ = !lean_is_exclusive(v_a_4274_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4281_ = v_a_4274_;
v_isShared_4282_ = v_isSharedCheck_4321_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_snd_4279_);
lean_inc(v_fst_4278_);
lean_dec(v_a_4274_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4321_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v_packages_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4288_; 
v_packages_4283_ = lean_ctor_get(v_fst_4278_, 4);
v___x_4284_ = lean_array_get_size(v_packages_4283_);
v___x_4285_ = lean_array_fget(v_packages_4283_, v___x_4256_);
v___x_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4272_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 1, v___x_4284_);
lean_ctor_set(v___x_4269_, 0, v___x_4286_);
v___x_4288_ = v___x_4269_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4286_);
lean_ctor_set(v_reuseFailAlloc_4320_, 1, v___x_4284_);
v___x_4288_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; uint8_t v___x_4291_; 
v___x_4289_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4288_, v___x_4263_);
v___x_4290_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4278_, v___x_4285_, v___x_4289_);
v___x_4291_ = lean_nat_dec_eq(v___x_4272_, v___x_4284_);
if (v___x_4291_ == 0)
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
lean_del_object(v___x_4281_);
lean_del_object(v___x_4276_);
v___x_4292_ = lean_unsigned_to_nat(1u);
v___x_4293_ = lean_nat_add(v___x_4272_, v___x_4292_);
v___x_4294_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4222_, v___x_4230_, v___x_4290_, v___x_4272_, v___x_4293_, v_snd_4279_, v_a_4224_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4312_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4297_ = v___x_4294_;
v_isShared_4298_ = v_isSharedCheck_4312_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4312_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v_fst_4299_; lean_object* v_snd_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4311_; 
v_fst_4299_ = lean_ctor_get(v_a_4295_, 0);
v_snd_4300_ = lean_ctor_get(v_a_4295_, 1);
v_isSharedCheck_4311_ = !lean_is_exclusive(v_a_4295_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4302_ = v_a_4295_;
v_isShared_4303_ = v_isSharedCheck_4311_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_snd_4300_);
lean_inc(v_fst_4299_);
lean_dec(v_a_4295_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4311_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4304_; lean_object* v___x_4306_; 
v___x_4304_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4299_);
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v___x_4304_);
v___x_4306_ = v___x_4302_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4304_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v_snd_4300_);
v___x_4306_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4308_; 
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4306_);
v___x_4308_ = v___x_4297_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4306_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
}
else
{
return v___x_4294_;
}
}
else
{
lean_object* v___x_4313_; lean_object* v___x_4315_; 
lean_dec_ref(v_leanOpts_4222_);
v___x_4313_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4290_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 0, v___x_4313_);
v___x_4315_ = v___x_4281_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4313_);
lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_snd_4279_);
v___x_4315_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
lean_object* v___x_4317_; 
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 0, v___x_4315_);
v___x_4317_ = v___x_4276_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4315_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_del_object(v___x_4269_);
lean_dec_ref(v_leanOpts_4222_);
v_a_4323_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4273_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4273_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_del_object(v___x_4269_);
lean_dec(v_snd_4267_);
lean_dec(v_fst_4266_);
lean_dec_ref(v___x_4262_);
lean_dec_ref(v_leanOpts_4222_);
lean_dec_ref(v_ws_4220_);
v_a_4331_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4271_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4271_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_dec_ref(v___x_4262_);
lean_dec_ref(v_leanOpts_4222_);
lean_dec_ref(v_ws_4220_);
v_a_4340_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4264_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4264_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec_ref(v_leanOpts_4222_);
lean_dec_ref(v_ws_4220_);
v_a_4348_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4227_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4227_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4356_, lean_object* v_toUpdate_4357_, lean_object* v_leanOpts_4358_, lean_object* v_updateToolchain_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_){
_start:
{
uint8_t v_updateToolchain_boxed_4362_; lean_object* v_res_4363_; 
v_updateToolchain_boxed_4362_ = lean_unbox(v_updateToolchain_4359_);
v_res_4363_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4356_, v_toUpdate_4357_, v_leanOpts_4358_, v_updateToolchain_boxed_4362_, v_a_4360_);
lean_dec_ref(v_a_4360_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_leanOpts_4364_, uint8_t v_reconfigure_4365_, lean_object* v_ws_4366_, lean_object* v_i_4367_, lean_object* v_i__lt_4368_, lean_object* v_next_4369_, lean_object* v_lt__next_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4364_, v_reconfigure_4365_, v_ws_4366_, v_i_4367_, v_next_4369_, v___y_4371_, v___y_4372_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_leanOpts_4375_, lean_object* v_reconfigure_4376_, lean_object* v_ws_4377_, lean_object* v_i_4378_, lean_object* v_i__lt_4379_, lean_object* v_next_4380_, lean_object* v_lt__next_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
uint8_t v_reconfigure_boxed_4385_; lean_object* v_res_4386_; 
v_reconfigure_boxed_4385_ = lean_unbox(v_reconfigure_4376_);
v_res_4386_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4375_, v_reconfigure_boxed_4385_, v_ws_4377_, v_i_4378_, v_i__lt_4379_, v_next_4380_, v_lt__next_4381_, v___y_4382_, v___y_4383_);
lean_dec_ref(v___y_4383_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_00_u03b1_4387_, lean_object* v_00_u03b2_4388_, lean_object* v_n_4389_, lean_object* v_f_4390_, lean_object* v_xs_4391_, lean_object* v_k_4392_, lean_object* v_h_4393_, lean_object* v_acc_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4389_, v_f_4390_, v_xs_4391_, v_k_4392_, v_acc_4394_, v___y_4395_, v___y_4396_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_00_u03b1_4399_, lean_object* v_00_u03b2_4400_, lean_object* v_n_4401_, lean_object* v_f_4402_, lean_object* v_xs_4403_, lean_object* v_k_4404_, lean_object* v_h_4405_, lean_object* v_acc_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_00_u03b1_4399_, v_00_u03b2_4400_, v_n_4401_, v_f_4402_, v_xs_4403_, v_k_4404_, v_h_4405_, v_acc_4406_, v___y_4407_, v___y_4408_);
lean_dec_ref(v___y_4408_);
lean_dec_ref(v_xs_4403_);
lean_dec(v_n_4401_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_inst_4411_, lean_object* v_R_4412_, lean_object* v_a_4413_, lean_object* v_b_4414_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_a_4413_, v_b_4414_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_upperBound_4416_, lean_object* v_fst_4417_, lean_object* v___x_4418_, lean_object* v_leanOpts_4419_, lean_object* v_inst_4420_, lean_object* v_R_4421_, lean_object* v_a_4422_, lean_object* v_b_4423_, lean_object* v_c_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v___x_4428_; 
v___x_4428_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4416_, v_fst_4417_, v___x_4418_, v_leanOpts_4419_, v_a_4422_, v_b_4423_, v___y_4425_, v___y_4426_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_upperBound_4429_, lean_object* v_fst_4430_, lean_object* v___x_4431_, lean_object* v_leanOpts_4432_, lean_object* v_inst_4433_, lean_object* v_R_4434_, lean_object* v_a_4435_, lean_object* v_b_4436_, lean_object* v_c_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4429_, v_fst_4430_, v___x_4431_, v_leanOpts_4432_, v_inst_4433_, v_R_4434_, v_a_4435_, v_b_4436_, v_c_4437_, v___y_4438_, v___y_4439_);
lean_dec_ref(v___y_4439_);
lean_dec_ref(v___x_4431_);
lean_dec_ref(v_fst_4430_);
lean_dec(v_upperBound_4429_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_start_4442_, lean_object* v_pkg_4443_, lean_object* v_leanOpts_4444_, uint8_t v_reconfigure_4445_, lean_object* v_as_4446_, size_t v_i_4447_, size_t v_stop_4448_, lean_object* v_b_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4443_, v_leanOpts_4444_, v_reconfigure_4445_, v_as_4446_, v_i_4447_, v_stop_4448_, v_b_4449_, v___y_4450_, v___y_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_start_4454_, lean_object* v_pkg_4455_, lean_object* v_leanOpts_4456_, lean_object* v_reconfigure_4457_, lean_object* v_as_4458_, lean_object* v_i_4459_, lean_object* v_stop_4460_, lean_object* v_b_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
uint8_t v_reconfigure_boxed_4465_; size_t v_i_boxed_4466_; size_t v_stop_boxed_4467_; lean_object* v_res_4468_; 
v_reconfigure_boxed_4465_ = lean_unbox(v_reconfigure_4457_);
v_i_boxed_4466_ = lean_unbox_usize(v_i_4459_);
lean_dec(v_i_4459_);
v_stop_boxed_4467_ = lean_unbox_usize(v_stop_4460_);
lean_dec(v_stop_4460_);
v_res_4468_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_start_4454_, v_pkg_4455_, v_leanOpts_4456_, v_reconfigure_boxed_4465_, v_as_4458_, v_i_boxed_4466_, v_stop_boxed_4467_, v_b_4461_, v___y_4462_, v___y_4463_);
lean_dec_ref(v___y_4463_);
lean_dec_ref(v_as_4458_);
lean_dec(v_start_4454_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_4469_, lean_object* v_msg_4470_){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v_msg_4470_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object* v_00_u03b2_4472_, lean_object* v_k_4473_, lean_object* v_v_4474_, lean_object* v_t_4475_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_4473_, v_v_4474_, v_t_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object* v_init_4477_, lean_object* v_t_4478_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_4477_, v_t_4478_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4480_, lean_object* v_as_4481_, size_t v_i_4482_, size_t v_stop_4483_, lean_object* v_b_4484_){
_start:
{
lean_object* v___y_4486_; uint8_t v___x_4490_; 
v___x_4490_ = lean_usize_dec_eq(v_i_4482_, v_stop_4483_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; lean_object* v_baseName_4492_; lean_object* v_relConfigFile_4493_; lean_object* v_relManifestFile_4494_; lean_object* v___x_4495_; 
v___x_4491_ = lean_array_uget_borrowed(v_as_4481_, v_i_4482_);
v_baseName_4492_ = lean_ctor_get(v___x_4491_, 1);
v_relConfigFile_4493_ = lean_ctor_get(v___x_4491_, 8);
v_relManifestFile_4494_ = lean_ctor_get(v___x_4491_, 9);
v___x_4495_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4480_, v_baseName_4492_);
if (lean_obj_tag(v___x_4495_) == 0)
{
v___y_4486_ = v_b_4484_;
goto v___jp_4485_;
}
else
{
lean_object* v_val_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4517_; 
v_val_4496_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4498_ = v___x_4495_;
v_isShared_4499_ = v_isSharedCheck_4517_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_val_4496_);
lean_dec(v___x_4495_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4517_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v_name_4500_; lean_object* v_scope_4501_; uint8_t v_inherited_4502_; lean_object* v_src_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4514_; 
v_name_4500_ = lean_ctor_get(v_val_4496_, 0);
v_scope_4501_ = lean_ctor_get(v_val_4496_, 1);
v_inherited_4502_ = lean_ctor_get_uint8(v_val_4496_, sizeof(void*)*5);
v_src_4503_ = lean_ctor_get(v_val_4496_, 4);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_val_4496_);
if (v_isSharedCheck_4514_ == 0)
{
lean_object* v_unused_4515_; lean_object* v_unused_4516_; 
v_unused_4515_ = lean_ctor_get(v_val_4496_, 3);
lean_dec(v_unused_4515_);
v_unused_4516_ = lean_ctor_get(v_val_4496_, 2);
lean_dec(v_unused_4516_);
v___x_4505_ = v_val_4496_;
v_isShared_4506_ = v_isSharedCheck_4514_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_src_4503_);
lean_inc(v_scope_4501_);
lean_inc(v_name_4500_);
lean_dec(v_val_4496_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4514_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4508_; 
lean_inc_ref(v_relManifestFile_4494_);
if (v_isShared_4499_ == 0)
{
lean_ctor_set(v___x_4498_, 0, v_relManifestFile_4494_);
v___x_4508_ = v___x_4498_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_relManifestFile_4494_);
v___x_4508_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4510_; 
lean_inc_ref(v_relConfigFile_4493_);
if (v_isShared_4506_ == 0)
{
lean_ctor_set(v___x_4505_, 3, v___x_4508_);
lean_ctor_set(v___x_4505_, 2, v_relConfigFile_4493_);
v___x_4510_ = v___x_4505_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_name_4500_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_scope_4501_);
lean_ctor_set(v_reuseFailAlloc_4512_, 2, v_relConfigFile_4493_);
lean_ctor_set(v_reuseFailAlloc_4512_, 3, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4512_, 4, v_src_4503_);
lean_ctor_set_uint8(v_reuseFailAlloc_4512_, sizeof(void*)*5, v_inherited_4502_);
v___x_4510_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; 
v___x_4511_ = lean_array_push(v_b_4484_, v___x_4510_);
v___y_4486_ = v___x_4511_;
goto v___jp_4485_;
}
}
}
}
}
}
else
{
return v_b_4484_;
}
v___jp_4485_:
{
size_t v___x_4487_; size_t v___x_4488_; 
v___x_4487_ = ((size_t)1ULL);
v___x_4488_ = lean_usize_add(v_i_4482_, v___x_4487_);
v_i_4482_ = v___x_4488_;
v_b_4484_ = v___y_4486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4518_, lean_object* v_as_4519_, lean_object* v_i_4520_, lean_object* v_stop_4521_, lean_object* v_b_4522_){
_start:
{
size_t v_i_boxed_4523_; size_t v_stop_boxed_4524_; lean_object* v_res_4525_; 
v_i_boxed_4523_ = lean_unbox_usize(v_i_4520_);
lean_dec(v_i_4520_);
v_stop_boxed_4524_ = lean_unbox_usize(v_stop_4521_);
lean_dec(v_stop_4521_);
v_res_4525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4518_, v_as_4519_, v_i_boxed_4523_, v_stop_boxed_4524_, v_b_4522_);
lean_dec_ref(v_as_4519_);
lean_dec(v_entries_4518_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4526_, lean_object* v_entries_4527_){
_start:
{
lean_object* v_packages_4529_; lean_object* v___y_4531_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; uint8_t v___x_4549_; 
v_packages_4529_ = lean_ctor_get(v_ws_4526_, 4);
v___x_4546_ = lean_unsigned_to_nat(0u);
v___x_4547_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4548_ = lean_array_get_size(v_packages_4529_);
v___x_4549_ = lean_nat_dec_lt(v___x_4546_, v___x_4548_);
if (v___x_4549_ == 0)
{
v___y_4531_ = v___x_4547_;
goto v___jp_4530_;
}
else
{
uint8_t v___x_4550_; 
v___x_4550_ = lean_nat_dec_le(v___x_4548_, v___x_4548_);
if (v___x_4550_ == 0)
{
if (v___x_4549_ == 0)
{
v___y_4531_ = v___x_4547_;
goto v___jp_4530_;
}
else
{
size_t v___x_4551_; size_t v___x_4552_; lean_object* v___x_4553_; 
v___x_4551_ = ((size_t)0ULL);
v___x_4552_ = lean_usize_of_nat(v___x_4548_);
v___x_4553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4527_, v_packages_4529_, v___x_4551_, v___x_4552_, v___x_4547_);
v___y_4531_ = v___x_4553_;
goto v___jp_4530_;
}
}
else
{
size_t v___x_4554_; size_t v___x_4555_; lean_object* v___x_4556_; 
v___x_4554_ = ((size_t)0ULL);
v___x_4555_ = lean_usize_of_nat(v___x_4548_);
v___x_4556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4527_, v_packages_4529_, v___x_4554_, v___x_4555_, v___x_4547_);
v___y_4531_ = v___x_4556_;
goto v___jp_4530_;
}
}
v___jp_4530_:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v_config_4534_; lean_object* v_baseName_4535_; lean_object* v_dir_4536_; lean_object* v_relManifestFile_4537_; lean_object* v_toWorkspaceConfig_4538_; uint8_t v_fixedToolchain_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v_manifest_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4532_ = lean_unsigned_to_nat(0u);
v___x_4533_ = lean_array_fget_borrowed(v_packages_4529_, v___x_4532_);
v_config_4534_ = lean_ctor_get(v___x_4533_, 6);
v_baseName_4535_ = lean_ctor_get(v___x_4533_, 1);
v_dir_4536_ = lean_ctor_get(v___x_4533_, 4);
v_relManifestFile_4537_ = lean_ctor_get(v___x_4533_, 9);
v_toWorkspaceConfig_4538_ = lean_ctor_get(v_config_4534_, 0);
v_fixedToolchain_4539_ = lean_ctor_get_uint8(v_config_4534_, sizeof(void*)*28 + 6);
v___x_4540_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4538_);
v___x_4541_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4538_);
v___x_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
lean_inc(v_baseName_4535_);
v_manifest_4543_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4543_, 0, v_baseName_4535_);
lean_ctor_set(v_manifest_4543_, 1, v___x_4540_);
lean_ctor_set(v_manifest_4543_, 2, v___x_4542_);
lean_ctor_set(v_manifest_4543_, 3, v___y_4531_);
lean_ctor_set_uint8(v_manifest_4543_, sizeof(void*)*4, v_fixedToolchain_4539_);
lean_inc_ref(v_relManifestFile_4537_);
lean_inc_ref(v_dir_4536_);
v___x_4544_ = l_Lake_joinRelative(v_dir_4536_, v_relManifestFile_4537_);
v___x_4545_ = l_Lake_Manifest_save(v_manifest_4543_, v___x_4544_);
lean_dec_ref(v___x_4544_);
return v___x_4545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4557_, lean_object* v_entries_4558_, lean_object* v_a_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4557_, v_entries_4558_);
lean_dec(v_entries_4558_);
lean_dec_ref(v_ws_4557_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4561_, lean_object* v_as_4562_, size_t v_i_4563_, size_t v_stop_4564_, lean_object* v_b_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
lean_object* v_a_4570_; lean_object* v___y_4575_; uint8_t v___x_4577_; 
v___x_4577_ = lean_usize_dec_eq(v_i_4563_, v_stop_4564_);
if (v___x_4577_ == 0)
{
lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_6568__overap_4580_; lean_object* v___x_4581_; 
v___x_4578_ = lean_unsigned_to_nat(0u);
v___x_4579_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_6568__overap_4580_ = lean_array_uget_borrowed(v_as_4562_, v_i_4563_);
lean_inc(v___x_6568__overap_4580_);
lean_inc(v___y_4566_);
lean_inc_ref(v_pkg_4561_);
v___x_4581_ = lean_apply_4(v___x_6568__overap_4580_, v_pkg_4561_, v___y_4566_, v___x_4579_, lean_box(0));
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v_a_4583_; lean_object* v___x_4584_; uint8_t v___x_4585_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc(v_a_4582_);
v_a_4583_ = lean_ctor_get(v___x_4581_, 1);
lean_inc(v_a_4583_);
lean_dec_ref_known(v___x_4581_, 2);
v___x_4584_ = lean_array_get_size(v_a_4583_);
v___x_4585_ = lean_nat_dec_lt(v___x_4578_, v___x_4584_);
if (v___x_4585_ == 0)
{
lean_dec(v_a_4583_);
v_a_4570_ = v_a_4582_;
goto v___jp_4569_;
}
else
{
lean_object* v___x_4586_; size_t v___x_4587_; size_t v___x_4588_; lean_object* v___x_4589_; 
v___x_4586_ = lean_box(0);
v___x_4587_ = ((size_t)0ULL);
v___x_4588_ = lean_usize_of_nat(v___x_4584_);
v___x_4589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4583_, v___x_4587_, v___x_4588_, v___x_4586_, v___y_4567_);
lean_dec(v_a_4583_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_dec_ref_known(v___x_4589_, 1);
v_a_4570_ = v_a_4582_;
goto v___jp_4569_;
}
else
{
lean_dec(v_a_4582_);
v___y_4575_ = v___x_4589_;
goto v___jp_4574_;
}
}
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4591_; uint8_t v___x_4592_; 
v_a_4590_ = lean_ctor_get(v___x_4581_, 1);
lean_inc(v_a_4590_);
lean_dec_ref_known(v___x_4581_, 2);
v___x_4591_ = lean_array_get_size(v_a_4590_);
v___x_4592_ = lean_nat_dec_lt(v___x_4578_, v___x_4591_);
if (v___x_4592_ == 0)
{
lean_object* v___x_4593_; lean_object* v___x_4594_; 
lean_dec(v_a_4590_);
lean_dec_ref(v_pkg_4561_);
v___x_4593_ = lean_box(0);
v___x_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4594_, 0, v___x_4593_);
return v___x_4594_;
}
else
{
lean_object* v___x_4595_; size_t v___x_4596_; size_t v___x_4597_; lean_object* v___x_4598_; 
v___x_4595_ = lean_box(0);
v___x_4596_ = ((size_t)0ULL);
v___x_4597_ = lean_usize_of_nat(v___x_4591_);
v___x_4598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4590_, v___x_4596_, v___x_4597_, v___x_4595_, v___y_4567_);
lean_dec(v_a_4590_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4605_; 
lean_dec_ref(v_pkg_4561_);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4605_ == 0)
{
lean_object* v_unused_4606_; 
v_unused_4606_ = lean_ctor_get(v___x_4598_, 0);
lean_dec(v_unused_4606_);
v___x_4600_ = v___x_4598_;
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
else
{
lean_dec(v___x_4598_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4603_; 
if (v_isShared_4601_ == 0)
{
lean_ctor_set_tag(v___x_4600_, 1);
lean_ctor_set(v___x_4600_, 0, v___x_4595_);
v___x_4603_ = v___x_4600_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v___x_4595_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
else
{
v___y_4575_ = v___x_4598_;
goto v___jp_4574_;
}
}
}
}
else
{
lean_object* v___x_4607_; 
lean_dec_ref(v_pkg_4561_);
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v_b_4565_);
return v___x_4607_;
}
v___jp_4569_:
{
size_t v___x_4571_; size_t v___x_4572_; 
v___x_4571_ = ((size_t)1ULL);
v___x_4572_ = lean_usize_add(v_i_4563_, v___x_4571_);
v_i_4563_ = v___x_4572_;
v_b_4565_ = v_a_4570_;
goto _start;
}
v___jp_4574_:
{
if (lean_obj_tag(v___y_4575_) == 0)
{
lean_object* v_a_4576_; 
v_a_4576_ = lean_ctor_get(v___y_4575_, 0);
lean_inc(v_a_4576_);
lean_dec_ref_known(v___y_4575_, 1);
v_a_4570_ = v_a_4576_;
goto v___jp_4569_;
}
else
{
lean_dec_ref(v_pkg_4561_);
return v___y_4575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4608_, lean_object* v_as_4609_, lean_object* v_i_4610_, lean_object* v_stop_4611_, lean_object* v_b_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
size_t v_i_boxed_4616_; size_t v_stop_boxed_4617_; lean_object* v_res_4618_; 
v_i_boxed_4616_ = lean_unbox_usize(v_i_4610_);
lean_dec(v_i_4610_);
v_stop_boxed_4617_ = lean_unbox_usize(v_stop_4611_);
lean_dec(v_stop_4611_);
v_res_4618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4608_, v_as_4609_, v_i_boxed_4616_, v_stop_boxed_4617_, v_b_4612_, v___y_4613_, v___y_4614_);
lean_dec_ref(v___y_4614_);
lean_dec(v___y_4613_);
lean_dec_ref(v_as_4609_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_){
_start:
{
lean_object* v_baseName_4624_; lean_object* v_postUpdateHooks_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; uint8_t v___x_4628_; 
v_baseName_4624_ = lean_ctor_get(v_pkg_4620_, 1);
v_postUpdateHooks_4625_ = lean_ctor_get(v_pkg_4620_, 20);
lean_inc_ref(v_postUpdateHooks_4625_);
v___x_4626_ = lean_array_get_size(v_postUpdateHooks_4625_);
v___x_4627_ = lean_unsigned_to_nat(0u);
v___x_4628_ = lean_nat_dec_eq(v___x_4626_, v___x_4627_);
if (v___x_4628_ == 0)
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; uint8_t v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; 
lean_inc(v_baseName_4624_);
v___x_4629_ = l_Lean_Name_toString(v_baseName_4624_, v___x_4628_);
v___x_4630_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4631_ = lean_string_append(v___x_4629_, v___x_4630_);
v___x_4632_ = 1;
v___x_4633_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4633_, 0, v___x_4631_);
lean_ctor_set_uint8(v___x_4633_, sizeof(void*)*1, v___x_4632_);
lean_inc_ref(v_a_4622_);
v___x_4634_ = lean_apply_2(v_a_4622_, v___x_4633_, lean_box(0));
v___x_4635_ = lean_box(0);
v___x_4636_ = lean_nat_dec_lt(v___x_4627_, v___x_4626_);
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; 
lean_dec_ref(v_postUpdateHooks_4625_);
lean_dec_ref(v_pkg_4620_);
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4635_);
return v___x_4637_;
}
else
{
uint8_t v___x_4638_; 
v___x_4638_ = lean_nat_dec_le(v___x_4626_, v___x_4626_);
if (v___x_4638_ == 0)
{
if (v___x_4636_ == 0)
{
lean_object* v___x_4639_; 
lean_dec_ref(v_postUpdateHooks_4625_);
lean_dec_ref(v_pkg_4620_);
v___x_4639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4635_);
return v___x_4639_;
}
else
{
size_t v___x_4640_; size_t v___x_4641_; lean_object* v___x_4642_; 
v___x_4640_ = ((size_t)0ULL);
v___x_4641_ = lean_usize_of_nat(v___x_4626_);
v___x_4642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4620_, v_postUpdateHooks_4625_, v___x_4640_, v___x_4641_, v___x_4635_, v_a_4621_, v_a_4622_);
lean_dec_ref(v_postUpdateHooks_4625_);
return v___x_4642_;
}
}
else
{
size_t v___x_4643_; size_t v___x_4644_; lean_object* v___x_4645_; 
v___x_4643_ = ((size_t)0ULL);
v___x_4644_ = lean_usize_of_nat(v___x_4626_);
v___x_4645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4620_, v_postUpdateHooks_4625_, v___x_4643_, v___x_4644_, v___x_4635_, v_a_4621_, v_a_4622_);
lean_dec_ref(v_postUpdateHooks_4625_);
return v___x_4645_;
}
}
}
else
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
lean_dec_ref(v_postUpdateHooks_4625_);
lean_dec_ref(v_pkg_4620_);
v___x_4646_ = lean_box(0);
v___x_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4646_);
return v___x_4647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4648_, v_a_4649_, v_a_4650_);
lean_dec_ref(v_a_4650_);
lean_dec(v_a_4649_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4653_, lean_object* v_ws_4654_, lean_object* v_toUpdate_4655_, lean_object* v_leanOpts_4656_, uint8_t v_updateToolchain_4657_){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4659_ = lean_box(1);
v___x_4660_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4653_, v_ws_4654_, v_toUpdate_4655_, v___x_4659_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v_snd_4662_; uint8_t v___x_4663_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
v_snd_4662_ = lean_ctor_get(v_a_4661_, 1);
lean_inc(v_snd_4662_);
lean_dec(v_a_4661_);
v___x_4663_ = 1;
if (v_updateToolchain_4657_ == 0)
{
lean_object* v_packages_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v_wsIdx_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v_packages_4664_ = lean_ctor_get(v_ws_4654_, 4);
v___x_4665_ = lean_unsigned_to_nat(0u);
v___x_4666_ = lean_array_fget_borrowed(v_packages_4664_, v___x_4665_);
v_wsIdx_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc(v_wsIdx_4667_);
v___x_4668_ = lean_array_get_size(v_packages_4664_);
v___x_4669_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4656_, v___x_4663_, v_ws_4654_, v_wsIdx_4667_, v___x_4668_, v_snd_4662_, v_a_4653_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4687_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4669_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4672_ = v___x_4669_;
v_isShared_4673_ = v_isSharedCheck_4687_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4669_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4687_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v_fst_4674_; lean_object* v_snd_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4686_; 
v_fst_4674_ = lean_ctor_get(v_a_4670_, 0);
v_snd_4675_ = lean_ctor_get(v_a_4670_, 1);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_a_4670_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4677_ = v_a_4670_;
v_isShared_4678_ = v_isSharedCheck_4686_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_snd_4675_);
lean_inc(v_fst_4674_);
lean_dec(v_a_4670_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4686_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4679_; lean_object* v___x_4681_; 
v___x_4679_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4674_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 0, v___x_4679_);
v___x_4681_ = v___x_4677_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4679_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v_snd_4675_);
v___x_4681_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
lean_object* v___x_4683_; 
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 0, v___x_4681_);
v___x_4683_ = v___x_4672_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v___x_4681_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
}
else
{
return v___x_4669_;
}
}
else
{
lean_object* v_packages_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v_depConfigs_4691_; lean_object* v___x_4692_; lean_object* v___f_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v_packages_4688_ = lean_ctor_get(v_ws_4654_, 4);
v___x_4689_ = lean_unsigned_to_nat(0u);
v___x_4690_ = lean_array_fget_borrowed(v_packages_4688_, v___x_4689_);
v_depConfigs_4691_ = lean_ctor_get(v___x_4690_, 12);
v___x_4692_ = lean_box(v_updateToolchain_4657_);
lean_inc_ref(v_ws_4654_);
lean_inc(v___x_4690_);
v___f_4693_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4693_, 0, v___x_4690_);
lean_closure_set(v___f_4693_, 1, v___x_4692_);
lean_closure_set(v___f_4693_, 2, v_ws_4654_);
v___x_4694_ = lean_array_get_size(v_depConfigs_4691_);
lean_inc_ref(v_depConfigs_4691_);
v___x_4695_ = l_Array_reverse___redArg(v_depConfigs_4691_);
v___x_4696_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4697_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4694_, v___f_4693_, v___x_4695_, v___x_4689_, v___x_4696_, v_snd_4662_, v_a_4653_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v_fst_4699_; lean_object* v_snd_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4772_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4698_);
lean_dec_ref_known(v___x_4697_, 1);
v_fst_4699_ = lean_ctor_get(v_a_4698_, 0);
v_snd_4700_ = lean_ctor_get(v_a_4698_, 1);
v_isSharedCheck_4772_ = !lean_is_exclusive(v_a_4698_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4702_ = v_a_4698_;
v_isShared_4703_ = v_isSharedCheck_4772_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_snd_4700_);
lean_inc(v_fst_4699_);
lean_dec(v_a_4698_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4772_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4704_; 
lean_inc_ref(v_ws_4654_);
v___x_4704_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4653_, v_ws_4654_, v_fst_4699_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_object* v___x_4705_; lean_object* v___x_4706_; 
lean_dec_ref_known(v___x_4704_, 1);
v___x_4705_ = lean_array_get_size(v_packages_4688_);
lean_inc_ref(v_leanOpts_4656_);
v___x_4706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4694_, v_fst_4699_, v___x_4695_, v_leanOpts_4656_, v___x_4689_, v_ws_4654_, v_snd_4700_, v_a_4653_);
lean_dec_ref(v___x_4695_);
lean_dec(v_fst_4699_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4755_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4709_ = v___x_4706_;
v_isShared_4710_ = v_isSharedCheck_4755_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___x_4706_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4755_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v_fst_4711_; lean_object* v_snd_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4754_; 
v_fst_4711_ = lean_ctor_get(v_a_4707_, 0);
v_snd_4712_ = lean_ctor_get(v_a_4707_, 1);
v_isSharedCheck_4754_ = !lean_is_exclusive(v_a_4707_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4714_ = v_a_4707_;
v_isShared_4715_ = v_isSharedCheck_4754_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_snd_4712_);
lean_inc(v_fst_4711_);
lean_dec(v_a_4707_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4754_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v_packages_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4721_; 
v_packages_4716_ = lean_ctor_get(v_fst_4711_, 4);
v___x_4717_ = lean_array_get_size(v_packages_4716_);
v___x_4718_ = lean_array_fget(v_packages_4716_, v___x_4689_);
v___x_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4705_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 1, v___x_4717_);
lean_ctor_set(v___x_4702_, 0, v___x_4719_);
v___x_4721_ = v___x_4702_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4719_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v___x_4717_);
v___x_4721_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; uint8_t v___x_4724_; 
v___x_4722_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4721_, v___x_4696_);
v___x_4723_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4711_, v___x_4718_, v___x_4722_);
v___x_4724_ = lean_nat_dec_eq(v___x_4705_, v___x_4717_);
if (v___x_4724_ == 0)
{
lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
lean_del_object(v___x_4714_);
lean_del_object(v___x_4709_);
v___x_4725_ = lean_unsigned_to_nat(1u);
v___x_4726_ = lean_nat_add(v___x_4705_, v___x_4725_);
v___x_4727_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4656_, v___x_4663_, v___x_4723_, v___x_4705_, v___x_4726_, v_snd_4712_, v_a_4653_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4745_; 
v_a_4728_ = lean_ctor_get(v___x_4727_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4727_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4730_ = v___x_4727_;
v_isShared_4731_ = v_isSharedCheck_4745_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4727_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4745_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v_fst_4732_; lean_object* v_snd_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4744_; 
v_fst_4732_ = lean_ctor_get(v_a_4728_, 0);
v_snd_4733_ = lean_ctor_get(v_a_4728_, 1);
v_isSharedCheck_4744_ = !lean_is_exclusive(v_a_4728_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4735_ = v_a_4728_;
v_isShared_4736_ = v_isSharedCheck_4744_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_snd_4733_);
lean_inc(v_fst_4732_);
lean_dec(v_a_4728_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4744_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4737_; lean_object* v___x_4739_; 
v___x_4737_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4732_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 0, v___x_4737_);
v___x_4739_ = v___x_4735_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4737_);
lean_ctor_set(v_reuseFailAlloc_4743_, 1, v_snd_4733_);
v___x_4739_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
lean_object* v___x_4741_; 
if (v_isShared_4731_ == 0)
{
lean_ctor_set(v___x_4730_, 0, v___x_4739_);
v___x_4741_ = v___x_4730_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4739_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
}
else
{
return v___x_4727_;
}
}
else
{
lean_object* v___x_4746_; lean_object* v___x_4748_; 
lean_dec_ref(v_leanOpts_4656_);
v___x_4746_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4723_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 0, v___x_4746_);
v___x_4748_ = v___x_4714_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4746_);
lean_ctor_set(v_reuseFailAlloc_4752_, 1, v_snd_4712_);
v___x_4748_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
lean_object* v___x_4750_; 
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 0, v___x_4748_);
v___x_4750_ = v___x_4709_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v___x_4748_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_del_object(v___x_4702_);
lean_dec_ref(v_leanOpts_4656_);
v_a_4756_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4706_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4706_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
lean_del_object(v___x_4702_);
lean_dec(v_snd_4700_);
lean_dec(v_fst_4699_);
lean_dec_ref(v___x_4695_);
lean_dec_ref(v_leanOpts_4656_);
lean_dec_ref(v_ws_4654_);
v_a_4764_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4704_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4704_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
}
else
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4780_; 
lean_dec_ref(v___x_4695_);
lean_dec_ref(v_leanOpts_4656_);
lean_dec_ref(v_ws_4654_);
v_a_4773_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4775_ = v___x_4697_;
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v___x_4697_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
}
else
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4788_; 
lean_dec_ref(v_leanOpts_4656_);
lean_dec_ref(v_ws_4654_);
v_a_4781_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4783_ = v___x_4660_;
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v___x_4660_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4786_; 
if (v_isShared_4784_ == 0)
{
v___x_4786_ = v___x_4783_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4781_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4789_, lean_object* v_ws_4790_, lean_object* v_toUpdate_4791_, lean_object* v_leanOpts_4792_, lean_object* v_updateToolchain_4793_, lean_object* v_a_4794_){
_start:
{
uint8_t v_updateToolchain_boxed_4795_; lean_object* v_res_4796_; 
v_updateToolchain_boxed_4795_ = lean_unbox(v_updateToolchain_4793_);
v_res_4796_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4789_, v_ws_4790_, v_toUpdate_4791_, v_leanOpts_4792_, v_updateToolchain_boxed_4795_);
lean_dec_ref(v_a_4789_);
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4797_, size_t v_i_4798_, size_t v_stop_4799_, lean_object* v_b_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_){
_start:
{
uint8_t v___x_4804_; 
v___x_4804_ = lean_usize_dec_eq(v_i_4798_, v_stop_4799_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4805_ = lean_array_uget_borrowed(v_as_4797_, v_i_4798_);
lean_inc(v___x_4805_);
v___x_4806_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4805_, v___y_4801_, v___y_4802_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; size_t v___x_4808_; size_t v___x_4809_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
lean_inc(v_a_4807_);
lean_dec_ref_known(v___x_4806_, 1);
v___x_4808_ = ((size_t)1ULL);
v___x_4809_ = lean_usize_add(v_i_4798_, v___x_4808_);
v_i_4798_ = v___x_4809_;
v_b_4800_ = v_a_4807_;
goto _start;
}
else
{
return v___x_4806_;
}
}
else
{
lean_object* v___x_4811_; 
v___x_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4811_, 0, v_b_4800_);
return v___x_4811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4812_, lean_object* v_i_4813_, lean_object* v_stop_4814_, lean_object* v_b_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
size_t v_i_boxed_4819_; size_t v_stop_boxed_4820_; lean_object* v_res_4821_; 
v_i_boxed_4819_ = lean_unbox_usize(v_i_4813_);
lean_dec(v_i_4813_);
v_stop_boxed_4820_ = lean_unbox_usize(v_stop_4814_);
lean_dec(v_stop_4814_);
v_res_4821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4812_, v_i_boxed_4819_, v_stop_boxed_4820_, v_b_4815_, v___y_4816_, v___y_4817_);
lean_dec_ref(v___y_4817_);
lean_dec(v___y_4816_);
lean_dec_ref(v_as_4812_);
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4822_, lean_object* v_toUpdate_4823_, lean_object* v_leanOpts_4824_, uint8_t v_updateToolchain_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4826_, v_ws_4822_, v_toUpdate_4823_, v_leanOpts_4824_, v_updateToolchain_4825_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v_fst_4830_; lean_object* v_snd_4831_; lean_object* v___y_4833_; lean_object* v___x_4850_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref_known(v___x_4828_, 1);
v_fst_4830_ = lean_ctor_get(v_a_4829_, 0);
lean_inc(v_fst_4830_);
v_snd_4831_ = lean_ctor_get(v_a_4829_, 1);
lean_inc(v_snd_4831_);
lean_dec(v_a_4829_);
v___x_4850_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4830_, v_snd_4831_);
lean_dec(v_snd_4831_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4872_; 
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4872_ == 0)
{
lean_object* v_unused_4873_; 
v_unused_4873_ = lean_ctor_get(v___x_4850_, 0);
lean_dec(v_unused_4873_);
v___x_4852_ = v___x_4850_;
v_isShared_4853_ = v_isSharedCheck_4872_;
goto v_resetjp_4851_;
}
else
{
lean_dec(v___x_4850_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4872_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v_packages_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; uint8_t v___x_4857_; 
v_packages_4854_ = lean_ctor_get(v_fst_4830_, 4);
v___x_4855_ = lean_unsigned_to_nat(0u);
v___x_4856_ = lean_array_get_size(v_packages_4854_);
v___x_4857_ = lean_nat_dec_lt(v___x_4855_, v___x_4856_);
if (v___x_4857_ == 0)
{
lean_object* v___x_4859_; 
if (v_isShared_4853_ == 0)
{
lean_ctor_set(v___x_4852_, 0, v_fst_4830_);
v___x_4859_ = v___x_4852_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_fst_4830_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
else
{
lean_object* v___x_4861_; uint8_t v___x_4862_; 
v___x_4861_ = lean_box(0);
v___x_4862_ = lean_nat_dec_le(v___x_4856_, v___x_4856_);
if (v___x_4862_ == 0)
{
if (v___x_4857_ == 0)
{
lean_object* v___x_4864_; 
if (v_isShared_4853_ == 0)
{
lean_ctor_set(v___x_4852_, 0, v_fst_4830_);
v___x_4864_ = v___x_4852_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_fst_4830_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
else
{
size_t v___x_4866_; size_t v___x_4867_; lean_object* v___x_4868_; 
lean_del_object(v___x_4852_);
v___x_4866_ = ((size_t)0ULL);
v___x_4867_ = lean_usize_of_nat(v___x_4856_);
v___x_4868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4854_, v___x_4866_, v___x_4867_, v___x_4861_, v_fst_4830_, v_a_4826_);
v___y_4833_ = v___x_4868_;
goto v___jp_4832_;
}
}
else
{
size_t v___x_4869_; size_t v___x_4870_; lean_object* v___x_4871_; 
lean_del_object(v___x_4852_);
v___x_4869_ = ((size_t)0ULL);
v___x_4870_ = lean_usize_of_nat(v___x_4856_);
v___x_4871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4854_, v___x_4869_, v___x_4870_, v___x_4861_, v_fst_4830_, v_a_4826_);
v___y_4833_ = v___x_4871_;
goto v___jp_4832_;
}
}
}
}
else
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4886_; 
lean_dec(v_fst_4830_);
v_a_4874_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4876_ = v___x_4850_;
v_isShared_4877_ = v_isSharedCheck_4886_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4850_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4886_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4878_; uint8_t v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4884_; 
v___x_4878_ = lean_io_error_to_string(v_a_4874_);
v___x_4879_ = 3;
v___x_4880_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4880_, 0, v___x_4878_);
lean_ctor_set_uint8(v___x_4880_, sizeof(void*)*1, v___x_4879_);
lean_inc_ref(v_a_4826_);
v___x_4881_ = lean_apply_2(v_a_4826_, v___x_4880_, lean_box(0));
v___x_4882_ = lean_box(0);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v___x_4882_);
v___x_4884_ = v___x_4876_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4882_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
v___jp_4832_:
{
if (lean_obj_tag(v___y_4833_) == 0)
{
lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
v_isSharedCheck_4840_ = !lean_is_exclusive(v___y_4833_);
if (v_isSharedCheck_4840_ == 0)
{
lean_object* v_unused_4841_; 
v_unused_4841_ = lean_ctor_get(v___y_4833_, 0);
lean_dec(v_unused_4841_);
v___x_4835_ = v___y_4833_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_dec(v___y_4833_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v_fst_4830_);
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_fst_4830_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
lean_dec(v_fst_4830_);
v_a_4842_ = lean_ctor_get(v___y_4833_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___y_4833_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4844_ = v___y_4833_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___y_4833_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
v_a_4887_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4828_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4828_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4895_, lean_object* v_toUpdate_4896_, lean_object* v_leanOpts_4897_, lean_object* v_updateToolchain_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_){
_start:
{
uint8_t v_updateToolchain_boxed_4901_; lean_object* v_res_4902_; 
v_updateToolchain_boxed_4901_ = lean_unbox(v_updateToolchain_4898_);
v_res_4902_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4895_, v_toUpdate_4896_, v_leanOpts_4897_, v_updateToolchain_boxed_4901_, v_a_4899_);
lean_dec_ref(v_a_4899_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_4907_, lean_object* v_what_4908_, lean_object* v___y_4909_){
_start:
{
lean_object* v_name_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; uint8_t v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; uint8_t v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v_name_4911_ = lean_ctor_get(v___x_4907_, 0);
lean_inc(v_name_4911_);
lean_dec_ref(v___x_4907_);
v___x_4912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_4913_ = lean_string_append(v___x_4912_, v_what_4908_);
v___x_4914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_4915_ = lean_string_append(v___x_4913_, v___x_4914_);
v___x_4916_ = 1;
v___x_4917_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4911_, v___x_4916_);
v___x_4918_ = lean_string_append(v___x_4915_, v___x_4917_);
v___x_4919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_4920_ = lean_string_append(v___x_4918_, v___x_4919_);
v___x_4921_ = lean_string_append(v___x_4920_, v___x_4917_);
lean_dec_ref(v___x_4917_);
v___x_4922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_4923_ = lean_string_append(v___x_4921_, v___x_4922_);
v___x_4924_ = 2;
v___x_4925_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4925_, 0, v___x_4923_);
lean_ctor_set_uint8(v___x_4925_, sizeof(void*)*1, v___x_4924_);
lean_inc_ref(v___y_4909_);
v___x_4926_ = lean_apply_2(v___y_4909_, v___x_4925_, lean_box(0));
v___x_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4926_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_4928_, lean_object* v_what_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4928_, v_what_4929_, v___y_4930_);
lean_dec_ref(v___y_4930_);
lean_dec_ref(v_what_4929_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_4936_, lean_object* v_as_4937_, size_t v_i_4938_, size_t v_stop_4939_, lean_object* v_b_4940_, lean_object* v___y_4941_){
_start:
{
lean_object* v_a_4944_; lean_object* v___y_4949_; uint8_t v___x_4951_; 
v___x_4951_ = lean_usize_dec_eq(v_i_4938_, v_stop_4939_);
if (v___x_4951_ == 0)
{
lean_object* v___x_4952_; lean_object* v_src_x3f_4953_; 
v___x_4952_ = lean_array_uget_borrowed(v_as_4937_, v_i_4938_);
v_src_x3f_4953_ = lean_ctor_get(v___x_4952_, 3);
if (lean_obj_tag(v_src_x3f_4953_) == 1)
{
lean_object* v_name_4954_; lean_object* v_val_4955_; lean_object* v___x_4956_; 
v_name_4954_ = lean_ctor_get(v___x_4952_, 0);
v_val_4955_ = lean_ctor_get(v_src_x3f_4953_, 0);
v___x_4956_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_4936_, v_name_4954_);
if (lean_obj_tag(v___x_4956_) == 1)
{
lean_object* v_val_4957_; lean_object* v___y_4959_; lean_object* v___y_4963_; 
v_val_4957_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_val_4957_);
lean_dec_ref_known(v___x_4956_, 1);
if (lean_obj_tag(v_val_4955_) == 0)
{
lean_object* v_src_4966_; 
v_src_4966_ = lean_ctor_get(v_val_4957_, 4);
lean_inc_ref(v_src_4966_);
lean_dec(v_val_4957_);
if (lean_obj_tag(v_src_4966_) == 0)
{
lean_object* v___x_4967_; 
lean_dec_ref_known(v_src_4966_, 1);
v___x_4967_ = lean_box(0);
v_a_4944_ = v___x_4967_;
goto v___jp_4943_;
}
else
{
lean_dec_ref(v_src_4966_);
v___y_4963_ = v___y_4941_;
goto v___jp_4962_;
}
}
else
{
lean_object* v_src_4968_; 
v_src_4968_ = lean_ctor_get(v_val_4957_, 4);
lean_inc_ref(v_src_4968_);
lean_dec(v_val_4957_);
if (lean_obj_tag(v_src_4968_) == 1)
{
lean_object* v_url_4969_; lean_object* v_rev_4970_; lean_object* v_url_4971_; lean_object* v_inputRev_x3f_4972_; lean_object* v___y_4974_; uint8_t v___x_4981_; 
v_url_4969_ = lean_ctor_get(v_val_4955_, 0);
v_rev_4970_ = lean_ctor_get(v_val_4955_, 1);
v_url_4971_ = lean_ctor_get(v_src_4968_, 0);
lean_inc_ref(v_url_4971_);
v_inputRev_x3f_4972_ = lean_ctor_get(v_src_4968_, 2);
lean_inc(v_inputRev_x3f_4972_);
lean_dec_ref_known(v_src_4968_, 4);
v___x_4981_ = lean_string_dec_eq(v_url_4969_, v_url_4971_);
lean_dec_ref(v_url_4971_);
if (v___x_4981_ == 0)
{
goto v___jp_4978_;
}
else
{
if (v___x_4951_ == 0)
{
v___y_4974_ = v___y_4941_;
goto v___jp_4973_;
}
else
{
goto v___jp_4978_;
}
}
v___jp_4973_:
{
lean_object* v___x_4975_; uint8_t v___x_4976_; 
v___x_4975_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_4970_);
v___x_4976_ = l_Option_instDecidableEq___redArg(v___x_4975_, v_rev_4970_, v_inputRev_x3f_4972_);
if (v___x_4976_ == 0)
{
v___y_4959_ = v___y_4974_;
goto v___jp_4958_;
}
else
{
if (v___x_4951_ == 0)
{
lean_object* v___x_4977_; 
v___x_4977_ = lean_box(0);
v_a_4944_ = v___x_4977_;
goto v___jp_4943_;
}
else
{
v___y_4959_ = v___y_4974_;
goto v___jp_4958_;
}
}
}
v___jp_4978_:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_4952_);
v___x_4980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4952_, v___x_4979_, v___y_4941_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_dec_ref_known(v___x_4980_, 1);
v___y_4974_ = v___y_4941_;
goto v___jp_4973_;
}
else
{
lean_dec(v_inputRev_x3f_4972_);
return v___x_4980_;
}
}
}
else
{
lean_dec_ref(v_src_4968_);
v___y_4963_ = v___y_4941_;
goto v___jp_4962_;
}
}
v___jp_4958_:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_4952_);
v___x_4961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4952_, v___x_4960_, v___y_4959_);
v___y_4949_ = v___x_4961_;
goto v___jp_4948_;
}
v___jp_4962_:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_4952_);
v___x_4965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4952_, v___x_4964_, v___y_4963_);
v___y_4949_ = v___x_4965_;
goto v___jp_4948_;
}
}
else
{
lean_object* v___x_4982_; 
lean_dec(v___x_4956_);
v___x_4982_ = lean_box(0);
v_a_4944_ = v___x_4982_;
goto v___jp_4943_;
}
}
else
{
lean_object* v___x_4983_; 
v___x_4983_ = lean_box(0);
v_a_4944_ = v___x_4983_;
goto v___jp_4943_;
}
}
else
{
lean_object* v___x_4984_; 
v___x_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4984_, 0, v_b_4940_);
return v___x_4984_;
}
v___jp_4943_:
{
size_t v___x_4945_; size_t v___x_4946_; 
v___x_4945_ = ((size_t)1ULL);
v___x_4946_ = lean_usize_add(v_i_4938_, v___x_4945_);
v_i_4938_ = v___x_4946_;
v_b_4940_ = v_a_4944_;
goto _start;
}
v___jp_4948_:
{
if (lean_obj_tag(v___y_4949_) == 0)
{
lean_object* v_a_4950_; 
v_a_4950_ = lean_ctor_get(v___y_4949_, 0);
lean_inc(v_a_4950_);
lean_dec_ref_known(v___y_4949_, 1);
v_a_4944_ = v_a_4950_;
goto v___jp_4943_;
}
else
{
return v___y_4949_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_4985_, lean_object* v_as_4986_, lean_object* v_i_4987_, lean_object* v_stop_4988_, lean_object* v_b_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
size_t v_i_boxed_4992_; size_t v_stop_boxed_4993_; lean_object* v_res_4994_; 
v_i_boxed_4992_ = lean_unbox_usize(v_i_4987_);
lean_dec(v_i_4987_);
v_stop_boxed_4993_ = lean_unbox_usize(v_stop_4988_);
lean_dec(v_stop_4988_);
v_res_4994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4985_, v_as_4986_, v_i_boxed_4992_, v_stop_boxed_4993_, v_b_4989_, v___y_4990_);
lean_dec_ref(v___y_4990_);
lean_dec_ref(v_as_4986_);
lean_dec(v_pkgEntries_4985_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_4995_, lean_object* v_deps_4996_, lean_object* v_a_4997_){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; uint8_t v___x_5002_; 
v___x_4999_ = lean_unsigned_to_nat(0u);
v___x_5000_ = lean_array_get_size(v_deps_4996_);
v___x_5001_ = lean_box(0);
v___x_5002_ = lean_nat_dec_lt(v___x_4999_, v___x_5000_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; 
v___x_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5003_, 0, v___x_5001_);
return v___x_5003_;
}
else
{
uint8_t v___x_5004_; 
v___x_5004_ = lean_nat_dec_le(v___x_5000_, v___x_5000_);
if (v___x_5004_ == 0)
{
if (v___x_5002_ == 0)
{
lean_object* v___x_5005_; 
v___x_5005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5001_);
return v___x_5005_;
}
else
{
size_t v___x_5006_; size_t v___x_5007_; lean_object* v___x_5008_; 
v___x_5006_ = ((size_t)0ULL);
v___x_5007_ = lean_usize_of_nat(v___x_5000_);
v___x_5008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4995_, v_deps_4996_, v___x_5006_, v___x_5007_, v___x_5001_, v_a_4997_);
return v___x_5008_;
}
}
else
{
size_t v___x_5009_; size_t v___x_5010_; lean_object* v___x_5011_; 
v___x_5009_ = ((size_t)0ULL);
v___x_5010_ = lean_usize_of_nat(v___x_5000_);
v___x_5011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4995_, v_deps_4996_, v___x_5009_, v___x_5010_, v___x_5001_, v_a_4997_);
return v___x_5011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_5012_, lean_object* v_deps_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_5012_, v_deps_5013_, v_a_5014_);
lean_dec_ref(v_a_5014_);
lean_dec_ref(v_deps_5013_);
lean_dec(v_pkgEntries_5012_);
return v_res_5016_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_5017_, lean_object* v_x_5018_){
_start:
{
if (lean_obj_tag(v_x_5017_) == 0)
{
if (lean_obj_tag(v_x_5018_) == 0)
{
uint8_t v___x_5019_; 
v___x_5019_ = 1;
return v___x_5019_;
}
else
{
uint8_t v___x_5020_; 
v___x_5020_ = 0;
return v___x_5020_;
}
}
else
{
if (lean_obj_tag(v_x_5018_) == 0)
{
uint8_t v___x_5021_; 
v___x_5021_ = 0;
return v___x_5021_;
}
else
{
lean_object* v_val_5022_; lean_object* v_val_5023_; uint8_t v___x_5024_; 
v_val_5022_ = lean_ctor_get(v_x_5017_, 0);
v_val_5023_ = lean_ctor_get(v_x_5018_, 0);
v___x_5024_ = lean_string_dec_eq(v_val_5022_, v_val_5023_);
return v___x_5024_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_5025_, lean_object* v_x_5026_){
_start:
{
uint8_t v_res_5027_; lean_object* v_r_5028_; 
v_res_5027_ = l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_5025_, v_x_5026_);
lean_dec(v_x_5026_);
lean_dec(v_x_5025_);
v_r_5028_ = lean_box(v_res_5027_);
return v_r_5028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_pkg_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v_leanOpts_5037_, uint8_t v_reconfigure_5038_, lean_object* v_as_5039_, size_t v_i_5040_, size_t v_stop_5041_, lean_object* v_b_5042_, lean_object* v___y_5043_){
_start:
{
uint8_t v___x_5045_; 
v___x_5045_ = lean_usize_dec_eq(v_i_5040_, v_stop_5041_);
if (v___x_5045_ == 0)
{
lean_object* v_ws_5046_; lean_object* v_depIdxs_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5177_; 
v_ws_5046_ = lean_ctor_get(v_b_5042_, 0);
v_depIdxs_5047_ = lean_ctor_get(v_b_5042_, 1);
v_isSharedCheck_5177_ = !lean_is_exclusive(v_b_5042_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5049_ = v_b_5042_;
v_isShared_5050_ = v_isSharedCheck_5177_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_depIdxs_5047_);
lean_inc(v_ws_5046_);
lean_dec(v_b_5042_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5177_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v_lakeEnv_5051_; lean_object* v_packages_5052_; size_t v___x_5053_; size_t v___x_5054_; lean_object* v___x_5055_; lean_object* v___f_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v_lakeEnv_5051_ = lean_ctor_get(v_ws_5046_, 0);
v_packages_5052_ = lean_ctor_get(v_ws_5046_, 4);
v___x_5053_ = ((size_t)1ULL);
v___x_5054_ = lean_usize_sub(v_i_5040_, v___x_5053_);
v___x_5055_ = lean_array_uget_borrowed(v_as_5039_, v___x_5054_);
lean_inc(v___x_5055_);
v___f_5056_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5056_, 0, v___x_5055_);
v___x_5057_ = lean_unsigned_to_nat(0u);
v___x_5058_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5056_, v_packages_5052_, v___x_5057_);
if (lean_obj_tag(v___x_5058_) == 1)
{
lean_object* v_val_5059_; lean_object* v___x_5060_; lean_object* v___x_5062_; 
v_val_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc(v_val_5059_);
lean_dec_ref_known(v___x_5058_, 1);
v___x_5060_ = lean_array_push(v_depIdxs_5047_, v_val_5059_);
if (v_isShared_5050_ == 0)
{
lean_ctor_set(v___x_5049_, 1, v___x_5060_);
v___x_5062_ = v___x_5049_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_ws_5046_);
lean_ctor_set(v_reuseFailAlloc_5064_, 1, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
v_i_5040_ = v___x_5054_;
v_b_5042_ = v___x_5062_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_5065_; lean_object* v_baseName_5066_; lean_object* v_name_5067_; lean_object* v_opts_5068_; uint8_t v___x_5069_; 
lean_dec(v___x_5058_);
v_wsIdx_5065_ = lean_ctor_get(v_pkg_5034_, 0);
v_baseName_5066_ = lean_ctor_get(v_pkg_5034_, 1);
v_name_5067_ = lean_ctor_get(v___x_5055_, 0);
v_opts_5068_ = lean_ctor_get(v___x_5055_, 4);
v___x_5069_ = lean_name_eq(v_baseName_5066_, v_name_5067_);
if (v___x_5069_ == 0)
{
lean_object* v___x_5070_; 
v___x_5070_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5035_, v_name_5067_);
if (lean_obj_tag(v___x_5070_) == 1)
{
lean_object* v_val_5071_; lean_object* v___x_5072_; lean_object* v_dir_5073_; lean_object* v___x_5074_; 
v_val_5071_ = lean_ctor_get(v___x_5070_, 0);
lean_inc(v_val_5071_);
lean_dec_ref_known(v___x_5070_, 1);
v___x_5072_ = lean_array_fget_borrowed(v_packages_5052_, v___x_5057_);
v_dir_5073_ = lean_ctor_get(v___x_5072_, 4);
lean_inc_ref(v___y_5036_);
lean_inc_ref(v_dir_5073_);
v___x_5074_ = l_Lake_PackageEntry_materialize(v_val_5071_, v_lakeEnv_5051_, v_dir_5073_, v___y_5036_, v___y_5043_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5131_; 
v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5077_ = v___x_5074_;
v_isShared_5078_ = v_isSharedCheck_5131_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_5074_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5131_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5079_; lean_object* v_wsIdx_5080_; lean_object* v___x_5081_; 
v___x_5079_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_5080_ = lean_array_get_size(v_packages_5052_);
lean_inc_ref(v_leanOpts_5037_);
lean_inc(v_opts_5068_);
v___x_5081_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5046_, v_a_5075_, v_opts_5068_, v_leanOpts_5037_, v_reconfigure_5038_, v___x_5079_);
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_object* v_a_5082_; lean_object* v_a_5083_; lean_object* v___x_5084_; lean_object* v___x_5086_; 
lean_del_object(v___x_5077_);
v_a_5082_ = lean_ctor_get(v___x_5081_, 0);
lean_inc(v_a_5082_);
v_a_5083_ = lean_ctor_get(v___x_5081_, 1);
lean_inc(v_a_5083_);
lean_dec_ref_known(v___x_5081_, 2);
v___x_5084_ = lean_array_push(v_depIdxs_5047_, v_wsIdx_5080_);
if (v_isShared_5050_ == 0)
{
lean_ctor_set(v___x_5049_, 1, v___x_5084_);
lean_ctor_set(v___x_5049_, 0, v_a_5082_);
v___x_5086_ = v___x_5049_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5082_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v___x_5084_);
v___x_5086_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
lean_object* v___x_5087_; uint8_t v___x_5088_; 
v___x_5087_ = lean_array_get_size(v_a_5083_);
v___x_5088_ = lean_nat_dec_lt(v___x_5057_, v___x_5087_);
if (v___x_5088_ == 0)
{
lean_dec(v_a_5083_);
v_i_5040_ = v___x_5054_;
v_b_5042_ = v___x_5086_;
goto _start;
}
else
{
lean_object* v___x_5090_; size_t v___x_5091_; size_t v___x_5092_; lean_object* v___x_5093_; 
v___x_5090_ = lean_box(0);
v___x_5091_ = ((size_t)0ULL);
v___x_5092_ = lean_usize_of_nat(v___x_5087_);
v___x_5093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5083_, v___x_5091_, v___x_5092_, v___x_5090_, v___y_5043_);
lean_dec(v_a_5083_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_dec_ref_known(v___x_5093_, 1);
v_i_5040_ = v___x_5054_;
v_b_5042_ = v___x_5086_;
goto _start;
}
else
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
lean_dec_ref(v___x_5086_);
lean_dec_ref(v_leanOpts_5037_);
lean_dec_ref(v___y_5036_);
lean_dec_ref(v_pkg_5034_);
v_a_5095_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_5093_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5093_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
}
}
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5105_; uint8_t v___x_5106_; 
lean_del_object(v___x_5049_);
lean_dec_ref(v_depIdxs_5047_);
lean_dec_ref(v_leanOpts_5037_);
lean_dec_ref(v___y_5036_);
lean_dec_ref(v_pkg_5034_);
v_a_5104_ = lean_ctor_get(v___x_5081_, 1);
lean_inc(v_a_5104_);
lean_dec_ref_known(v___x_5081_, 2);
v___x_5105_ = lean_array_get_size(v_a_5104_);
v___x_5106_ = lean_nat_dec_lt(v___x_5057_, v___x_5105_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5107_; lean_object* v___x_5109_; 
lean_dec(v_a_5104_);
v___x_5107_ = lean_box(0);
if (v_isShared_5078_ == 0)
{
lean_ctor_set_tag(v___x_5077_, 1);
lean_ctor_set(v___x_5077_, 0, v___x_5107_);
v___x_5109_ = v___x_5077_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v___x_5107_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
else
{
lean_object* v___x_5111_; size_t v___x_5112_; size_t v___x_5113_; lean_object* v___x_5114_; 
lean_del_object(v___x_5077_);
v___x_5111_ = lean_box(0);
v___x_5112_ = ((size_t)0ULL);
v___x_5113_ = lean_usize_of_nat(v___x_5105_);
v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5104_, v___x_5112_, v___x_5113_, v___x_5111_, v___y_5043_);
lean_dec(v_a_5104_);
if (lean_obj_tag(v___x_5114_) == 0)
{
lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5114_);
if (v_isSharedCheck_5121_ == 0)
{
lean_object* v_unused_5122_; 
v_unused_5122_ = lean_ctor_get(v___x_5114_, 0);
lean_dec(v_unused_5122_);
v___x_5116_ = v___x_5114_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_dec(v___x_5114_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
lean_ctor_set_tag(v___x_5116_, 1);
lean_ctor_set(v___x_5116_, 0, v___x_5111_);
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v___x_5111_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
else
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5130_; 
v_a_5123_ = lean_ctor_get(v___x_5114_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5114_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5125_ = v___x_5114_;
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5114_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5128_; 
if (v_isShared_5126_ == 0)
{
v___x_5128_ = v___x_5125_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
lean_del_object(v___x_5049_);
lean_dec_ref(v_depIdxs_5047_);
lean_dec_ref(v_ws_5046_);
lean_dec_ref(v_leanOpts_5037_);
lean_dec_ref(v___y_5036_);
lean_dec_ref(v_pkg_5034_);
v_a_5132_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_5074_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_5074_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5137_; 
if (v_isShared_5135_ == 0)
{
v___x_5137_ = v___x_5134_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5132_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
return v___x_5137_;
}
}
}
}
else
{
uint8_t v___x_5140_; 
lean_inc(v_baseName_5066_);
lean_inc(v_wsIdx_5065_);
lean_dec(v___x_5070_);
lean_del_object(v___x_5049_);
lean_dec_ref(v_depIdxs_5047_);
lean_dec_ref(v_ws_5046_);
lean_dec_ref(v_leanOpts_5037_);
lean_dec_ref(v___y_5036_);
lean_dec_ref(v_pkg_5034_);
v___x_5140_ = lean_nat_dec_eq(v_wsIdx_5065_, v___x_5057_);
lean_dec(v_wsIdx_5065_);
if (v___x_5140_ == 0)
{
lean_object* v___x_5141_; uint8_t v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; uint8_t v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; 
v___x_5141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5142_ = 1;
lean_inc(v_name_5067_);
v___x_5143_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5067_, v___x_5142_);
v___x_5144_ = lean_string_append(v___x_5141_, v___x_5143_);
lean_dec_ref(v___x_5143_);
v___x_5145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5146_ = lean_string_append(v___x_5144_, v___x_5145_);
v___x_5147_ = l_Lean_Name_toString(v_baseName_5066_, v___x_5140_);
v___x_5148_ = lean_string_append(v___x_5146_, v___x_5147_);
lean_dec_ref(v___x_5147_);
v___x_5149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5150_ = lean_string_append(v___x_5148_, v___x_5149_);
v___x_5151_ = 3;
v___x_5152_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5152_, 0, v___x_5150_);
lean_ctor_set_uint8(v___x_5152_, sizeof(void*)*1, v___x_5151_);
lean_inc_ref(v___y_5043_);
v___x_5153_ = lean_apply_2(v___y_5043_, v___x_5152_, lean_box(0));
v___x_5154_ = lean_box(0);
v___x_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5155_, 0, v___x_5154_);
return v___x_5155_;
}
else
{
lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; uint8_t v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; 
lean_dec(v_baseName_5066_);
v___x_5156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5067_);
v___x_5157_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5067_, v___x_5140_);
v___x_5158_ = lean_string_append(v___x_5156_, v___x_5157_);
v___x_5159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5160_ = lean_string_append(v___x_5158_, v___x_5159_);
v___x_5161_ = lean_string_append(v___x_5160_, v___x_5157_);
lean_dec_ref(v___x_5157_);
v___x_5162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5163_ = lean_string_append(v___x_5161_, v___x_5162_);
v___x_5164_ = 3;
v___x_5165_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5165_, 0, v___x_5163_);
lean_ctor_set_uint8(v___x_5165_, sizeof(void*)*1, v___x_5164_);
lean_inc_ref(v___y_5043_);
v___x_5166_ = lean_apply_2(v___y_5043_, v___x_5165_, lean_box(0));
v___x_5167_ = lean_box(0);
v___x_5168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5167_);
return v___x_5168_;
}
}
}
else
{
lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; uint8_t v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; 
lean_inc(v_baseName_5066_);
lean_del_object(v___x_5049_);
lean_dec_ref(v_depIdxs_5047_);
lean_dec_ref(v_ws_5046_);
lean_dec_ref(v_leanOpts_5037_);
lean_dec_ref(v___y_5036_);
lean_dec_ref(v_pkg_5034_);
v___x_5169_ = l_Lean_Name_toString(v_baseName_5066_, v___x_5045_);
v___x_5170_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5171_ = lean_string_append(v___x_5169_, v___x_5170_);
v___x_5172_ = 3;
v___x_5173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5173_, 0, v___x_5171_);
lean_ctor_set_uint8(v___x_5173_, sizeof(void*)*1, v___x_5172_);
lean_inc_ref(v___y_5043_);
v___x_5174_ = lean_apply_2(v___y_5043_, v___x_5173_, lean_box(0));
v___x_5175_ = lean_box(0);
v___x_5176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5175_);
return v___x_5176_;
}
}
}
}
else
{
lean_object* v___x_5178_; 
lean_dec_ref(v_leanOpts_5037_);
lean_dec_ref(v___y_5036_);
lean_dec_ref(v_pkg_5034_);
v___x_5178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5178_, 0, v_b_5042_);
return v___x_5178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_pkg_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v_leanOpts_5182_, lean_object* v_reconfigure_5183_, lean_object* v_as_5184_, lean_object* v_i_5185_, lean_object* v_stop_5186_, lean_object* v_b_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_){
_start:
{
uint8_t v_reconfigure_boxed_5190_; size_t v_i_boxed_5191_; size_t v_stop_boxed_5192_; lean_object* v_res_5193_; 
v_reconfigure_boxed_5190_ = lean_unbox(v_reconfigure_5183_);
v_i_boxed_5191_ = lean_unbox_usize(v_i_5185_);
lean_dec(v_i_5185_);
v_stop_boxed_5192_ = lean_unbox_usize(v_stop_5186_);
lean_dec(v_stop_5186_);
v_res_5193_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5179_, v___y_5180_, v___y_5181_, v_leanOpts_5182_, v_reconfigure_boxed_5190_, v_as_5184_, v_i_boxed_5191_, v_stop_boxed_5192_, v_b_5187_, v___y_5188_);
lean_dec_ref(v___y_5188_);
lean_dec_ref(v_as_5184_);
lean_dec(v___y_5180_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_start_5194_, lean_object* v_pkg_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v_leanOpts_5198_, uint8_t v_reconfigure_5199_, lean_object* v_as_5200_, size_t v_i_5201_, size_t v_stop_5202_, lean_object* v_b_5203_, lean_object* v___y_5204_){
_start:
{
uint8_t v___x_5206_; 
v___x_5206_ = lean_usize_dec_eq(v_i_5201_, v_stop_5202_);
if (v___x_5206_ == 0)
{
lean_object* v_ws_5207_; lean_object* v_depIdxs_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5338_; 
v_ws_5207_ = lean_ctor_get(v_b_5203_, 0);
v_depIdxs_5208_ = lean_ctor_get(v_b_5203_, 1);
v_isSharedCheck_5338_ = !lean_is_exclusive(v_b_5203_);
if (v_isSharedCheck_5338_ == 0)
{
v___x_5210_ = v_b_5203_;
v_isShared_5211_ = v_isSharedCheck_5338_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_depIdxs_5208_);
lean_inc(v_ws_5207_);
lean_dec(v_b_5203_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5338_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v_lakeEnv_5212_; lean_object* v_packages_5213_; size_t v___x_5214_; size_t v___x_5215_; lean_object* v___x_5216_; lean_object* v___f_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; 
v_lakeEnv_5212_ = lean_ctor_get(v_ws_5207_, 0);
v_packages_5213_ = lean_ctor_get(v_ws_5207_, 4);
v___x_5214_ = ((size_t)1ULL);
v___x_5215_ = lean_usize_sub(v_i_5201_, v___x_5214_);
v___x_5216_ = lean_array_uget_borrowed(v_as_5200_, v___x_5215_);
lean_inc(v___x_5216_);
v___f_5217_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5217_, 0, v___x_5216_);
v___x_5218_ = lean_unsigned_to_nat(0u);
v___x_5219_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5217_, v_packages_5213_, v___x_5218_);
if (lean_obj_tag(v___x_5219_) == 1)
{
lean_object* v_val_5220_; lean_object* v___x_5221_; lean_object* v___x_5223_; 
v_val_5220_ = lean_ctor_get(v___x_5219_, 0);
lean_inc(v_val_5220_);
lean_dec_ref_known(v___x_5219_, 1);
v___x_5221_ = lean_array_push(v_depIdxs_5208_, v_val_5220_);
if (v_isShared_5211_ == 0)
{
lean_ctor_set(v___x_5210_, 1, v___x_5221_);
v___x_5223_ = v___x_5210_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_ws_5207_);
lean_ctor_set(v_reuseFailAlloc_5225_, 1, v___x_5221_);
v___x_5223_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
lean_object* v___x_5224_; 
v___x_5224_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5195_, v___y_5196_, v___y_5197_, v_leanOpts_5198_, v_reconfigure_5199_, v_as_5200_, v___x_5215_, v_stop_5202_, v___x_5223_, v___y_5204_);
return v___x_5224_;
}
}
else
{
lean_object* v_wsIdx_5226_; lean_object* v_baseName_5227_; lean_object* v_name_5228_; lean_object* v_opts_5229_; uint8_t v___x_5230_; 
lean_dec(v___x_5219_);
v_wsIdx_5226_ = lean_ctor_get(v_pkg_5195_, 0);
v_baseName_5227_ = lean_ctor_get(v_pkg_5195_, 1);
v_name_5228_ = lean_ctor_get(v___x_5216_, 0);
v_opts_5229_ = lean_ctor_get(v___x_5216_, 4);
v___x_5230_ = lean_name_eq(v_baseName_5227_, v_name_5228_);
if (v___x_5230_ == 0)
{
lean_object* v___x_5231_; 
v___x_5231_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5196_, v_name_5228_);
if (lean_obj_tag(v___x_5231_) == 1)
{
lean_object* v_val_5232_; lean_object* v___x_5233_; lean_object* v_dir_5234_; lean_object* v___x_5235_; 
v_val_5232_ = lean_ctor_get(v___x_5231_, 0);
lean_inc(v_val_5232_);
lean_dec_ref_known(v___x_5231_, 1);
v___x_5233_ = lean_array_fget_borrowed(v_packages_5213_, v___x_5218_);
v_dir_5234_ = lean_ctor_get(v___x_5233_, 4);
lean_inc_ref(v___y_5197_);
lean_inc_ref(v_dir_5234_);
v___x_5235_ = l_Lake_PackageEntry_materialize(v_val_5232_, v_lakeEnv_5212_, v_dir_5234_, v___y_5197_, v___y_5204_);
if (lean_obj_tag(v___x_5235_) == 0)
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5292_; 
v_a_5236_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5238_ = v___x_5235_;
v_isShared_5239_ = v_isSharedCheck_5292_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5235_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5292_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5240_; lean_object* v_wsIdx_5241_; lean_object* v___x_5242_; 
v___x_5240_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_5241_ = lean_array_get_size(v_packages_5213_);
lean_inc_ref(v_leanOpts_5198_);
lean_inc(v_opts_5229_);
v___x_5242_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5207_, v_a_5236_, v_opts_5229_, v_leanOpts_5198_, v_reconfigure_5199_, v___x_5240_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_a_5243_; lean_object* v_a_5244_; lean_object* v___x_5245_; lean_object* v___x_5247_; 
lean_del_object(v___x_5238_);
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
lean_inc(v_a_5243_);
v_a_5244_ = lean_ctor_get(v___x_5242_, 1);
lean_inc(v_a_5244_);
lean_dec_ref_known(v___x_5242_, 2);
v___x_5245_ = lean_array_push(v_depIdxs_5208_, v_wsIdx_5241_);
if (v_isShared_5211_ == 0)
{
lean_ctor_set(v___x_5210_, 1, v___x_5245_);
lean_ctor_set(v___x_5210_, 0, v_a_5243_);
v___x_5247_ = v___x_5210_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_a_5243_);
lean_ctor_set(v_reuseFailAlloc_5264_, 1, v___x_5245_);
v___x_5247_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
lean_object* v___x_5248_; uint8_t v___x_5249_; 
v___x_5248_ = lean_array_get_size(v_a_5244_);
v___x_5249_ = lean_nat_dec_lt(v___x_5218_, v___x_5248_);
if (v___x_5249_ == 0)
{
lean_object* v___x_5250_; 
lean_dec(v_a_5244_);
v___x_5250_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5195_, v___y_5196_, v___y_5197_, v_leanOpts_5198_, v_reconfigure_5199_, v_as_5200_, v___x_5215_, v_stop_5202_, v___x_5247_, v___y_5204_);
return v___x_5250_;
}
else
{
lean_object* v___x_5251_; size_t v___x_5252_; size_t v___x_5253_; lean_object* v___x_5254_; 
v___x_5251_ = lean_box(0);
v___x_5252_ = ((size_t)0ULL);
v___x_5253_ = lean_usize_of_nat(v___x_5248_);
v___x_5254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5244_, v___x_5252_, v___x_5253_, v___x_5251_, v___y_5204_);
lean_dec(v_a_5244_);
if (lean_obj_tag(v___x_5254_) == 0)
{
lean_object* v___x_5255_; 
lean_dec_ref_known(v___x_5254_, 1);
v___x_5255_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5195_, v___y_5196_, v___y_5197_, v_leanOpts_5198_, v_reconfigure_5199_, v_as_5200_, v___x_5215_, v_stop_5202_, v___x_5247_, v___y_5204_);
return v___x_5255_;
}
else
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5263_; 
lean_dec_ref(v___x_5247_);
lean_dec_ref(v_leanOpts_5198_);
lean_dec_ref(v___y_5197_);
lean_dec_ref(v_pkg_5195_);
v_a_5256_ = lean_ctor_get(v___x_5254_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5254_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5258_ = v___x_5254_;
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5254_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5261_; 
if (v_isShared_5259_ == 0)
{
v___x_5261_ = v___x_5258_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
v___x_5261_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
return v___x_5261_;
}
}
}
}
}
}
else
{
lean_object* v_a_5265_; lean_object* v___x_5266_; uint8_t v___x_5267_; 
lean_del_object(v___x_5210_);
lean_dec_ref(v_depIdxs_5208_);
lean_dec_ref(v_leanOpts_5198_);
lean_dec_ref(v___y_5197_);
lean_dec_ref(v_pkg_5195_);
v_a_5265_ = lean_ctor_get(v___x_5242_, 1);
lean_inc(v_a_5265_);
lean_dec_ref_known(v___x_5242_, 2);
v___x_5266_ = lean_array_get_size(v_a_5265_);
v___x_5267_ = lean_nat_dec_lt(v___x_5218_, v___x_5266_);
if (v___x_5267_ == 0)
{
lean_object* v___x_5268_; lean_object* v___x_5270_; 
lean_dec(v_a_5265_);
v___x_5268_ = lean_box(0);
if (v_isShared_5239_ == 0)
{
lean_ctor_set_tag(v___x_5238_, 1);
lean_ctor_set(v___x_5238_, 0, v___x_5268_);
v___x_5270_ = v___x_5238_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v___x_5268_);
v___x_5270_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
return v___x_5270_;
}
}
else
{
lean_object* v___x_5272_; size_t v___x_5273_; size_t v___x_5274_; lean_object* v___x_5275_; 
lean_del_object(v___x_5238_);
v___x_5272_ = lean_box(0);
v___x_5273_ = ((size_t)0ULL);
v___x_5274_ = lean_usize_of_nat(v___x_5266_);
v___x_5275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5265_, v___x_5273_, v___x_5274_, v___x_5272_, v___y_5204_);
lean_dec(v_a_5265_);
if (lean_obj_tag(v___x_5275_) == 0)
{
lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5282_; 
v_isSharedCheck_5282_ = !lean_is_exclusive(v___x_5275_);
if (v_isSharedCheck_5282_ == 0)
{
lean_object* v_unused_5283_; 
v_unused_5283_ = lean_ctor_get(v___x_5275_, 0);
lean_dec(v_unused_5283_);
v___x_5277_ = v___x_5275_;
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
else
{
lean_dec(v___x_5275_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5280_; 
if (v_isShared_5278_ == 0)
{
lean_ctor_set_tag(v___x_5277_, 1);
lean_ctor_set(v___x_5277_, 0, v___x_5272_);
v___x_5280_ = v___x_5277_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v___x_5272_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
}
else
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5291_; 
v_a_5284_ = lean_ctor_get(v___x_5275_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5275_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5286_ = v___x_5275_;
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5275_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5289_; 
if (v_isShared_5287_ == 0)
{
v___x_5289_ = v___x_5286_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5300_; 
lean_del_object(v___x_5210_);
lean_dec_ref(v_depIdxs_5208_);
lean_dec_ref(v_ws_5207_);
lean_dec_ref(v_leanOpts_5198_);
lean_dec_ref(v___y_5197_);
lean_dec_ref(v_pkg_5195_);
v_a_5293_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5295_ = v___x_5235_;
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5235_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5298_; 
if (v_isShared_5296_ == 0)
{
v___x_5298_ = v___x_5295_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_a_5293_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
return v___x_5298_;
}
}
}
}
else
{
uint8_t v___x_5301_; 
lean_inc(v_baseName_5227_);
lean_inc(v_wsIdx_5226_);
lean_dec(v___x_5231_);
lean_del_object(v___x_5210_);
lean_dec_ref(v_depIdxs_5208_);
lean_dec_ref(v_ws_5207_);
lean_dec_ref(v_leanOpts_5198_);
lean_dec_ref(v___y_5197_);
lean_dec_ref(v_pkg_5195_);
v___x_5301_ = lean_nat_dec_eq(v_wsIdx_5226_, v___x_5218_);
lean_dec(v_wsIdx_5226_);
if (v___x_5301_ == 0)
{
lean_object* v___x_5302_; uint8_t v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; uint8_t v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___x_5302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5303_ = 1;
lean_inc(v_name_5228_);
v___x_5304_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5228_, v___x_5303_);
v___x_5305_ = lean_string_append(v___x_5302_, v___x_5304_);
lean_dec_ref(v___x_5304_);
v___x_5306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5307_ = lean_string_append(v___x_5305_, v___x_5306_);
v___x_5308_ = l_Lean_Name_toString(v_baseName_5227_, v___x_5301_);
v___x_5309_ = lean_string_append(v___x_5307_, v___x_5308_);
lean_dec_ref(v___x_5308_);
v___x_5310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5311_ = lean_string_append(v___x_5309_, v___x_5310_);
v___x_5312_ = 3;
v___x_5313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5313_, 0, v___x_5311_);
lean_ctor_set_uint8(v___x_5313_, sizeof(void*)*1, v___x_5312_);
lean_inc_ref(v___y_5204_);
v___x_5314_ = lean_apply_2(v___y_5204_, v___x_5313_, lean_box(0));
v___x_5315_ = lean_box(0);
v___x_5316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5316_, 0, v___x_5315_);
return v___x_5316_;
}
else
{
lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; uint8_t v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; 
lean_dec(v_baseName_5227_);
v___x_5317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5228_);
v___x_5318_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5228_, v___x_5301_);
v___x_5319_ = lean_string_append(v___x_5317_, v___x_5318_);
v___x_5320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5321_ = lean_string_append(v___x_5319_, v___x_5320_);
v___x_5322_ = lean_string_append(v___x_5321_, v___x_5318_);
lean_dec_ref(v___x_5318_);
v___x_5323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5324_ = lean_string_append(v___x_5322_, v___x_5323_);
v___x_5325_ = 3;
v___x_5326_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5326_, 0, v___x_5324_);
lean_ctor_set_uint8(v___x_5326_, sizeof(void*)*1, v___x_5325_);
lean_inc_ref(v___y_5204_);
v___x_5327_ = lean_apply_2(v___y_5204_, v___x_5326_, lean_box(0));
v___x_5328_ = lean_box(0);
v___x_5329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5328_);
return v___x_5329_;
}
}
}
else
{
lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; uint8_t v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; 
lean_inc(v_baseName_5227_);
lean_del_object(v___x_5210_);
lean_dec_ref(v_depIdxs_5208_);
lean_dec_ref(v_ws_5207_);
lean_dec_ref(v_leanOpts_5198_);
lean_dec_ref(v___y_5197_);
lean_dec_ref(v_pkg_5195_);
v___x_5330_ = l_Lean_Name_toString(v_baseName_5227_, v___x_5206_);
v___x_5331_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5332_ = lean_string_append(v___x_5330_, v___x_5331_);
v___x_5333_ = 3;
v___x_5334_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5334_, 0, v___x_5332_);
lean_ctor_set_uint8(v___x_5334_, sizeof(void*)*1, v___x_5333_);
lean_inc_ref(v___y_5204_);
v___x_5335_ = lean_apply_2(v___y_5204_, v___x_5334_, lean_box(0));
v___x_5336_ = lean_box(0);
v___x_5337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5336_);
return v___x_5337_;
}
}
}
}
else
{
lean_object* v___x_5339_; 
lean_dec_ref(v_leanOpts_5198_);
lean_dec_ref(v___y_5197_);
lean_dec_ref(v_pkg_5195_);
v___x_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5339_, 0, v_b_5203_);
return v___x_5339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_start_5340_, lean_object* v_pkg_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v_leanOpts_5344_, lean_object* v_reconfigure_5345_, lean_object* v_as_5346_, lean_object* v_i_5347_, lean_object* v_stop_5348_, lean_object* v_b_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_){
_start:
{
uint8_t v_reconfigure_boxed_5352_; size_t v_i_boxed_5353_; size_t v_stop_boxed_5354_; lean_object* v_res_5355_; 
v_reconfigure_boxed_5352_ = lean_unbox(v_reconfigure_5345_);
v_i_boxed_5353_ = lean_unbox_usize(v_i_5347_);
lean_dec(v_i_5347_);
v_stop_boxed_5354_ = lean_unbox_usize(v_stop_5348_);
lean_dec(v_stop_5348_);
v_res_5355_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5340_, v_pkg_5341_, v___y_5342_, v___y_5343_, v_leanOpts_5344_, v_reconfigure_boxed_5352_, v_as_5346_, v_i_boxed_5353_, v_stop_boxed_5354_, v_b_5349_, v___y_5350_);
lean_dec_ref(v___y_5350_);
lean_dec_ref(v_as_5346_);
lean_dec(v___y_5342_);
lean_dec(v_start_5340_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v_leanOpts_5358_, uint8_t v_reconfigure_5359_, lean_object* v_ws_5360_, lean_object* v_i_5361_, lean_object* v_next_5362_, lean_object* v___y_5363_){
_start:
{
lean_object* v_packages_5365_; lean_object* v_pkg_5366_; lean_object* v_ws_5368_; lean_object* v_depIdxs_5369_; lean_object* v___y_5370_; lean_object* v_____x_5380_; lean_object* v___y_5381_; lean_object* v_depConfigs_5384_; lean_object* v_start_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v_s_5388_; lean_object* v___x_5389_; uint8_t v___x_5390_; 
v_packages_5365_ = lean_ctor_get(v_ws_5360_, 4);
v_pkg_5366_ = lean_array_fget(v_packages_5365_, v_i_5361_);
lean_dec(v_i_5361_);
v_depConfigs_5384_ = lean_ctor_get(v_pkg_5366_, 12);
v_start_5385_ = lean_array_get_size(v_packages_5365_);
v___x_5386_ = lean_array_get_size(v_depConfigs_5384_);
v___x_5387_ = lean_mk_empty_array_with_capacity(v___x_5386_);
lean_inc_ref(v___x_5387_);
lean_inc_ref(v_ws_5360_);
v_s_5388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5388_, 0, v_ws_5360_);
lean_ctor_set(v_s_5388_, 1, v___x_5387_);
v___x_5389_ = lean_unsigned_to_nat(0u);
v___x_5390_ = lean_nat_dec_le(v___x_5386_, v___x_5386_);
if (v___x_5390_ == 0)
{
uint8_t v___x_5391_; 
v___x_5391_ = lean_nat_dec_lt(v___x_5389_, v___x_5386_);
if (v___x_5391_ == 0)
{
lean_object* v_ws_5392_; lean_object* v_packages_5393_; lean_object* v___x_5394_; uint8_t v___x_5395_; 
lean_dec_ref_known(v_s_5388_, 2);
v_ws_5392_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5360_, v_pkg_5366_, v___x_5387_);
v_packages_5393_ = lean_ctor_get(v_ws_5392_, 4);
v___x_5394_ = lean_array_get_size(v_packages_5393_);
v___x_5395_ = lean_nat_dec_lt(v_next_5362_, v___x_5394_);
if (v___x_5395_ == 0)
{
lean_object* v___x_5396_; 
lean_dec(v_next_5362_);
lean_dec_ref(v_leanOpts_5358_);
lean_dec_ref(v___y_5357_);
v___x_5396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5396_, 0, v_ws_5392_);
return v___x_5396_;
}
else
{
lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5397_ = lean_unsigned_to_nat(1u);
v___x_5398_ = lean_nat_add(v_next_5362_, v___x_5397_);
v_ws_5360_ = v_ws_5392_;
v_i_5361_ = v_next_5362_;
v_next_5362_ = v___x_5398_;
goto _start;
}
}
else
{
size_t v___x_5400_; size_t v___x_5401_; lean_object* v___x_5402_; 
lean_dec_ref(v___x_5387_);
lean_dec_ref(v_ws_5360_);
v___x_5400_ = lean_usize_of_nat(v___x_5386_);
v___x_5401_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5358_);
lean_inc_ref(v___y_5357_);
lean_inc(v_pkg_5366_);
v___x_5402_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5385_, v_pkg_5366_, v___y_5356_, v___y_5357_, v_leanOpts_5358_, v_reconfigure_5359_, v_depConfigs_5384_, v___x_5400_, v___x_5401_, v_s_5388_, v___y_5363_);
if (lean_obj_tag(v___x_5402_) == 0)
{
lean_object* v_a_5403_; 
v_a_5403_ = lean_ctor_get(v___x_5402_, 0);
lean_inc(v_a_5403_);
lean_dec_ref_known(v___x_5402_, 1);
v_____x_5380_ = v_a_5403_;
v___y_5381_ = v___y_5363_;
goto v___jp_5379_;
}
else
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_dec(v_pkg_5366_);
lean_dec(v_next_5362_);
lean_dec_ref(v_leanOpts_5358_);
lean_dec_ref(v___y_5357_);
v_a_5404_ = lean_ctor_get(v___x_5402_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5402_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5402_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
}
else
{
uint8_t v___x_5412_; 
v___x_5412_ = lean_nat_dec_lt(v___x_5389_, v___x_5386_);
if (v___x_5412_ == 0)
{
lean_dec_ref_known(v_s_5388_, 2);
v_ws_5368_ = v_ws_5360_;
v_depIdxs_5369_ = v___x_5387_;
v___y_5370_ = v___y_5363_;
goto v___jp_5367_;
}
else
{
size_t v___x_5413_; size_t v___x_5414_; lean_object* v___x_5415_; 
lean_dec_ref(v___x_5387_);
lean_dec_ref(v_ws_5360_);
v___x_5413_ = lean_usize_of_nat(v___x_5386_);
v___x_5414_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5358_);
lean_inc_ref(v___y_5357_);
lean_inc(v_pkg_5366_);
v___x_5415_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5385_, v_pkg_5366_, v___y_5356_, v___y_5357_, v_leanOpts_5358_, v_reconfigure_5359_, v_depConfigs_5384_, v___x_5413_, v___x_5414_, v_s_5388_, v___y_5363_);
if (lean_obj_tag(v___x_5415_) == 0)
{
lean_object* v_a_5416_; 
v_a_5416_ = lean_ctor_get(v___x_5415_, 0);
lean_inc(v_a_5416_);
lean_dec_ref_known(v___x_5415_, 1);
v_____x_5380_ = v_a_5416_;
v___y_5381_ = v___y_5363_;
goto v___jp_5379_;
}
else
{
lean_object* v_a_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5424_; 
lean_dec(v_pkg_5366_);
lean_dec(v_next_5362_);
lean_dec_ref(v_leanOpts_5358_);
lean_dec_ref(v___y_5357_);
v_a_5417_ = lean_ctor_get(v___x_5415_, 0);
v_isSharedCheck_5424_ = !lean_is_exclusive(v___x_5415_);
if (v_isSharedCheck_5424_ == 0)
{
v___x_5419_ = v___x_5415_;
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_a_5417_);
lean_dec(v___x_5415_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v___x_5422_; 
if (v_isShared_5420_ == 0)
{
v___x_5422_ = v___x_5419_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_a_5417_);
v___x_5422_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
return v___x_5422_;
}
}
}
}
}
v___jp_5367_:
{
lean_object* v_ws_5371_; lean_object* v_packages_5372_; lean_object* v___x_5373_; uint8_t v___x_5374_; 
v_ws_5371_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5368_, v_pkg_5366_, v_depIdxs_5369_);
v_packages_5372_ = lean_ctor_get(v_ws_5371_, 4);
v___x_5373_ = lean_array_get_size(v_packages_5372_);
v___x_5374_ = lean_nat_dec_lt(v_next_5362_, v___x_5373_);
if (v___x_5374_ == 0)
{
lean_object* v___x_5375_; 
lean_dec(v_next_5362_);
lean_dec_ref(v_leanOpts_5358_);
lean_dec_ref(v___y_5357_);
v___x_5375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5375_, 0, v_ws_5371_);
return v___x_5375_;
}
else
{
lean_object* v___x_5376_; lean_object* v___x_5377_; 
v___x_5376_ = lean_unsigned_to_nat(1u);
v___x_5377_ = lean_nat_add(v_next_5362_, v___x_5376_);
v_ws_5360_ = v_ws_5371_;
v_i_5361_ = v_next_5362_;
v_next_5362_ = v___x_5377_;
v___y_5363_ = v___y_5370_;
goto _start;
}
}
v___jp_5379_:
{
lean_object* v_ws_5382_; lean_object* v_depIdxs_5383_; 
v_ws_5382_ = lean_ctor_get(v_____x_5380_, 0);
lean_inc_ref(v_ws_5382_);
v_depIdxs_5383_ = lean_ctor_get(v_____x_5380_, 1);
lean_inc_ref(v_depIdxs_5383_);
lean_dec_ref(v_____x_5380_);
v_ws_5368_ = v_ws_5382_;
v_depIdxs_5369_ = v_depIdxs_5383_;
v___y_5370_ = v___y_5381_;
goto v___jp_5367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v_leanOpts_5427_, lean_object* v_reconfigure_5428_, lean_object* v_ws_5429_, lean_object* v_i_5430_, lean_object* v_next_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
uint8_t v_reconfigure_boxed_5434_; lean_object* v_res_5435_; 
v_reconfigure_boxed_5434_ = lean_unbox(v_reconfigure_5428_);
v_res_5435_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5425_, v___y_5426_, v_leanOpts_5427_, v_reconfigure_boxed_5434_, v_ws_5429_, v_i_5430_, v_next_5431_, v___y_5432_);
lean_dec_ref(v___y_5432_);
lean_dec(v___y_5425_);
return v_res_5435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(lean_object* v_as_5436_, size_t v_i_5437_, size_t v_stop_5438_, lean_object* v_b_5439_){
_start:
{
uint8_t v___x_5440_; 
v___x_5440_ = lean_usize_dec_eq(v_i_5437_, v_stop_5438_);
if (v___x_5440_ == 0)
{
lean_object* v___x_5441_; lean_object* v_name_5442_; lean_object* v___x_5443_; size_t v___x_5444_; size_t v___x_5445_; 
v___x_5441_ = lean_array_uget_borrowed(v_as_5436_, v_i_5437_);
v_name_5442_ = lean_ctor_get(v___x_5441_, 0);
lean_inc(v___x_5441_);
lean_inc(v_name_5442_);
v___x_5443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5442_, v___x_5441_, v_b_5439_);
v___x_5444_ = ((size_t)1ULL);
v___x_5445_ = lean_usize_add(v_i_5437_, v___x_5444_);
v_i_5437_ = v___x_5445_;
v_b_5439_ = v___x_5443_;
goto _start;
}
else
{
return v_b_5439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2___boxed(lean_object* v_as_5447_, lean_object* v_i_5448_, lean_object* v_stop_5449_, lean_object* v_b_5450_){
_start:
{
size_t v_i_boxed_5451_; size_t v_stop_boxed_5452_; lean_object* v_res_5453_; 
v_i_boxed_5451_ = lean_unbox_usize(v_i_5448_);
lean_dec(v_i_5448_);
v_stop_boxed_5452_ = lean_unbox_usize(v_stop_5449_);
lean_dec(v_stop_5449_);
v_res_5453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5447_, v_i_boxed_5451_, v_stop_boxed_5452_, v_b_5450_);
lean_dec_ref(v_as_5447_);
return v_res_5453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5454_, size_t v_i_5455_, size_t v_stop_5456_, lean_object* v_b_5457_){
_start:
{
uint8_t v___x_5458_; 
v___x_5458_ = lean_usize_dec_eq(v_i_5455_, v_stop_5456_);
if (v___x_5458_ == 0)
{
lean_object* v___x_5459_; lean_object* v_name_5460_; lean_object* v___x_5461_; size_t v___x_5462_; size_t v___x_5463_; lean_object* v___x_5464_; 
v___x_5459_ = lean_array_uget_borrowed(v_as_5454_, v_i_5455_);
v_name_5460_ = lean_ctor_get(v___x_5459_, 0);
lean_inc(v___x_5459_);
lean_inc(v_name_5460_);
v___x_5461_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5460_, v___x_5459_, v_b_5457_);
v___x_5462_ = ((size_t)1ULL);
v___x_5463_ = lean_usize_add(v_i_5455_, v___x_5462_);
v___x_5464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5454_, v___x_5463_, v_stop_5456_, v___x_5461_);
return v___x_5464_;
}
else
{
return v_b_5457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5465_, lean_object* v_i_5466_, lean_object* v_stop_5467_, lean_object* v_b_5468_){
_start:
{
size_t v_i_boxed_5469_; size_t v_stop_boxed_5470_; lean_object* v_res_5471_; 
v_i_boxed_5469_ = lean_unbox_usize(v_i_5466_);
lean_dec(v_i_5466_);
v_stop_boxed_5470_ = lean_unbox_usize(v_stop_5467_);
lean_dec(v_stop_5467_);
v_res_5471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5465_, v_i_boxed_5469_, v_stop_boxed_5470_, v_b_5468_);
lean_dec_ref(v_as_5465_);
return v_res_5471_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5481_, lean_object* v_manifest_5482_, lean_object* v_leanOpts_5483_, uint8_t v_reconfigure_5484_, lean_object* v_overrides_5485_, lean_object* v_a_5486_){
_start:
{
lean_object* v___y_5489_; lean_object* v___y_5490_; lean_object* v___y_5491_; lean_object* v___y_5492_; lean_object* v___y_5493_; lean_object* v___y_5506_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v___y_5510_; lean_object* v___y_5511_; lean_object* v___y_5512_; lean_object* v___y_5520_; lean_object* v___y_5521_; lean_object* v___y_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5537_; lean_object* v___y_5538_; lean_object* v___y_5539_; lean_object* v___y_5540_; lean_object* v_packagesDir_x3f_5583_; lean_object* v_packages_5584_; lean_object* v___y_5586_; lean_object* v___y_5587_; lean_object* v___y_5600_; lean_object* v___x_5608_; lean_object* v___x_5609_; uint8_t v___x_5610_; 
v_packagesDir_x3f_5583_ = lean_ctor_get(v_manifest_5482_, 2);
lean_inc(v_packagesDir_x3f_5583_);
v_packages_5584_ = lean_ctor_get(v_manifest_5482_, 3);
lean_inc_ref(v_packages_5584_);
lean_dec_ref(v_manifest_5482_);
v___x_5608_ = lean_array_get_size(v_packages_5584_);
v___x_5609_ = lean_unsigned_to_nat(0u);
v___x_5610_ = lean_nat_dec_eq(v___x_5608_, v___x_5609_);
if (v___x_5610_ == 0)
{
lean_object* v_packages_5611_; lean_object* v___x_5612_; lean_object* v_config_5613_; lean_object* v_toWorkspaceConfig_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; uint8_t v___x_5618_; 
v_packages_5611_ = lean_ctor_get(v_ws_5481_, 4);
v___x_5612_ = lean_array_fget_borrowed(v_packages_5611_, v___x_5609_);
v_config_5613_ = lean_ctor_get(v___x_5612_, 6);
v_toWorkspaceConfig_5614_ = lean_ctor_get(v_config_5613_, 0);
lean_inc_ref(v_toWorkspaceConfig_5614_);
v___x_5615_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5614_);
v___x_5616_ = l_Lake_mkRelPathString(v___x_5615_);
v___x_5617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5617_, 0, v___x_5616_);
v___x_5618_ = l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5583_, v___x_5617_);
lean_dec_ref_known(v___x_5617_, 1);
if (v___x_5618_ == 0)
{
lean_object* v___x_5619_; lean_object* v___x_5620_; 
v___x_5619_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5486_);
v___x_5620_ = lean_apply_2(v_a_5486_, v___x_5619_, lean_box(0));
v___y_5600_ = v_a_5486_;
goto v___jp_5599_;
}
else
{
v___y_5600_ = v_a_5486_;
goto v___jp_5599_;
}
}
else
{
v___y_5600_ = v_a_5486_;
goto v___jp_5599_;
}
v___jp_5488_:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5494_ = lean_array_get_size(v___y_5493_);
lean_dec_ref(v___y_5493_);
v___x_5495_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5489_, v___y_5492_, v_leanOpts_5483_, v_reconfigure_5484_, v_ws_5481_, v___y_5491_, v___x_5494_, v___y_5490_);
lean_dec(v___y_5489_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5504_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5498_ = v___x_5495_;
v_isShared_5499_ = v_isSharedCheck_5504_;
goto v_resetjp_5497_;
}
else
{
lean_inc(v_a_5496_);
lean_dec(v___x_5495_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5504_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v___x_5500_; lean_object* v___x_5502_; 
v___x_5500_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_a_5496_);
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 0, v___x_5500_);
v___x_5502_ = v___x_5498_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5500_);
v___x_5502_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
return v___x_5502_;
}
}
}
else
{
return v___x_5495_;
}
}
v___jp_5505_:
{
if (lean_obj_tag(v___y_5512_) == 0)
{
lean_dec_ref(v___y_5506_);
v___y_5489_ = v___y_5512_;
v___y_5490_ = v___y_5507_;
v___y_5491_ = v___y_5509_;
v___y_5492_ = v___y_5511_;
v___y_5493_ = v___y_5510_;
goto v___jp_5488_;
}
else
{
lean_object* v___x_5513_; uint8_t v___x_5514_; 
v___x_5513_ = lean_array_get_size(v___y_5506_);
lean_dec_ref(v___y_5506_);
v___x_5514_ = lean_nat_dec_eq(v___x_5513_, v___y_5508_);
if (v___x_5514_ == 0)
{
lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; 
lean_dec_ref(v___y_5511_);
lean_dec_ref(v___y_5510_);
lean_dec(v___y_5509_);
lean_dec_ref(v_leanOpts_5483_);
lean_dec_ref(v_ws_5481_);
v___x_5515_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5507_);
v___x_5516_ = lean_apply_2(v___y_5507_, v___x_5515_, lean_box(0));
v___x_5517_ = lean_box(0);
v___x_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5518_, 0, v___x_5517_);
return v___x_5518_;
}
else
{
v___y_5489_ = v___y_5512_;
v___y_5490_ = v___y_5507_;
v___y_5491_ = v___y_5509_;
v___y_5492_ = v___y_5511_;
v___y_5493_ = v___y_5510_;
goto v___jp_5488_;
}
}
}
v___jp_5519_:
{
lean_object* v___x_5527_; uint8_t v___x_5528_; 
v___x_5527_ = lean_array_get_size(v_overrides_5485_);
v___x_5528_ = lean_nat_dec_lt(v___y_5523_, v___x_5527_);
if (v___x_5528_ == 0)
{
v___y_5506_ = v___y_5520_;
v___y_5507_ = v___y_5521_;
v___y_5508_ = v___y_5523_;
v___y_5509_ = v___y_5522_;
v___y_5510_ = v___y_5525_;
v___y_5511_ = v___y_5524_;
v___y_5512_ = v___y_5526_;
goto v___jp_5505_;
}
else
{
uint8_t v___x_5529_; 
v___x_5529_ = lean_nat_dec_le(v___x_5527_, v___x_5527_);
if (v___x_5529_ == 0)
{
if (v___x_5528_ == 0)
{
v___y_5506_ = v___y_5520_;
v___y_5507_ = v___y_5521_;
v___y_5508_ = v___y_5523_;
v___y_5509_ = v___y_5522_;
v___y_5510_ = v___y_5525_;
v___y_5511_ = v___y_5524_;
v___y_5512_ = v___y_5526_;
goto v___jp_5505_;
}
else
{
size_t v___x_5530_; size_t v___x_5531_; lean_object* v___x_5532_; 
v___x_5530_ = ((size_t)0ULL);
v___x_5531_ = lean_usize_of_nat(v___x_5527_);
v___x_5532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5485_, v___x_5530_, v___x_5531_, v___y_5526_);
v___y_5506_ = v___y_5520_;
v___y_5507_ = v___y_5521_;
v___y_5508_ = v___y_5523_;
v___y_5509_ = v___y_5522_;
v___y_5510_ = v___y_5525_;
v___y_5511_ = v___y_5524_;
v___y_5512_ = v___x_5532_;
goto v___jp_5505_;
}
}
else
{
size_t v___x_5533_; size_t v___x_5534_; lean_object* v___x_5535_; 
v___x_5533_ = ((size_t)0ULL);
v___x_5534_ = lean_usize_of_nat(v___x_5527_);
v___x_5535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5485_, v___x_5533_, v___x_5534_, v___y_5526_);
v___y_5506_ = v___y_5520_;
v___y_5507_ = v___y_5521_;
v___y_5508_ = v___y_5523_;
v___y_5509_ = v___y_5522_;
v___y_5510_ = v___y_5525_;
v___y_5511_ = v___y_5524_;
v___y_5512_ = v___x_5535_;
goto v___jp_5505_;
}
}
}
v___jp_5536_:
{
lean_object* v_packages_5541_; lean_object* v___x_5542_; lean_object* v_wsIdx_5543_; lean_object* v_dir_5544_; lean_object* v_depConfigs_5545_; lean_object* v___x_5546_; 
v_packages_5541_ = lean_ctor_get(v_ws_5481_, 4);
v___x_5542_ = lean_array_fget_borrowed(v_packages_5541_, v___y_5538_);
v_wsIdx_5543_ = lean_ctor_get(v___x_5542_, 0);
v_dir_5544_ = lean_ctor_get(v___x_5542_, 4);
v_depConfigs_5545_ = lean_ctor_get(v___x_5542_, 12);
v___x_5546_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5540_, v_depConfigs_5545_, v___y_5537_);
if (lean_obj_tag(v___x_5546_) == 0)
{
lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; 
lean_dec_ref_known(v___x_5546_, 1);
v___x_5547_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5544_);
v___x_5548_ = l_Lake_joinRelative(v_dir_5544_, v___x_5547_);
v___x_5549_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5550_ = l_Lake_joinRelative(v___x_5548_, v___x_5549_);
v___x_5551_ = l_Lake_Manifest_tryLoadEntries(v___x_5550_);
if (lean_obj_tag(v___x_5551_) == 0)
{
lean_object* v_a_5552_; lean_object* v___x_5553_; uint8_t v___x_5554_; 
v_a_5552_ = lean_ctor_get(v___x_5551_, 0);
lean_inc(v_a_5552_);
lean_dec_ref_known(v___x_5551_, 1);
v___x_5553_ = lean_array_get_size(v_a_5552_);
v___x_5554_ = lean_nat_dec_lt(v___y_5538_, v___x_5553_);
if (v___x_5554_ == 0)
{
lean_dec(v_a_5552_);
lean_inc_ref(v_packages_5541_);
lean_inc(v_wsIdx_5543_);
lean_inc_ref(v_depConfigs_5545_);
v___y_5520_ = v_depConfigs_5545_;
v___y_5521_ = v___y_5537_;
v___y_5522_ = v_wsIdx_5543_;
v___y_5523_ = v___y_5538_;
v___y_5524_ = v___y_5539_;
v___y_5525_ = v_packages_5541_;
v___y_5526_ = v___y_5540_;
goto v___jp_5519_;
}
else
{
uint8_t v___x_5555_; 
v___x_5555_ = lean_nat_dec_le(v___x_5553_, v___x_5553_);
if (v___x_5555_ == 0)
{
if (v___x_5554_ == 0)
{
lean_dec(v_a_5552_);
lean_inc_ref(v_packages_5541_);
lean_inc(v_wsIdx_5543_);
lean_inc_ref(v_depConfigs_5545_);
v___y_5520_ = v_depConfigs_5545_;
v___y_5521_ = v___y_5537_;
v___y_5522_ = v_wsIdx_5543_;
v___y_5523_ = v___y_5538_;
v___y_5524_ = v___y_5539_;
v___y_5525_ = v_packages_5541_;
v___y_5526_ = v___y_5540_;
goto v___jp_5519_;
}
else
{
size_t v___x_5556_; size_t v___x_5557_; lean_object* v___x_5558_; 
v___x_5556_ = ((size_t)0ULL);
v___x_5557_ = lean_usize_of_nat(v___x_5553_);
v___x_5558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5552_, v___x_5556_, v___x_5557_, v___y_5540_);
lean_dec(v_a_5552_);
lean_inc_ref(v_packages_5541_);
lean_inc(v_wsIdx_5543_);
lean_inc_ref(v_depConfigs_5545_);
v___y_5520_ = v_depConfigs_5545_;
v___y_5521_ = v___y_5537_;
v___y_5522_ = v_wsIdx_5543_;
v___y_5523_ = v___y_5538_;
v___y_5524_ = v___y_5539_;
v___y_5525_ = v_packages_5541_;
v___y_5526_ = v___x_5558_;
goto v___jp_5519_;
}
}
else
{
size_t v___x_5559_; size_t v___x_5560_; lean_object* v___x_5561_; 
v___x_5559_ = ((size_t)0ULL);
v___x_5560_ = lean_usize_of_nat(v___x_5553_);
v___x_5561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5552_, v___x_5559_, v___x_5560_, v___y_5540_);
lean_dec(v_a_5552_);
lean_inc_ref(v_packages_5541_);
lean_inc(v_wsIdx_5543_);
lean_inc_ref(v_depConfigs_5545_);
v___y_5520_ = v_depConfigs_5545_;
v___y_5521_ = v___y_5537_;
v___y_5522_ = v_wsIdx_5543_;
v___y_5523_ = v___y_5538_;
v___y_5524_ = v___y_5539_;
v___y_5525_ = v_packages_5541_;
v___y_5526_ = v___x_5561_;
goto v___jp_5519_;
}
}
}
else
{
lean_object* v_a_5562_; lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5574_; 
lean_dec(v___y_5540_);
lean_dec_ref(v___y_5539_);
lean_dec_ref(v_leanOpts_5483_);
lean_dec_ref(v_ws_5481_);
v_a_5562_ = lean_ctor_get(v___x_5551_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5551_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5564_ = v___x_5551_;
v_isShared_5565_ = v_isSharedCheck_5574_;
goto v_resetjp_5563_;
}
else
{
lean_inc(v_a_5562_);
lean_dec(v___x_5551_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5574_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5566_; uint8_t v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5572_; 
v___x_5566_ = lean_io_error_to_string(v_a_5562_);
v___x_5567_ = 3;
v___x_5568_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5568_, 0, v___x_5566_);
lean_ctor_set_uint8(v___x_5568_, sizeof(void*)*1, v___x_5567_);
lean_inc_ref(v___y_5537_);
v___x_5569_ = lean_apply_2(v___y_5537_, v___x_5568_, lean_box(0));
v___x_5570_ = lean_box(0);
if (v_isShared_5565_ == 0)
{
lean_ctor_set(v___x_5564_, 0, v___x_5570_);
v___x_5572_ = v___x_5564_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5570_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
else
{
lean_object* v_a_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5582_; 
lean_dec(v___y_5540_);
lean_dec_ref(v___y_5539_);
lean_dec_ref(v_leanOpts_5483_);
lean_dec_ref(v_ws_5481_);
v_a_5575_ = lean_ctor_get(v___x_5546_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5546_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5577_ = v___x_5546_;
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_a_5575_);
lean_dec(v___x_5546_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5580_; 
if (v_isShared_5578_ == 0)
{
v___x_5580_ = v___x_5577_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
}
v___jp_5585_:
{
lean_object* v_pkgEntries_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; uint8_t v___x_5591_; 
v_pkgEntries_5588_ = lean_box(1);
v___x_5589_ = lean_unsigned_to_nat(0u);
v___x_5590_ = lean_array_get_size(v_packages_5584_);
v___x_5591_ = lean_nat_dec_lt(v___x_5589_, v___x_5590_);
if (v___x_5591_ == 0)
{
lean_dec_ref(v_packages_5584_);
v___y_5537_ = v___y_5586_;
v___y_5538_ = v___x_5589_;
v___y_5539_ = v___y_5587_;
v___y_5540_ = v_pkgEntries_5588_;
goto v___jp_5536_;
}
else
{
uint8_t v___x_5592_; 
v___x_5592_ = lean_nat_dec_le(v___x_5590_, v___x_5590_);
if (v___x_5592_ == 0)
{
if (v___x_5591_ == 0)
{
lean_dec_ref(v_packages_5584_);
v___y_5537_ = v___y_5586_;
v___y_5538_ = v___x_5589_;
v___y_5539_ = v___y_5587_;
v___y_5540_ = v_pkgEntries_5588_;
goto v___jp_5536_;
}
else
{
size_t v___x_5593_; size_t v___x_5594_; lean_object* v___x_5595_; 
v___x_5593_ = ((size_t)0ULL);
v___x_5594_ = lean_usize_of_nat(v___x_5590_);
v___x_5595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5584_, v___x_5593_, v___x_5594_, v_pkgEntries_5588_);
lean_dec_ref(v_packages_5584_);
v___y_5537_ = v___y_5586_;
v___y_5538_ = v___x_5589_;
v___y_5539_ = v___y_5587_;
v___y_5540_ = v___x_5595_;
goto v___jp_5536_;
}
}
else
{
size_t v___x_5596_; size_t v___x_5597_; lean_object* v___x_5598_; 
v___x_5596_ = ((size_t)0ULL);
v___x_5597_ = lean_usize_of_nat(v___x_5590_);
v___x_5598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5584_, v___x_5596_, v___x_5597_, v_pkgEntries_5588_);
lean_dec_ref(v_packages_5584_);
v___y_5537_ = v___y_5586_;
v___y_5538_ = v___x_5589_;
v___y_5539_ = v___y_5587_;
v___y_5540_ = v___x_5598_;
goto v___jp_5536_;
}
}
}
v___jp_5599_:
{
if (lean_obj_tag(v_packagesDir_x3f_5583_) == 0)
{
lean_object* v_packages_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v_config_5604_; lean_object* v_toWorkspaceConfig_5605_; lean_object* v___x_5606_; 
v_packages_5601_ = lean_ctor_get(v_ws_5481_, 4);
v___x_5602_ = lean_unsigned_to_nat(0u);
v___x_5603_ = lean_array_fget_borrowed(v_packages_5601_, v___x_5602_);
v_config_5604_ = lean_ctor_get(v___x_5603_, 6);
v_toWorkspaceConfig_5605_ = lean_ctor_get(v_config_5604_, 0);
lean_inc_ref(v_toWorkspaceConfig_5605_);
v___x_5606_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5605_);
v___y_5586_ = v___y_5600_;
v___y_5587_ = v___x_5606_;
goto v___jp_5585_;
}
else
{
lean_object* v_val_5607_; 
v_val_5607_ = lean_ctor_get(v_packagesDir_x3f_5583_, 0);
lean_inc(v_val_5607_);
lean_dec_ref_known(v_packagesDir_x3f_5583_, 1);
v___y_5586_ = v___y_5600_;
v___y_5587_ = v_val_5607_;
goto v___jp_5585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5621_, lean_object* v_manifest_5622_, lean_object* v_leanOpts_5623_, lean_object* v_reconfigure_5624_, lean_object* v_overrides_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_){
_start:
{
uint8_t v_reconfigure_boxed_5628_; lean_object* v_res_5629_; 
v_reconfigure_boxed_5628_ = lean_unbox(v_reconfigure_5624_);
v_res_5629_ = l_Lake_Workspace_materializeDeps(v_ws_5621_, v_manifest_5622_, v_leanOpts_5623_, v_reconfigure_boxed_5628_, v_overrides_5625_, v_a_5626_);
lean_dec_ref(v_a_5626_);
lean_dec_ref(v_overrides_5625_);
return v_res_5629_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v_leanOpts_5632_, uint8_t v_reconfigure_5633_, lean_object* v_ws_5634_, lean_object* v_i_5635_, lean_object* v_i__lt_5636_, lean_object* v_next_5637_, lean_object* v_lt__next_5638_, lean_object* v___y_5639_){
_start:
{
lean_object* v___x_5641_; 
v___x_5641_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5630_, v___y_5631_, v_leanOpts_5632_, v_reconfigure_5633_, v_ws_5634_, v_i_5635_, v_next_5637_, v___y_5639_);
return v___x_5641_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v_leanOpts_5644_, lean_object* v_reconfigure_5645_, lean_object* v_ws_5646_, lean_object* v_i_5647_, lean_object* v_i__lt_5648_, lean_object* v_next_5649_, lean_object* v_lt__next_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_){
_start:
{
uint8_t v_reconfigure_boxed_5653_; lean_object* v_res_5654_; 
v_reconfigure_boxed_5653_ = lean_unbox(v_reconfigure_5645_);
v_res_5654_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5642_, v___y_5643_, v_leanOpts_5644_, v_reconfigure_boxed_5653_, v_ws_5646_, v_i_5647_, v_i__lt_5648_, v_next_5649_, v_lt__next_5650_, v___y_5651_);
lean_dec_ref(v___y_5651_);
lean_dec(v___y_5642_);
return v_res_5654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(lean_object* v_start_5655_, lean_object* v_pkg_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v_leanOpts_5659_, uint8_t v_reconfigure_5660_, lean_object* v_as_5661_, size_t v_i_5662_, size_t v_stop_5663_, lean_object* v_b_5664_, lean_object* v___y_5665_){
_start:
{
lean_object* v___x_5667_; 
v___x_5667_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5656_, v___y_5657_, v___y_5658_, v_leanOpts_5659_, v_reconfigure_5660_, v_as_5661_, v_i_5662_, v_stop_5663_, v_b_5664_, v___y_5665_);
return v___x_5667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_start_5668_, lean_object* v_pkg_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v_leanOpts_5672_, lean_object* v_reconfigure_5673_, lean_object* v_as_5674_, lean_object* v_i_5675_, lean_object* v_stop_5676_, lean_object* v_b_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_){
_start:
{
uint8_t v_reconfigure_boxed_5680_; size_t v_i_boxed_5681_; size_t v_stop_boxed_5682_; lean_object* v_res_5683_; 
v_reconfigure_boxed_5680_ = lean_unbox(v_reconfigure_5673_);
v_i_boxed_5681_ = lean_unbox_usize(v_i_5675_);
lean_dec(v_i_5675_);
v_stop_boxed_5682_ = lean_unbox_usize(v_stop_5676_);
lean_dec(v_stop_5676_);
v_res_5683_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(v_start_5668_, v_pkg_5669_, v___y_5670_, v___y_5671_, v_leanOpts_5672_, v_reconfigure_boxed_5680_, v_as_5674_, v_i_boxed_5681_, v_stop_boxed_5682_, v_b_5677_, v___y_5678_);
lean_dec_ref(v___y_5678_);
lean_dec_ref(v_as_5674_);
lean_dec(v___y_5670_);
lean_dec(v_start_5668_);
return v_res_5683_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_StoreInsts(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Materialize(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Package(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Runtime(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Resolve(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_StoreInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Materialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Load_Resolve_0__Lake_restartCode = _init_l___private_Lake_Load_Resolve_0__Lake_restartCode();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Resolve(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Lake_Util_StoreInsts(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Load_Materialize(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* initialize_Lake_Load_Package(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Lean_Runtime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Resolve(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_StoreInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Materialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Resolve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Resolve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Resolve(builtin);
}
#ifdef __cplusplus
}
#endif

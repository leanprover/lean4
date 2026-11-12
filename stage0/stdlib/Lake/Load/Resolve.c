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
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_resolveConfigFile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadConfigFile___redArg(lean_object*, lean_object*);
lean_object* l_Lake_mkPackage(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
uint8_t l_Lake_ToolchainVer_ble(lean_object*, lean_object*);
uint8_t l_Lake_ToolchainVer_blt(lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4_spec__6___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": updating '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' with "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "source kind (git/path)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "git revision"};
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
size_t v___x_77_; size_t v___x_78_; lean_object* v___x_79_; 
v___x_77_ = ((size_t)0ULL);
v___x_78_ = lean_usize_of_nat(v___x_75_);
v___x_79_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_decls_72_, v___x_77_, v___x_78_, v_self_73_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls___boxed(lean_object* v_decls_80_, lean_object* v_self_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(v_decls_80_, v_self_81_);
lean_dec_ref(v_decls_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(lean_object* v_k_83_, lean_object* v_v_84_, lean_object* v_t_85_){
_start:
{
if (lean_obj_tag(v_t_85_) == 0)
{
lean_object* v_size_86_; lean_object* v_k_87_; lean_object* v_v_88_; lean_object* v_l_89_; lean_object* v_r_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_370_; 
v_size_86_ = lean_ctor_get(v_t_85_, 0);
v_k_87_ = lean_ctor_get(v_t_85_, 1);
v_v_88_ = lean_ctor_get(v_t_85_, 2);
v_l_89_ = lean_ctor_get(v_t_85_, 3);
v_r_90_ = lean_ctor_get(v_t_85_, 4);
v_isSharedCheck_370_ = !lean_is_exclusive(v_t_85_);
if (v_isSharedCheck_370_ == 0)
{
v___x_92_ = v_t_85_;
v_isShared_93_ = v_isSharedCheck_370_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_r_90_);
lean_inc(v_l_89_);
lean_inc(v_v_88_);
lean_inc(v_k_87_);
lean_inc(v_size_86_);
lean_dec(v_t_85_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_370_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
uint8_t v___x_94_; 
v___x_94_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_83_, v_k_87_);
switch(v___x_94_)
{
case 0:
{
lean_object* v_impl_95_; lean_object* v___x_96_; 
lean_dec(v_size_86_);
v_impl_95_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_83_, v_v_84_, v_l_89_);
v___x_96_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_90_) == 0)
{
lean_object* v_size_97_; lean_object* v_size_98_; lean_object* v_k_99_; lean_object* v_v_100_; lean_object* v_l_101_; lean_object* v_r_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_size_97_ = lean_ctor_get(v_r_90_, 0);
v_size_98_ = lean_ctor_get(v_impl_95_, 0);
v_k_99_ = lean_ctor_get(v_impl_95_, 1);
v_v_100_ = lean_ctor_get(v_impl_95_, 2);
v_l_101_ = lean_ctor_get(v_impl_95_, 3);
v_r_102_ = lean_ctor_get(v_impl_95_, 4);
lean_inc(v_r_102_);
v___x_103_ = lean_unsigned_to_nat(3u);
v___x_104_ = lean_nat_mul(v___x_103_, v_size_97_);
v___x_105_ = lean_nat_dec_lt(v___x_104_, v_size_98_);
lean_dec(v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
lean_dec(v_r_102_);
v___x_106_ = lean_nat_add(v___x_96_, v_size_98_);
v___x_107_ = lean_nat_add(v___x_106_, v_size_97_);
lean_dec(v___x_106_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 3, v_impl_95_);
lean_ctor_set(v___x_92_, 0, v___x_107_);
v___x_109_ = v___x_92_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_110_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_110_, 3, v_impl_95_);
lean_ctor_set(v_reuseFailAlloc_110_, 4, v_r_90_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
else
{
lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_176_; 
lean_inc(v_l_101_);
lean_inc(v_v_100_);
lean_inc(v_k_99_);
lean_inc(v_size_98_);
v_isSharedCheck_176_ = !lean_is_exclusive(v_impl_95_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; lean_object* v_unused_178_; lean_object* v_unused_179_; lean_object* v_unused_180_; lean_object* v_unused_181_; 
v_unused_177_ = lean_ctor_get(v_impl_95_, 4);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_impl_95_, 3);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_impl_95_, 2);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_impl_95_, 1);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_impl_95_, 0);
lean_dec(v_unused_181_);
v___x_112_ = v_impl_95_;
v_isShared_113_ = v_isSharedCheck_176_;
goto v_resetjp_111_;
}
else
{
lean_dec(v_impl_95_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_176_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_size_114_; lean_object* v_size_115_; lean_object* v_k_116_; lean_object* v_v_117_; lean_object* v_l_118_; lean_object* v_r_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_size_114_ = lean_ctor_get(v_l_101_, 0);
v_size_115_ = lean_ctor_get(v_r_102_, 0);
v_k_116_ = lean_ctor_get(v_r_102_, 1);
v_v_117_ = lean_ctor_get(v_r_102_, 2);
v_l_118_ = lean_ctor_get(v_r_102_, 3);
v_r_119_ = lean_ctor_get(v_r_102_, 4);
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = lean_nat_mul(v___x_120_, v_size_114_);
v___x_122_ = lean_nat_dec_lt(v_size_115_, v___x_121_);
lean_dec(v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_151_; 
lean_inc(v_r_119_);
lean_inc(v_l_118_);
lean_inc(v_v_117_);
lean_inc(v_k_116_);
v_isSharedCheck_151_ = !lean_is_exclusive(v_r_102_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; lean_object* v_unused_153_; lean_object* v_unused_154_; lean_object* v_unused_155_; lean_object* v_unused_156_; 
v_unused_152_ = lean_ctor_get(v_r_102_, 4);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_r_102_, 3);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v_r_102_, 2);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_r_102_, 1);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v_r_102_, 0);
lean_dec(v_unused_156_);
v___x_124_ = v_r_102_;
v_isShared_125_ = v_isSharedCheck_151_;
goto v_resetjp_123_;
}
else
{
lean_dec(v_r_102_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_151_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v___x_139_; lean_object* v___y_141_; 
v___x_126_ = lean_nat_add(v___x_96_, v_size_98_);
lean_dec(v_size_98_);
v___x_127_ = lean_nat_add(v___x_126_, v_size_97_);
lean_dec(v___x_126_);
v___x_139_ = lean_nat_add(v___x_96_, v_size_114_);
if (lean_obj_tag(v_l_118_) == 0)
{
lean_object* v_size_149_; 
v_size_149_ = lean_ctor_get(v_l_118_, 0);
lean_inc(v_size_149_);
v___y_141_ = v_size_149_;
goto v___jp_140_;
}
else
{
lean_object* v___x_150_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___y_141_ = v___x_150_;
goto v___jp_140_;
}
v___jp_128_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_nat_add(v___y_129_, v___y_131_);
lean_dec(v___y_131_);
lean_dec(v___y_129_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 4, v_r_90_);
lean_ctor_set(v___x_124_, 3, v_r_119_);
lean_ctor_set(v___x_124_, 2, v_v_88_);
lean_ctor_set(v___x_124_, 1, v_k_87_);
lean_ctor_set(v___x_124_, 0, v___x_132_);
v___x_134_ = v___x_124_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_138_, 3, v_r_119_);
lean_ctor_set(v_reuseFailAlloc_138_, 4, v_r_90_);
v___x_134_ = v_reuseFailAlloc_138_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v___x_134_);
lean_ctor_set(v___x_112_, 3, v___y_130_);
lean_ctor_set(v___x_112_, 2, v_v_117_);
lean_ctor_set(v___x_112_, 1, v_k_116_);
lean_ctor_set(v___x_112_, 0, v___x_127_);
v___x_136_ = v___x_112_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_k_116_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_v_117_);
lean_ctor_set(v_reuseFailAlloc_137_, 3, v___y_130_);
lean_ctor_set(v_reuseFailAlloc_137_, 4, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_nat_add(v___x_139_, v___y_141_);
lean_dec(v___y_141_);
lean_dec(v___x_139_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_l_118_);
lean_ctor_set(v___x_92_, 3, v_l_101_);
lean_ctor_set(v___x_92_, 2, v_v_100_);
lean_ctor_set(v___x_92_, 1, v_k_99_);
lean_ctor_set(v___x_92_, 0, v___x_142_);
v___x_144_ = v___x_92_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_k_99_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_v_100_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v_l_101_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v_l_118_);
v___x_144_ = v_reuseFailAlloc_148_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; 
v___x_145_ = lean_nat_add(v___x_96_, v_size_97_);
if (lean_obj_tag(v_r_119_) == 0)
{
lean_object* v_size_146_; 
v_size_146_ = lean_ctor_get(v_r_119_, 0);
lean_inc(v_size_146_);
v___y_129_ = v___x_145_;
v___y_130_ = v___x_144_;
v___y_131_ = v_size_146_;
goto v___jp_128_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___y_129_ = v___x_145_;
v___y_130_ = v___x_144_;
v___y_131_ = v___x_147_;
goto v___jp_128_;
}
}
}
}
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
lean_del_object(v___x_92_);
v___x_157_ = lean_nat_add(v___x_96_, v_size_98_);
lean_dec(v_size_98_);
v___x_158_ = lean_nat_add(v___x_157_, v_size_97_);
lean_dec(v___x_157_);
v___x_159_ = lean_nat_add(v___x_96_, v_size_97_);
v___x_160_ = lean_nat_add(v___x_159_, v_size_115_);
lean_dec(v___x_159_);
lean_inc_ref(v_r_90_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v_r_90_);
lean_ctor_set(v___x_112_, 3, v_r_102_);
lean_ctor_set(v___x_112_, 2, v_v_88_);
lean_ctor_set(v___x_112_, 1, v_k_87_);
lean_ctor_set(v___x_112_, 0, v___x_160_);
v___x_162_ = v___x_112_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_r_102_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v_r_90_);
v___x_162_ = v_reuseFailAlloc_175_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_isSharedCheck_169_ = !lean_is_exclusive(v_r_90_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; lean_object* v_unused_171_; lean_object* v_unused_172_; lean_object* v_unused_173_; lean_object* v_unused_174_; 
v_unused_170_ = lean_ctor_get(v_r_90_, 4);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_r_90_, 3);
lean_dec(v_unused_171_);
v_unused_172_ = lean_ctor_get(v_r_90_, 2);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_r_90_, 1);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_r_90_, 0);
lean_dec(v_unused_174_);
v___x_164_ = v_r_90_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_dec(v_r_90_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 4, v___x_162_);
lean_ctor_set(v___x_164_, 3, v_l_101_);
lean_ctor_set(v___x_164_, 2, v_v_100_);
lean_ctor_set(v___x_164_, 1, v_k_99_);
lean_ctor_set(v___x_164_, 0, v___x_158_);
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_k_99_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_v_100_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_l_101_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v___x_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_182_; 
v_l_182_ = lean_ctor_get(v_impl_95_, 3);
if (lean_obj_tag(v_l_182_) == 0)
{
lean_object* v_r_183_; lean_object* v_k_184_; lean_object* v_v_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_196_; 
lean_inc_ref(v_l_182_);
v_r_183_ = lean_ctor_get(v_impl_95_, 4);
v_k_184_ = lean_ctor_get(v_impl_95_, 1);
v_v_185_ = lean_ctor_get(v_impl_95_, 2);
v_isSharedCheck_196_ = !lean_is_exclusive(v_impl_95_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; lean_object* v_unused_198_; 
v_unused_197_ = lean_ctor_get(v_impl_95_, 3);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_impl_95_, 0);
lean_dec(v_unused_198_);
v___x_187_ = v_impl_95_;
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_r_183_);
lean_inc(v_v_185_);
lean_inc(v_k_184_);
lean_dec(v_impl_95_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_183_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 3, v_r_183_);
lean_ctor_set(v___x_187_, 2, v_v_88_);
lean_ctor_set(v___x_187_, 1, v_k_87_);
lean_ctor_set(v___x_187_, 0, v___x_96_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v_r_183_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v_r_183_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_191_);
lean_ctor_set(v___x_92_, 3, v_l_182_);
lean_ctor_set(v___x_92_, 2, v_v_185_);
lean_ctor_set(v___x_92_, 1, v_k_184_);
lean_ctor_set(v___x_92_, 0, v___x_189_);
v___x_193_ = v___x_92_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_k_184_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_v_185_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_l_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_r_199_; 
v_r_199_ = lean_ctor_get(v_impl_95_, 4);
lean_inc(v_r_199_);
if (lean_obj_tag(v_r_199_) == 0)
{
lean_object* v_k_200_; lean_object* v_v_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_224_; 
lean_inc(v_l_182_);
v_k_200_ = lean_ctor_get(v_impl_95_, 1);
v_v_201_ = lean_ctor_get(v_impl_95_, 2);
v_isSharedCheck_224_ = !lean_is_exclusive(v_impl_95_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; lean_object* v_unused_226_; lean_object* v_unused_227_; 
v_unused_225_ = lean_ctor_get(v_impl_95_, 4);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_impl_95_, 3);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_impl_95_, 0);
lean_dec(v_unused_227_);
v___x_203_ = v_impl_95_;
v_isShared_204_ = v_isSharedCheck_224_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_v_201_);
lean_inc(v_k_200_);
lean_dec(v_impl_95_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_224_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_k_205_; lean_object* v_v_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_220_; 
v_k_205_ = lean_ctor_get(v_r_199_, 1);
v_v_206_ = lean_ctor_get(v_r_199_, 2);
v_isSharedCheck_220_ = !lean_is_exclusive(v_r_199_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; lean_object* v_unused_222_; lean_object* v_unused_223_; 
v_unused_221_ = lean_ctor_get(v_r_199_, 4);
lean_dec(v_unused_221_);
v_unused_222_ = lean_ctor_get(v_r_199_, 3);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_r_199_, 0);
lean_dec(v_unused_223_);
v___x_208_ = v_r_199_;
v_isShared_209_ = v_isSharedCheck_220_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_v_206_);
lean_inc(v_k_205_);
lean_dec(v_r_199_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_220_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_unsigned_to_nat(3u);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 4, v_l_182_);
lean_ctor_set(v___x_208_, 3, v_l_182_);
lean_ctor_set(v___x_208_, 2, v_v_201_);
lean_ctor_set(v___x_208_, 1, v_k_200_);
lean_ctor_set(v___x_208_, 0, v___x_96_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_k_200_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_v_201_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_l_182_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_l_182_);
v___x_212_ = v_reuseFailAlloc_219_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 4, v_l_182_);
lean_ctor_set(v___x_203_, 2, v_v_88_);
lean_ctor_set(v___x_203_, 1, v_k_87_);
lean_ctor_set(v___x_203_, 0, v___x_96_);
v___x_214_ = v___x_203_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v_l_182_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v_l_182_);
v___x_214_ = v_reuseFailAlloc_218_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_216_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_214_);
lean_ctor_set(v___x_92_, 3, v___x_212_);
lean_ctor_set(v___x_92_, 2, v_v_206_);
lean_ctor_set(v___x_92_, 1, v_k_205_);
lean_ctor_set(v___x_92_, 0, v___x_210_);
v___x_216_ = v___x_92_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_k_205_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_v_206_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
}
else
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_unsigned_to_nat(2u);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_r_199_);
lean_ctor_set(v___x_92_, 3, v_impl_95_);
lean_ctor_set(v___x_92_, 0, v___x_228_);
v___x_230_ = v___x_92_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_impl_95_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_r_199_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
case 1:
{
lean_object* v___x_233_; 
lean_dec(v_v_88_);
lean_dec(v_k_87_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 2, v_v_84_);
lean_ctor_set(v___x_92_, 1, v_k_83_);
v___x_233_ = v___x_92_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_size_86_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_l_89_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v_r_90_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
default: 
{
lean_object* v_impl_235_; lean_object* v___x_236_; 
lean_dec(v_size_86_);
v_impl_235_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_83_, v_v_84_, v_r_90_);
v___x_236_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_89_) == 0)
{
lean_object* v_size_237_; lean_object* v_size_238_; lean_object* v_k_239_; lean_object* v_v_240_; lean_object* v_l_241_; lean_object* v_r_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_size_237_ = lean_ctor_get(v_l_89_, 0);
v_size_238_ = lean_ctor_get(v_impl_235_, 0);
v_k_239_ = lean_ctor_get(v_impl_235_, 1);
v_v_240_ = lean_ctor_get(v_impl_235_, 2);
v_l_241_ = lean_ctor_get(v_impl_235_, 3);
lean_inc(v_l_241_);
v_r_242_ = lean_ctor_get(v_impl_235_, 4);
v___x_243_ = lean_unsigned_to_nat(3u);
v___x_244_ = lean_nat_mul(v___x_243_, v_size_237_);
v___x_245_ = lean_nat_dec_lt(v___x_244_, v_size_238_);
lean_dec(v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
lean_dec(v_l_241_);
v___x_246_ = lean_nat_add(v___x_236_, v_size_237_);
v___x_247_ = lean_nat_add(v___x_246_, v_size_238_);
lean_dec(v___x_246_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_impl_235_);
lean_ctor_set(v___x_92_, 0, v___x_247_);
v___x_249_ = v___x_92_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_l_89_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v_impl_235_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
else
{
lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_314_; 
lean_inc(v_r_242_);
lean_inc(v_v_240_);
lean_inc(v_k_239_);
lean_inc(v_size_238_);
v_isSharedCheck_314_ = !lean_is_exclusive(v_impl_235_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; 
v_unused_315_ = lean_ctor_get(v_impl_235_, 4);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_impl_235_, 3);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_impl_235_, 2);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_impl_235_, 1);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_impl_235_, 0);
lean_dec(v_unused_319_);
v___x_252_ = v_impl_235_;
v_isShared_253_ = v_isSharedCheck_314_;
goto v_resetjp_251_;
}
else
{
lean_dec(v_impl_235_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_314_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_size_254_; lean_object* v_k_255_; lean_object* v_v_256_; lean_object* v_l_257_; lean_object* v_r_258_; lean_object* v_size_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_size_254_ = lean_ctor_get(v_l_241_, 0);
v_k_255_ = lean_ctor_get(v_l_241_, 1);
v_v_256_ = lean_ctor_get(v_l_241_, 2);
v_l_257_ = lean_ctor_get(v_l_241_, 3);
v_r_258_ = lean_ctor_get(v_l_241_, 4);
v_size_259_ = lean_ctor_get(v_r_242_, 0);
v___x_260_ = lean_unsigned_to_nat(2u);
v___x_261_ = lean_nat_mul(v___x_260_, v_size_259_);
v___x_262_ = lean_nat_dec_lt(v_size_254_, v___x_261_);
lean_dec(v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_290_; 
lean_inc(v_r_258_);
lean_inc(v_l_257_);
lean_inc(v_v_256_);
lean_inc(v_k_255_);
v_isSharedCheck_290_ = !lean_is_exclusive(v_l_241_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; lean_object* v_unused_294_; lean_object* v_unused_295_; 
v_unused_291_ = lean_ctor_get(v_l_241_, 4);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_l_241_, 3);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_l_241_, 2);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v_l_241_, 1);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_l_241_, 0);
lean_dec(v_unused_295_);
v___x_264_ = v_l_241_;
v_isShared_265_ = v_isSharedCheck_290_;
goto v_resetjp_263_;
}
else
{
lean_dec(v_l_241_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_290_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_280_; 
v___x_266_ = lean_nat_add(v___x_236_, v_size_237_);
v___x_267_ = lean_nat_add(v___x_266_, v_size_238_);
lean_dec(v_size_238_);
if (lean_obj_tag(v_l_257_) == 0)
{
lean_object* v_size_288_; 
v_size_288_ = lean_ctor_get(v_l_257_, 0);
lean_inc(v_size_288_);
v___y_280_ = v_size_288_;
goto v___jp_279_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___y_280_ = v___x_289_;
goto v___jp_279_;
}
v___jp_268_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = lean_nat_add(v___y_269_, v___y_271_);
lean_dec(v___y_271_);
lean_dec(v___y_269_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 4, v_r_242_);
lean_ctor_set(v___x_264_, 3, v_r_258_);
lean_ctor_set(v___x_264_, 2, v_v_240_);
lean_ctor_set(v___x_264_, 1, v_k_239_);
lean_ctor_set(v___x_264_, 0, v___x_272_);
v___x_274_ = v___x_264_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_k_239_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_v_240_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_r_258_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_r_242_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 4, v___x_274_);
lean_ctor_set(v___x_252_, 3, v___y_270_);
lean_ctor_set(v___x_252_, 2, v_v_256_);
lean_ctor_set(v___x_252_, 1, v_k_255_);
lean_ctor_set(v___x_252_, 0, v___x_267_);
v___x_276_ = v___x_252_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_k_255_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_v_256_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v___y_270_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_nat_add(v___x_266_, v___y_280_);
lean_dec(v___y_280_);
lean_dec(v___x_266_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_l_257_);
lean_ctor_set(v___x_92_, 0, v___x_281_);
v___x_283_ = v___x_92_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_l_89_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_l_257_);
v___x_283_ = v_reuseFailAlloc_287_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; 
v___x_284_ = lean_nat_add(v___x_236_, v_size_259_);
if (lean_obj_tag(v_r_258_) == 0)
{
lean_object* v_size_285_; 
v_size_285_ = lean_ctor_get(v_r_258_, 0);
lean_inc(v_size_285_);
v___y_269_ = v___x_284_;
v___y_270_ = v___x_283_;
v___y_271_ = v_size_285_;
goto v___jp_268_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___y_269_ = v___x_284_;
v___y_270_ = v___x_283_;
v___y_271_ = v___x_286_;
goto v___jp_268_;
}
}
}
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
lean_del_object(v___x_92_);
v___x_296_ = lean_nat_add(v___x_236_, v_size_237_);
v___x_297_ = lean_nat_add(v___x_296_, v_size_238_);
lean_dec(v_size_238_);
v___x_298_ = lean_nat_add(v___x_296_, v_size_254_);
lean_dec(v___x_296_);
lean_inc_ref(v_l_89_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 4, v_l_241_);
lean_ctor_set(v___x_252_, 3, v_l_89_);
lean_ctor_set(v___x_252_, 2, v_v_88_);
lean_ctor_set(v___x_252_, 1, v_k_87_);
lean_ctor_set(v___x_252_, 0, v___x_298_);
v___x_300_ = v___x_252_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_l_89_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_l_241_);
v___x_300_ = v_reuseFailAlloc_313_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_isSharedCheck_307_ = !lean_is_exclusive(v_l_89_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; lean_object* v_unused_309_; lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; 
v_unused_308_ = lean_ctor_get(v_l_89_, 4);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_l_89_, 3);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_l_89_, 2);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_l_89_, 1);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_l_89_, 0);
lean_dec(v_unused_312_);
v___x_302_ = v_l_89_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_l_89_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_r_242_);
lean_ctor_set(v___x_302_, 3, v___x_300_);
lean_ctor_set(v___x_302_, 2, v_v_240_);
lean_ctor_set(v___x_302_, 1, v_k_239_);
lean_ctor_set(v___x_302_, 0, v___x_297_);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_k_239_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_v_240_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_r_242_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_320_; 
v_l_320_ = lean_ctor_get(v_impl_235_, 3);
lean_inc(v_l_320_);
if (lean_obj_tag(v_l_320_) == 0)
{
lean_object* v_r_321_; lean_object* v_k_322_; lean_object* v_v_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_346_; 
v_r_321_ = lean_ctor_get(v_impl_235_, 4);
v_k_322_ = lean_ctor_get(v_impl_235_, 1);
v_v_323_ = lean_ctor_get(v_impl_235_, 2);
v_isSharedCheck_346_ = !lean_is_exclusive(v_impl_235_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; lean_object* v_unused_348_; 
v_unused_347_ = lean_ctor_get(v_impl_235_, 3);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_impl_235_, 0);
lean_dec(v_unused_348_);
v___x_325_ = v_impl_235_;
v_isShared_326_ = v_isSharedCheck_346_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_r_321_);
lean_inc(v_v_323_);
lean_inc(v_k_322_);
lean_dec(v_impl_235_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_346_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_k_327_; lean_object* v_v_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_342_; 
v_k_327_ = lean_ctor_get(v_l_320_, 1);
v_v_328_ = lean_ctor_get(v_l_320_, 2);
v_isSharedCheck_342_ = !lean_is_exclusive(v_l_320_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; lean_object* v_unused_344_; lean_object* v_unused_345_; 
v_unused_343_ = lean_ctor_get(v_l_320_, 4);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v_l_320_, 3);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_l_320_, 0);
lean_dec(v_unused_345_);
v___x_330_ = v_l_320_;
v_isShared_331_ = v_isSharedCheck_342_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_v_328_);
lean_inc(v_k_327_);
lean_dec(v_l_320_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_342_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_321_, 2);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 4, v_r_321_);
lean_ctor_set(v___x_330_, 3, v_r_321_);
lean_ctor_set(v___x_330_, 2, v_v_88_);
lean_ctor_set(v___x_330_, 1, v_k_87_);
lean_ctor_set(v___x_330_, 0, v___x_236_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_r_321_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_r_321_);
v___x_334_ = v_reuseFailAlloc_341_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
lean_inc(v_r_321_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 3, v_r_321_);
lean_ctor_set(v___x_325_, 0, v___x_236_);
v___x_336_ = v___x_325_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_k_322_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_v_323_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v_r_321_);
lean_ctor_set(v_reuseFailAlloc_340_, 4, v_r_321_);
v___x_336_ = v_reuseFailAlloc_340_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_336_);
lean_ctor_set(v___x_92_, 3, v___x_334_);
lean_ctor_set(v___x_92_, 2, v_v_328_);
lean_ctor_set(v___x_92_, 1, v_k_327_);
lean_ctor_set(v___x_92_, 0, v___x_332_);
v___x_338_ = v___x_92_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_k_327_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_v_328_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_339_, 4, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
else
{
lean_object* v_r_349_; 
v_r_349_ = lean_ctor_get(v_impl_235_, 4);
lean_inc(v_r_349_);
if (lean_obj_tag(v_r_349_) == 0)
{
lean_object* v_k_350_; lean_object* v_v_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_362_; 
v_k_350_ = lean_ctor_get(v_impl_235_, 1);
v_v_351_ = lean_ctor_get(v_impl_235_, 2);
v_isSharedCheck_362_ = !lean_is_exclusive(v_impl_235_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; lean_object* v_unused_364_; lean_object* v_unused_365_; 
v_unused_363_ = lean_ctor_get(v_impl_235_, 4);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_impl_235_, 3);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_impl_235_, 0);
lean_dec(v_unused_365_);
v___x_353_ = v_impl_235_;
v_isShared_354_ = v_isSharedCheck_362_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_v_351_);
lean_inc(v_k_350_);
lean_dec(v_impl_235_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_362_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = lean_unsigned_to_nat(3u);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 4, v_l_320_);
lean_ctor_set(v___x_353_, 2, v_v_88_);
lean_ctor_set(v___x_353_, 1, v_k_87_);
lean_ctor_set(v___x_353_, 0, v___x_236_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_l_320_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v_l_320_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_r_349_);
lean_ctor_set(v___x_92_, 3, v___x_357_);
lean_ctor_set(v___x_92_, 2, v_v_351_);
lean_ctor_set(v___x_92_, 1, v_k_350_);
lean_ctor_set(v___x_92_, 0, v___x_355_);
v___x_359_ = v___x_92_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_k_350_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_v_351_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v_r_349_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(2u);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_impl_235_);
lean_ctor_set(v___x_92_, 3, v_r_349_);
lean_ctor_set(v___x_92_, 0, v___x_366_);
v___x_368_ = v___x_92_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_r_349_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_impl_235_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
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
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_k_83_);
lean_ctor_set(v___x_372_, 2, v_v_84_);
lean_ctor_set(v___x_372_, 3, v_t_85_);
lean_ctor_set(v___x_372_, 4, v_t_85_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(lean_object* v_ws_373_, lean_object* v_dep_374_, lean_object* v_lakeOpts_375_, lean_object* v_leanOpts_376_, uint8_t v_reconfigure_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_lakeEnv_380_; lean_object* v_lakeConfig_381_; lean_object* v_lakeCache_382_; lean_object* v_lakeArgs_x3f_383_; lean_object* v_packages_384_; lean_object* v_packageMap_385_; lean_object* v_facetConfigs_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_453_; 
v_lakeEnv_380_ = lean_ctor_get(v_ws_373_, 0);
v_lakeConfig_381_ = lean_ctor_get(v_ws_373_, 1);
v_lakeCache_382_ = lean_ctor_get(v_ws_373_, 2);
v_lakeArgs_x3f_383_ = lean_ctor_get(v_ws_373_, 3);
v_packages_384_ = lean_ctor_get(v_ws_373_, 4);
v_packageMap_385_ = lean_ctor_get(v_ws_373_, 5);
v_facetConfigs_386_ = lean_ctor_get(v_ws_373_, 6);
v_isSharedCheck_453_ = !lean_is_exclusive(v_ws_373_);
if (v_isSharedCheck_453_ == 0)
{
v___x_388_ = v_ws_373_;
v_isShared_389_ = v_isSharedCheck_453_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_facetConfigs_386_);
lean_inc(v_packageMap_385_);
lean_inc(v_packages_384_);
lean_inc(v_lakeArgs_x3f_383_);
lean_inc(v_lakeCache_382_);
lean_inc(v_lakeConfig_381_);
lean_inc(v_lakeEnv_380_);
lean_dec(v_ws_373_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_453_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_manifestEntry_392_; lean_object* v_dir_393_; lean_object* v_pkgDir_394_; lean_object* v_relPkgDir_395_; lean_object* v_remoteUrl_396_; lean_object* v_name_397_; lean_object* v_scope_398_; lean_object* v_configFile_399_; lean_object* v_manifestFile_x3f_400_; lean_object* v_wsIdx_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___y_405_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_array_fget_borrowed(v_packages_384_, v___x_390_);
v_manifestEntry_392_ = lean_ctor_get(v_dep_374_, 4);
lean_inc_ref(v_manifestEntry_392_);
v_dir_393_ = lean_ctor_get(v___x_391_, 4);
v_pkgDir_394_ = lean_ctor_get(v_dep_374_, 0);
lean_inc_ref_n(v_pkgDir_394_, 2);
v_relPkgDir_395_ = lean_ctor_get(v_dep_374_, 1);
lean_inc_ref(v_relPkgDir_395_);
v_remoteUrl_396_ = lean_ctor_get(v_dep_374_, 2);
lean_inc_ref(v_remoteUrl_396_);
lean_dec_ref(v_dep_374_);
v_name_397_ = lean_ctor_get(v_manifestEntry_392_, 0);
lean_inc(v_name_397_);
v_scope_398_ = lean_ctor_get(v_manifestEntry_392_, 1);
lean_inc_ref(v_scope_398_);
v_configFile_399_ = lean_ctor_get(v_manifestEntry_392_, 2);
lean_inc_ref_n(v_configFile_399_, 2);
v_manifestFile_x3f_400_ = lean_ctor_get(v_manifestEntry_392_, 3);
lean_inc(v_manifestFile_x3f_400_);
lean_dec_ref(v_manifestEntry_392_);
v_wsIdx_401_ = lean_array_get_size(v_packages_384_);
v___x_402_ = lean_box(0);
v___x_403_ = l_Lake_joinRelative(v_pkgDir_394_, v_configFile_399_);
if (lean_obj_tag(v_manifestFile_x3f_400_) == 0)
{
lean_object* v___x_451_; 
v___x_451_ = l_Lake_defaultManifestFile;
v___y_405_ = v___x_451_;
goto v___jp_404_;
}
else
{
lean_object* v_val_452_; 
v_val_452_ = lean_ctor_get(v_manifestFile_x3f_400_, 0);
lean_inc(v_val_452_);
lean_dec_ref_known(v_manifestFile_x3f_400_, 1);
v___y_405_ = v_val_452_;
goto v___jp_404_;
}
v___jp_404_:
{
lean_object* v___x_406_; uint8_t v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_406_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_407_ = 0;
v___x_408_ = 1;
lean_inc(v_name_397_);
lean_inc_ref(v_dir_393_);
lean_inc_ref(v_lakeEnv_380_);
v___x_409_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_409_, 0, v_lakeEnv_380_);
lean_ctor_set(v___x_409_, 1, v___x_402_);
lean_ctor_set(v___x_409_, 2, v_dir_393_);
lean_ctor_set(v___x_409_, 3, v_wsIdx_401_);
lean_ctor_set(v___x_409_, 4, v_name_397_);
lean_ctor_set(v___x_409_, 5, v_relPkgDir_395_);
lean_ctor_set(v___x_409_, 6, v_pkgDir_394_);
lean_ctor_set(v___x_409_, 7, v_configFile_399_);
lean_ctor_set(v___x_409_, 8, v___x_403_);
lean_ctor_set(v___x_409_, 9, v___x_402_);
lean_ctor_set(v___x_409_, 10, v___y_405_);
lean_ctor_set(v___x_409_, 11, v___x_406_);
lean_ctor_set(v___x_409_, 12, v_lakeOpts_375_);
lean_ctor_set(v___x_409_, 13, v_leanOpts_376_);
lean_ctor_set(v___x_409_, 14, v_scope_398_);
lean_ctor_set(v___x_409_, 15, v_remoteUrl_396_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*16, v_reconfigure_377_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*16 + 1, v___x_407_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*16 + 2, v___x_408_);
v___x_410_ = l_Lean_Name_toString(v_name_397_, v___x_407_);
v___x_411_ = l_Lake_resolveConfigFile(v___x_410_, v___x_409_, v_a_378_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v_a_413_; lean_object* v___x_414_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_n(v_a_412_, 2);
v_a_413_ = lean_ctor_get(v___x_411_, 1);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_411_, 2);
v___x_414_ = l_Lake_loadConfigFile___redArg(v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_432_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_a_416_ = lean_ctor_get(v___x_414_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_432_ == 0)
{
v___x_418_ = v___x_414_;
v_isShared_419_ = v_isSharedCheck_432_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_432_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_facetDecls_420_; lean_object* v___x_421_; lean_object* v_keyName_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v_facetDecls_420_ = lean_ctor_get(v_a_415_, 2);
lean_inc_ref(v_facetDecls_420_);
v___x_421_ = l_Lake_mkPackage(v_a_412_, v_a_415_, v_wsIdx_401_);
lean_dec(v_a_412_);
v_keyName_422_ = lean_ctor_get(v___x_421_, 2);
lean_inc(v_keyName_422_);
lean_inc_ref(v___x_421_);
v___x_423_ = lean_array_push(v_packages_384_, v___x_421_);
v___x_424_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_422_, v___x_421_, v_packageMap_385_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 5, v___x_424_);
lean_ctor_set(v___x_388_, 4, v___x_423_);
v___x_426_ = v___x_388_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_lakeEnv_380_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_lakeConfig_381_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_lakeCache_382_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_lakeArgs_x3f_383_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v_facetConfigs_386_);
v___x_426_ = v_reuseFailAlloc_431_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(v_facetDecls_420_, v___x_426_);
lean_dec_ref(v_facetDecls_420_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_427_);
v___x_429_ = v___x_418_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_a_416_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_a_433_; lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_a_412_);
lean_del_object(v___x_388_);
lean_dec(v_facetConfigs_386_);
lean_dec(v_packageMap_385_);
lean_dec_ref(v_packages_384_);
lean_dec(v_lakeArgs_x3f_383_);
lean_dec_ref(v_lakeCache_382_);
lean_dec_ref(v_lakeConfig_381_);
lean_dec_ref(v_lakeEnv_380_);
v_a_433_ = lean_ctor_get(v___x_414_, 0);
v_a_434_ = lean_ctor_get(v___x_414_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_414_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_inc(v_a_433_);
lean_dec(v___x_414_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_433_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v_a_442_; lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_del_object(v___x_388_);
lean_dec(v_facetConfigs_386_);
lean_dec(v_packageMap_385_);
lean_dec_ref(v_packages_384_);
lean_dec(v_lakeArgs_x3f_383_);
lean_dec_ref(v_lakeCache_382_);
lean_dec_ref(v_lakeConfig_381_);
lean_dec_ref(v_lakeEnv_380_);
v_a_442_ = lean_ctor_get(v___x_411_, 0);
v_a_443_ = lean_ctor_get(v___x_411_, 1);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_411_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_inc(v_a_442_);
lean_dec(v___x_411_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_442_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27___boxed(lean_object* v_ws_454_, lean_object* v_dep_455_, lean_object* v_lakeOpts_456_, lean_object* v_leanOpts_457_, lean_object* v_reconfigure_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
uint8_t v_reconfigure_boxed_461_; lean_object* v_res_462_; 
v_reconfigure_boxed_461_ = lean_unbox(v_reconfigure_458_);
v_res_462_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_454_, v_dep_455_, v_lakeOpts_456_, v_leanOpts_457_, v_reconfigure_boxed_461_, v_a_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0(lean_object* v_00_u03b2_463_, lean_object* v_k_464_, lean_object* v_v_465_, lean_object* v_t_466_, lean_object* v_hl_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_464_, v_v_465_, v_t_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(lean_object* v_self_469_, lean_object* v_pkg_470_, lean_object* v_depIdxs_471_){
_start:
{
lean_object* v_wsIdx_472_; lean_object* v_baseName_473_; lean_object* v_keyName_474_; lean_object* v_origName_475_; lean_object* v_dir_476_; lean_object* v_relDir_477_; lean_object* v_config_478_; lean_object* v_configFile_479_; lean_object* v_relConfigFile_480_; lean_object* v_relManifestFile_481_; lean_object* v_scope_482_; lean_object* v_remoteUrl_483_; lean_object* v_depConfigs_484_; lean_object* v_depPkgs_485_; lean_object* v_targetDecls_486_; lean_object* v_targetDeclMap_487_; lean_object* v_defaultTargets_488_; lean_object* v_cacheServices_489_; lean_object* v_scripts_490_; lean_object* v_defaultScripts_491_; lean_object* v_postUpdateHooks_492_; lean_object* v_buildArchive_493_; lean_object* v_testDriver_494_; lean_object* v_lintDriver_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_518_; 
v_wsIdx_472_ = lean_ctor_get(v_pkg_470_, 0);
v_baseName_473_ = lean_ctor_get(v_pkg_470_, 1);
v_keyName_474_ = lean_ctor_get(v_pkg_470_, 2);
v_origName_475_ = lean_ctor_get(v_pkg_470_, 3);
v_dir_476_ = lean_ctor_get(v_pkg_470_, 4);
v_relDir_477_ = lean_ctor_get(v_pkg_470_, 5);
v_config_478_ = lean_ctor_get(v_pkg_470_, 6);
v_configFile_479_ = lean_ctor_get(v_pkg_470_, 7);
v_relConfigFile_480_ = lean_ctor_get(v_pkg_470_, 8);
v_relManifestFile_481_ = lean_ctor_get(v_pkg_470_, 9);
v_scope_482_ = lean_ctor_get(v_pkg_470_, 10);
v_remoteUrl_483_ = lean_ctor_get(v_pkg_470_, 11);
v_depConfigs_484_ = lean_ctor_get(v_pkg_470_, 12);
v_depPkgs_485_ = lean_ctor_get(v_pkg_470_, 14);
v_targetDecls_486_ = lean_ctor_get(v_pkg_470_, 15);
v_targetDeclMap_487_ = lean_ctor_get(v_pkg_470_, 16);
v_defaultTargets_488_ = lean_ctor_get(v_pkg_470_, 17);
v_cacheServices_489_ = lean_ctor_get(v_pkg_470_, 18);
v_scripts_490_ = lean_ctor_get(v_pkg_470_, 19);
v_defaultScripts_491_ = lean_ctor_get(v_pkg_470_, 20);
v_postUpdateHooks_492_ = lean_ctor_get(v_pkg_470_, 21);
v_buildArchive_493_ = lean_ctor_get(v_pkg_470_, 22);
v_testDriver_494_ = lean_ctor_get(v_pkg_470_, 23);
v_lintDriver_495_ = lean_ctor_get(v_pkg_470_, 24);
v_isSharedCheck_518_ = !lean_is_exclusive(v_pkg_470_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_pkg_470_, 13);
lean_dec(v_unused_519_);
v___x_497_ = v_pkg_470_;
v_isShared_498_ = v_isSharedCheck_518_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_lintDriver_495_);
lean_inc(v_testDriver_494_);
lean_inc(v_buildArchive_493_);
lean_inc(v_postUpdateHooks_492_);
lean_inc(v_defaultScripts_491_);
lean_inc(v_scripts_490_);
lean_inc(v_cacheServices_489_);
lean_inc(v_defaultTargets_488_);
lean_inc(v_targetDeclMap_487_);
lean_inc(v_targetDecls_486_);
lean_inc(v_depPkgs_485_);
lean_inc(v_depConfigs_484_);
lean_inc(v_remoteUrl_483_);
lean_inc(v_scope_482_);
lean_inc(v_relManifestFile_481_);
lean_inc(v_relConfigFile_480_);
lean_inc(v_configFile_479_);
lean_inc(v_config_478_);
lean_inc(v_relDir_477_);
lean_inc(v_dir_476_);
lean_inc(v_origName_475_);
lean_inc(v_keyName_474_);
lean_inc(v_baseName_473_);
lean_inc(v_wsIdx_472_);
lean_dec(v_pkg_470_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_518_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_lakeEnv_499_; lean_object* v_lakeConfig_500_; lean_object* v_lakeCache_501_; lean_object* v_lakeArgs_x3f_502_; lean_object* v_packages_503_; lean_object* v_packageMap_504_; lean_object* v_facetConfigs_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_517_; 
v_lakeEnv_499_ = lean_ctor_get(v_self_469_, 0);
v_lakeConfig_500_ = lean_ctor_get(v_self_469_, 1);
v_lakeCache_501_ = lean_ctor_get(v_self_469_, 2);
v_lakeArgs_x3f_502_ = lean_ctor_get(v_self_469_, 3);
v_packages_503_ = lean_ctor_get(v_self_469_, 4);
v_packageMap_504_ = lean_ctor_get(v_self_469_, 5);
v_facetConfigs_505_ = lean_ctor_get(v_self_469_, 6);
v_isSharedCheck_517_ = !lean_is_exclusive(v_self_469_);
if (v_isSharedCheck_517_ == 0)
{
v___x_507_ = v_self_469_;
v_isShared_508_ = v_isSharedCheck_517_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_facetConfigs_505_);
lean_inc(v_packageMap_504_);
lean_inc(v_packages_503_);
lean_inc(v_lakeArgs_x3f_502_);
lean_inc(v_lakeCache_501_);
lean_inc(v_lakeConfig_500_);
lean_inc(v_lakeEnv_499_);
lean_dec(v_self_469_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_517_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_pkg_510_; 
lean_inc(v_keyName_474_);
lean_inc(v_wsIdx_472_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 13, v_depIdxs_471_);
v_pkg_510_ = v___x_497_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 25, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_wsIdx_472_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_baseName_473_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_keyName_474_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_origName_475_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v_dir_476_);
lean_ctor_set(v_reuseFailAlloc_516_, 5, v_relDir_477_);
lean_ctor_set(v_reuseFailAlloc_516_, 6, v_config_478_);
lean_ctor_set(v_reuseFailAlloc_516_, 7, v_configFile_479_);
lean_ctor_set(v_reuseFailAlloc_516_, 8, v_relConfigFile_480_);
lean_ctor_set(v_reuseFailAlloc_516_, 9, v_relManifestFile_481_);
lean_ctor_set(v_reuseFailAlloc_516_, 10, v_scope_482_);
lean_ctor_set(v_reuseFailAlloc_516_, 11, v_remoteUrl_483_);
lean_ctor_set(v_reuseFailAlloc_516_, 12, v_depConfigs_484_);
lean_ctor_set(v_reuseFailAlloc_516_, 13, v_depIdxs_471_);
lean_ctor_set(v_reuseFailAlloc_516_, 14, v_depPkgs_485_);
lean_ctor_set(v_reuseFailAlloc_516_, 15, v_targetDecls_486_);
lean_ctor_set(v_reuseFailAlloc_516_, 16, v_targetDeclMap_487_);
lean_ctor_set(v_reuseFailAlloc_516_, 17, v_defaultTargets_488_);
lean_ctor_set(v_reuseFailAlloc_516_, 18, v_cacheServices_489_);
lean_ctor_set(v_reuseFailAlloc_516_, 19, v_scripts_490_);
lean_ctor_set(v_reuseFailAlloc_516_, 20, v_defaultScripts_491_);
lean_ctor_set(v_reuseFailAlloc_516_, 21, v_postUpdateHooks_492_);
lean_ctor_set(v_reuseFailAlloc_516_, 22, v_buildArchive_493_);
lean_ctor_set(v_reuseFailAlloc_516_, 23, v_testDriver_494_);
lean_ctor_set(v_reuseFailAlloc_516_, 24, v_lintDriver_495_);
v_pkg_510_ = v_reuseFailAlloc_516_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
lean_inc_ref(v_pkg_510_);
v___x_511_ = lean_array_fset(v_packages_503_, v_wsIdx_472_, v_pkg_510_);
lean_dec(v_wsIdx_472_);
v___x_512_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_474_, v_pkg_510_, v_packageMap_504_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 5, v___x_512_);
lean_ctor_set(v___x_507_, 4, v___x_511_);
v___x_514_ = v___x_507_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_lakeEnv_499_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_lakeConfig_500_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_lakeCache_501_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_lakeArgs_x3f_502_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_515_, 6, v_facetConfigs_505_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs(lean_object* v_self_520_, lean_object* v_pkg_521_, lean_object* v_depIdxs_522_, lean_object* v_h__wsIdx_523_, lean_object* v_h__depIdxs_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_self_520_, v_pkg_521_, v_depIdxs_522_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(lean_object* v_val_526_, size_t v_sz_527_, size_t v_i_528_, lean_object* v_bs_529_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = lean_usize_dec_lt(v_i_528_, v_sz_527_);
if (v___x_530_ == 0)
{
return v_bs_529_;
}
else
{
lean_object* v_v_531_; lean_object* v___x_532_; lean_object* v_bs_x27_533_; lean_object* v___x_534_; size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; 
v_v_531_ = lean_array_uget(v_bs_529_, v_i_528_);
v___x_532_ = lean_unsigned_to_nat(0u);
v_bs_x27_533_ = lean_array_uset(v_bs_529_, v_i_528_, v___x_532_);
v___x_534_ = lean_array_fget_borrowed(v_val_526_, v_v_531_);
lean_dec(v_v_531_);
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_528_, v___x_535_);
lean_inc(v___x_534_);
v___x_537_ = lean_array_uset(v_bs_x27_533_, v_i_528_, v___x_534_);
v_i_528_ = v___x_536_;
v_bs_529_ = v___x_537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0___boxed(lean_object* v_val_539_, lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_bs_542_){
_start:
{
size_t v_sz_boxed_543_; size_t v_i_boxed_544_; lean_object* v_res_545_; 
v_sz_boxed_543_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_544_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_val_539_, v_sz_boxed_543_, v_i_boxed_544_, v_bs_542_);
lean_dec_ref(v_val_539_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
lean_object* v_zero_548_; uint8_t v_isZero_549_; 
v_zero_548_ = lean_unsigned_to_nat(0u);
v_isZero_549_ = lean_nat_dec_eq(v_x_546_, v_zero_548_);
if (v_isZero_549_ == 1)
{
lean_dec(v_x_546_);
return v_x_547_;
}
else
{
lean_object* v_one_550_; lean_object* v_n_551_; lean_object* v_pkg_552_; lean_object* v_wsIdx_553_; lean_object* v_baseName_554_; lean_object* v_keyName_555_; lean_object* v_origName_556_; lean_object* v_dir_557_; lean_object* v_relDir_558_; lean_object* v_config_559_; lean_object* v_configFile_560_; lean_object* v_relConfigFile_561_; lean_object* v_relManifestFile_562_; lean_object* v_scope_563_; lean_object* v_remoteUrl_564_; lean_object* v_depConfigs_565_; lean_object* v_depIdxs_566_; lean_object* v_targetDecls_567_; lean_object* v_targetDeclMap_568_; lean_object* v_defaultTargets_569_; lean_object* v_cacheServices_570_; lean_object* v_scripts_571_; lean_object* v_defaultScripts_572_; lean_object* v_postUpdateHooks_573_; lean_object* v_buildArchive_574_; lean_object* v_testDriver_575_; lean_object* v_lintDriver_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_588_; 
v_one_550_ = lean_unsigned_to_nat(1u);
v_n_551_ = lean_nat_sub(v_x_546_, v_one_550_);
lean_dec(v_x_546_);
v_pkg_552_ = lean_array_fget(v_x_547_, v_n_551_);
v_wsIdx_553_ = lean_ctor_get(v_pkg_552_, 0);
v_baseName_554_ = lean_ctor_get(v_pkg_552_, 1);
v_keyName_555_ = lean_ctor_get(v_pkg_552_, 2);
v_origName_556_ = lean_ctor_get(v_pkg_552_, 3);
v_dir_557_ = lean_ctor_get(v_pkg_552_, 4);
v_relDir_558_ = lean_ctor_get(v_pkg_552_, 5);
v_config_559_ = lean_ctor_get(v_pkg_552_, 6);
v_configFile_560_ = lean_ctor_get(v_pkg_552_, 7);
v_relConfigFile_561_ = lean_ctor_get(v_pkg_552_, 8);
v_relManifestFile_562_ = lean_ctor_get(v_pkg_552_, 9);
v_scope_563_ = lean_ctor_get(v_pkg_552_, 10);
v_remoteUrl_564_ = lean_ctor_get(v_pkg_552_, 11);
v_depConfigs_565_ = lean_ctor_get(v_pkg_552_, 12);
v_depIdxs_566_ = lean_ctor_get(v_pkg_552_, 13);
v_targetDecls_567_ = lean_ctor_get(v_pkg_552_, 15);
v_targetDeclMap_568_ = lean_ctor_get(v_pkg_552_, 16);
v_defaultTargets_569_ = lean_ctor_get(v_pkg_552_, 17);
v_cacheServices_570_ = lean_ctor_get(v_pkg_552_, 18);
v_scripts_571_ = lean_ctor_get(v_pkg_552_, 19);
v_defaultScripts_572_ = lean_ctor_get(v_pkg_552_, 20);
v_postUpdateHooks_573_ = lean_ctor_get(v_pkg_552_, 21);
v_buildArchive_574_ = lean_ctor_get(v_pkg_552_, 22);
v_testDriver_575_ = lean_ctor_get(v_pkg_552_, 23);
v_lintDriver_576_ = lean_ctor_get(v_pkg_552_, 24);
v_isSharedCheck_588_ = !lean_is_exclusive(v_pkg_552_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v_pkg_552_, 14);
lean_dec(v_unused_589_);
v___x_578_ = v_pkg_552_;
v_isShared_579_ = v_isSharedCheck_588_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_lintDriver_576_);
lean_inc(v_testDriver_575_);
lean_inc(v_buildArchive_574_);
lean_inc(v_postUpdateHooks_573_);
lean_inc(v_defaultScripts_572_);
lean_inc(v_scripts_571_);
lean_inc(v_cacheServices_570_);
lean_inc(v_defaultTargets_569_);
lean_inc(v_targetDeclMap_568_);
lean_inc(v_targetDecls_567_);
lean_inc(v_depIdxs_566_);
lean_inc(v_depConfigs_565_);
lean_inc(v_remoteUrl_564_);
lean_inc(v_scope_563_);
lean_inc(v_relManifestFile_562_);
lean_inc(v_relConfigFile_561_);
lean_inc(v_configFile_560_);
lean_inc(v_config_559_);
lean_inc(v_relDir_558_);
lean_inc(v_dir_557_);
lean_inc(v_origName_556_);
lean_inc(v_keyName_555_);
lean_inc(v_baseName_554_);
lean_inc(v_wsIdx_553_);
lean_dec(v_pkg_552_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_588_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
size_t v_sz_580_; size_t v___x_581_; lean_object* v_depPkgs_582_; lean_object* v___x_584_; 
v_sz_580_ = lean_array_size(v_depIdxs_566_);
v___x_581_ = ((size_t)0ULL);
lean_inc_ref(v_depIdxs_566_);
v_depPkgs_582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_x_547_, v_sz_580_, v___x_581_, v_depIdxs_566_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 14, v_depPkgs_582_);
v___x_584_ = v___x_578_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 25, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_wsIdx_553_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_baseName_554_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_keyName_555_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v_origName_556_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v_dir_557_);
lean_ctor_set(v_reuseFailAlloc_587_, 5, v_relDir_558_);
lean_ctor_set(v_reuseFailAlloc_587_, 6, v_config_559_);
lean_ctor_set(v_reuseFailAlloc_587_, 7, v_configFile_560_);
lean_ctor_set(v_reuseFailAlloc_587_, 8, v_relConfigFile_561_);
lean_ctor_set(v_reuseFailAlloc_587_, 9, v_relManifestFile_562_);
lean_ctor_set(v_reuseFailAlloc_587_, 10, v_scope_563_);
lean_ctor_set(v_reuseFailAlloc_587_, 11, v_remoteUrl_564_);
lean_ctor_set(v_reuseFailAlloc_587_, 12, v_depConfigs_565_);
lean_ctor_set(v_reuseFailAlloc_587_, 13, v_depIdxs_566_);
lean_ctor_set(v_reuseFailAlloc_587_, 14, v_depPkgs_582_);
lean_ctor_set(v_reuseFailAlloc_587_, 15, v_targetDecls_567_);
lean_ctor_set(v_reuseFailAlloc_587_, 16, v_targetDeclMap_568_);
lean_ctor_set(v_reuseFailAlloc_587_, 17, v_defaultTargets_569_);
lean_ctor_set(v_reuseFailAlloc_587_, 18, v_cacheServices_570_);
lean_ctor_set(v_reuseFailAlloc_587_, 19, v_scripts_571_);
lean_ctor_set(v_reuseFailAlloc_587_, 20, v_defaultScripts_572_);
lean_ctor_set(v_reuseFailAlloc_587_, 21, v_postUpdateHooks_573_);
lean_ctor_set(v_reuseFailAlloc_587_, 22, v_buildArchive_574_);
lean_ctor_set(v_reuseFailAlloc_587_, 23, v_testDriver_575_);
lean_ctor_set(v_reuseFailAlloc_587_, 24, v_lintDriver_576_);
v___x_584_ = v_reuseFailAlloc_587_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v_pkgs_x27_585_; 
v_pkgs_x27_585_ = lean_array_fset(v_x_547_, v_n_551_, v___x_584_);
v_x_546_ = v_n_551_;
v_x_547_ = v_pkgs_x27_585_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(lean_object* v___x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v_zero_593_; uint8_t v_isZero_594_; 
v_zero_593_ = lean_unsigned_to_nat(0u);
v_isZero_594_ = lean_nat_dec_eq(v_x_591_, v_zero_593_);
if (v_isZero_594_ == 1)
{
return v_x_592_;
}
else
{
lean_object* v_one_595_; lean_object* v_n_596_; lean_object* v_pkg_597_; lean_object* v_wsIdx_598_; lean_object* v_baseName_599_; lean_object* v_keyName_600_; lean_object* v_origName_601_; lean_object* v_dir_602_; lean_object* v_relDir_603_; lean_object* v_config_604_; lean_object* v_configFile_605_; lean_object* v_relConfigFile_606_; lean_object* v_relManifestFile_607_; lean_object* v_scope_608_; lean_object* v_remoteUrl_609_; lean_object* v_depConfigs_610_; lean_object* v_depIdxs_611_; lean_object* v_targetDecls_612_; lean_object* v_targetDeclMap_613_; lean_object* v_defaultTargets_614_; lean_object* v_cacheServices_615_; lean_object* v_scripts_616_; lean_object* v_defaultScripts_617_; lean_object* v_postUpdateHooks_618_; lean_object* v_buildArchive_619_; lean_object* v_testDriver_620_; lean_object* v_lintDriver_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_633_; 
v_one_595_ = lean_unsigned_to_nat(1u);
v_n_596_ = lean_nat_sub(v_x_591_, v_one_595_);
v_pkg_597_ = lean_array_fget(v_x_592_, v_n_596_);
v_wsIdx_598_ = lean_ctor_get(v_pkg_597_, 0);
v_baseName_599_ = lean_ctor_get(v_pkg_597_, 1);
v_keyName_600_ = lean_ctor_get(v_pkg_597_, 2);
v_origName_601_ = lean_ctor_get(v_pkg_597_, 3);
v_dir_602_ = lean_ctor_get(v_pkg_597_, 4);
v_relDir_603_ = lean_ctor_get(v_pkg_597_, 5);
v_config_604_ = lean_ctor_get(v_pkg_597_, 6);
v_configFile_605_ = lean_ctor_get(v_pkg_597_, 7);
v_relConfigFile_606_ = lean_ctor_get(v_pkg_597_, 8);
v_relManifestFile_607_ = lean_ctor_get(v_pkg_597_, 9);
v_scope_608_ = lean_ctor_get(v_pkg_597_, 10);
v_remoteUrl_609_ = lean_ctor_get(v_pkg_597_, 11);
v_depConfigs_610_ = lean_ctor_get(v_pkg_597_, 12);
v_depIdxs_611_ = lean_ctor_get(v_pkg_597_, 13);
v_targetDecls_612_ = lean_ctor_get(v_pkg_597_, 15);
v_targetDeclMap_613_ = lean_ctor_get(v_pkg_597_, 16);
v_defaultTargets_614_ = lean_ctor_get(v_pkg_597_, 17);
v_cacheServices_615_ = lean_ctor_get(v_pkg_597_, 18);
v_scripts_616_ = lean_ctor_get(v_pkg_597_, 19);
v_defaultScripts_617_ = lean_ctor_get(v_pkg_597_, 20);
v_postUpdateHooks_618_ = lean_ctor_get(v_pkg_597_, 21);
v_buildArchive_619_ = lean_ctor_get(v_pkg_597_, 22);
v_testDriver_620_ = lean_ctor_get(v_pkg_597_, 23);
v_lintDriver_621_ = lean_ctor_get(v_pkg_597_, 24);
v_isSharedCheck_633_ = !lean_is_exclusive(v_pkg_597_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v_pkg_597_, 14);
lean_dec(v_unused_634_);
v___x_623_ = v_pkg_597_;
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_lintDriver_621_);
lean_inc(v_testDriver_620_);
lean_inc(v_buildArchive_619_);
lean_inc(v_postUpdateHooks_618_);
lean_inc(v_defaultScripts_617_);
lean_inc(v_scripts_616_);
lean_inc(v_cacheServices_615_);
lean_inc(v_defaultTargets_614_);
lean_inc(v_targetDeclMap_613_);
lean_inc(v_targetDecls_612_);
lean_inc(v_depIdxs_611_);
lean_inc(v_depConfigs_610_);
lean_inc(v_remoteUrl_609_);
lean_inc(v_scope_608_);
lean_inc(v_relManifestFile_607_);
lean_inc(v_relConfigFile_606_);
lean_inc(v_configFile_605_);
lean_inc(v_config_604_);
lean_inc(v_relDir_603_);
lean_inc(v_dir_602_);
lean_inc(v_origName_601_);
lean_inc(v_keyName_600_);
lean_inc(v_baseName_599_);
lean_inc(v_wsIdx_598_);
lean_dec(v_pkg_597_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
size_t v_sz_625_; size_t v___x_626_; lean_object* v_depPkgs_627_; lean_object* v___x_629_; 
v_sz_625_ = lean_array_size(v_depIdxs_611_);
v___x_626_ = ((size_t)0ULL);
lean_inc_ref(v_depIdxs_611_);
v_depPkgs_627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_x_592_, v_sz_625_, v___x_626_, v_depIdxs_611_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 14, v_depPkgs_627_);
v___x_629_ = v___x_623_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 25, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_wsIdx_598_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_baseName_599_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_keyName_600_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_origName_601_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_dir_602_);
lean_ctor_set(v_reuseFailAlloc_632_, 5, v_relDir_603_);
lean_ctor_set(v_reuseFailAlloc_632_, 6, v_config_604_);
lean_ctor_set(v_reuseFailAlloc_632_, 7, v_configFile_605_);
lean_ctor_set(v_reuseFailAlloc_632_, 8, v_relConfigFile_606_);
lean_ctor_set(v_reuseFailAlloc_632_, 9, v_relManifestFile_607_);
lean_ctor_set(v_reuseFailAlloc_632_, 10, v_scope_608_);
lean_ctor_set(v_reuseFailAlloc_632_, 11, v_remoteUrl_609_);
lean_ctor_set(v_reuseFailAlloc_632_, 12, v_depConfigs_610_);
lean_ctor_set(v_reuseFailAlloc_632_, 13, v_depIdxs_611_);
lean_ctor_set(v_reuseFailAlloc_632_, 14, v_depPkgs_627_);
lean_ctor_set(v_reuseFailAlloc_632_, 15, v_targetDecls_612_);
lean_ctor_set(v_reuseFailAlloc_632_, 16, v_targetDeclMap_613_);
lean_ctor_set(v_reuseFailAlloc_632_, 17, v_defaultTargets_614_);
lean_ctor_set(v_reuseFailAlloc_632_, 18, v_cacheServices_615_);
lean_ctor_set(v_reuseFailAlloc_632_, 19, v_scripts_616_);
lean_ctor_set(v_reuseFailAlloc_632_, 20, v_defaultScripts_617_);
lean_ctor_set(v_reuseFailAlloc_632_, 21, v_postUpdateHooks_618_);
lean_ctor_set(v_reuseFailAlloc_632_, 22, v_buildArchive_619_);
lean_ctor_set(v_reuseFailAlloc_632_, 23, v_testDriver_620_);
lean_ctor_set(v_reuseFailAlloc_632_, 24, v_lintDriver_621_);
v___x_629_ = v_reuseFailAlloc_632_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v_pkgs_x27_630_; lean_object* v___x_631_; 
v_pkgs_x27_630_ = lean_array_fset(v_x_592_, v_n_596_, v___x_629_);
v___x_631_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(v_n_596_, v_pkgs_x27_630_);
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1___boxed(lean_object* v___x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(v___x_635_, v_x_636_, v_x_637_);
lean_dec(v_x_636_);
lean_dec(v___x_635_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(lean_object* v_as_639_, size_t v_i_640_, size_t v_stop_641_, lean_object* v_b_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = lean_usize_dec_eq(v_i_640_, v_stop_641_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v_keyName_645_; lean_object* v___x_646_; size_t v___x_647_; size_t v___x_648_; 
v___x_644_ = lean_array_uget_borrowed(v_as_639_, v_i_640_);
v_keyName_645_ = lean_ctor_get(v___x_644_, 2);
lean_inc(v___x_644_);
lean_inc(v_keyName_645_);
v___x_646_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_645_, v___x_644_, v_b_642_);
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_640_, v___x_647_);
v_i_640_ = v___x_648_;
v_b_642_ = v___x_646_;
goto _start;
}
else
{
return v_b_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2___boxed(lean_object* v_as_650_, lean_object* v_i_651_, lean_object* v_stop_652_, lean_object* v_b_653_){
_start:
{
size_t v_i_boxed_654_; size_t v_stop_boxed_655_; lean_object* v_res_656_; 
v_i_boxed_654_ = lean_unbox_usize(v_i_651_);
lean_dec(v_i_651_);
v_stop_boxed_655_ = lean_unbox_usize(v_stop_652_);
lean_dec(v_stop_652_);
v_res_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_as_650_, v_i_boxed_654_, v_stop_boxed_655_, v_b_653_);
lean_dec_ref(v_as_650_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(lean_object* v_self_657_){
_start:
{
lean_object* v_lakeEnv_658_; lean_object* v_lakeConfig_659_; lean_object* v_lakeCache_660_; lean_object* v_lakeArgs_x3f_661_; lean_object* v_packages_662_; lean_object* v_facetConfigs_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_682_; 
v_lakeEnv_658_ = lean_ctor_get(v_self_657_, 0);
v_lakeConfig_659_ = lean_ctor_get(v_self_657_, 1);
v_lakeCache_660_ = lean_ctor_get(v_self_657_, 2);
v_lakeArgs_x3f_661_ = lean_ctor_get(v_self_657_, 3);
v_packages_662_ = lean_ctor_get(v_self_657_, 4);
v_facetConfigs_663_ = lean_ctor_get(v_self_657_, 6);
v_isSharedCheck_682_ = !lean_is_exclusive(v_self_657_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v_self_657_, 5);
lean_dec(v_unused_683_);
v___x_665_ = v_self_657_;
v_isShared_666_ = v_isSharedCheck_682_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_facetConfigs_663_);
lean_inc(v_packages_662_);
lean_inc(v_lakeArgs_x3f_661_);
lean_inc(v_lakeCache_660_);
lean_inc(v_lakeConfig_659_);
lean_inc(v_lakeEnv_658_);
lean_dec(v_self_657_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_682_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v_val_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_667_ = lean_array_get_size(v_packages_662_);
v_val_668_ = l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(v___x_667_, v___x_667_, v_packages_662_);
v___x_669_ = lean_box(1);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_array_get_size(v_val_668_);
v___x_672_ = lean_nat_dec_lt(v___x_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_674_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 5, v___x_669_);
lean_ctor_set(v___x_665_, 4, v_val_668_);
v___x_674_ = v___x_665_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_lakeEnv_658_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_lakeConfig_659_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_lakeCache_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_lakeArgs_x3f_661_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_val_668_);
lean_ctor_set(v_reuseFailAlloc_675_, 5, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_675_, 6, v_facetConfigs_663_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
else
{
size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_676_ = ((size_t)0ULL);
v___x_677_ = lean_usize_of_nat(v___x_671_);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_val_668_, v___x_676_, v___x_677_, v___x_669_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 5, v___x_678_);
lean_ctor_set(v___x_665_, 4, v_val_668_);
v___x_680_ = v___x_665_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_lakeEnv_658_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_lakeConfig_659_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_lakeCache_660_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_lakeArgs_x3f_661_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_val_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 5, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 6, v_facetConfigs_663_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(lean_object* v___x_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(v_x_685_, v_x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___boxed(lean_object* v___x_688_, lean_object* v_x_689_, lean_object* v_x_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(v___x_688_, v_x_689_, v_x_690_);
lean_dec(v___x_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(lean_object* v_ws_692_, lean_object* v_size_693_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_mk_empty_array_with_capacity(v_size_693_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_ws_692_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init___boxed(lean_object* v_ws_696_, lean_object* v_size_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(v_ws_696_, v_size_697_);
lean_dec(v_size_697_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___redArg(lean_object* v_s_699_, lean_object* v_wsIdx_700_){
_start:
{
lean_object* v_ws_701_; lean_object* v_depIdxs_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
v_ws_701_ = lean_ctor_get(v_s_699_, 0);
v_depIdxs_702_ = lean_ctor_get(v_s_699_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_s_699_);
if (v_isSharedCheck_710_ == 0)
{
v___x_704_ = v_s_699_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_depIdxs_702_);
lean_inc(v_ws_701_);
lean_dec(v_s_699_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = lean_array_push(v_depIdxs_702_, v_wsIdx_700_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_ws_701_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(lean_object* v_n_711_, lean_object* v_s_712_, lean_object* v_wsIdx_713_){
_start:
{
lean_object* v_ws_714_; lean_object* v_depIdxs_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
v_ws_714_ = lean_ctor_get(v_s_712_, 0);
v_depIdxs_715_ = lean_ctor_get(v_s_712_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_s_712_);
if (v_isSharedCheck_723_ == 0)
{
v___x_717_ = v_s_712_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_depIdxs_715_);
lean_inc(v_ws_714_);
lean_dec(v_s_712_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_array_push(v_depIdxs_715_, v_wsIdx_713_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_ws_714_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___boxed(lean_object* v_n_724_, lean_object* v_s_725_, lean_object* v_wsIdx_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(v_n_724_, v_s_725_, v_wsIdx_726_);
lean_dec(v_n_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(lean_object* v_s_728_, lean_object* v_dep_729_, lean_object* v_lakeOpts_730_, lean_object* v_leanOpts_731_, uint8_t v_reconfigure_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_ws_735_; lean_object* v_depIdxs_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_765_; 
v_ws_735_ = lean_ctor_get(v_s_728_, 0);
v_depIdxs_736_ = lean_ctor_get(v_s_728_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_s_728_);
if (v_isSharedCheck_765_ == 0)
{
v___x_738_ = v_s_728_;
v_isShared_739_ = v_isSharedCheck_765_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_depIdxs_736_);
lean_inc(v_ws_735_);
lean_dec(v_s_728_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_765_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_packages_740_; lean_object* v_wsIdx_741_; lean_object* v___x_742_; 
v_packages_740_ = lean_ctor_get(v_ws_735_, 4);
v_wsIdx_741_ = lean_array_get_size(v_packages_740_);
v___x_742_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_735_, v_dep_729_, v_lakeOpts_730_, v_leanOpts_731_, v_reconfigure_732_, v_a_733_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_755_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_a_744_ = lean_ctor_get(v___x_742_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_755_ == 0)
{
v___x_746_ = v___x_742_;
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_array_push(v_depIdxs_736_, v_wsIdx_741_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_748_);
lean_ctor_set(v___x_738_, 0, v_a_743_);
v___x_750_ = v___x_738_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_743_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_748_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_750_);
v___x_752_ = v___x_746_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_a_744_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_del_object(v___x_738_);
lean_dec_ref(v_depIdxs_736_);
v_a_756_ = lean_ctor_get(v___x_742_, 0);
v_a_757_ = lean_ctor_get(v___x_742_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_742_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_inc(v_a_756_);
lean_dec(v___x_742_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_756_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg___boxed(lean_object* v_s_766_, lean_object* v_dep_767_, lean_object* v_lakeOpts_768_, lean_object* v_leanOpts_769_, lean_object* v_reconfigure_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
uint8_t v_reconfigure_boxed_773_; lean_object* v_res_774_; 
v_reconfigure_boxed_773_ = lean_unbox(v_reconfigure_770_);
v_res_774_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(v_s_766_, v_dep_767_, v_lakeOpts_768_, v_leanOpts_769_, v_reconfigure_boxed_773_, v_a_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(lean_object* v_n_775_, lean_object* v_s_776_, lean_object* v_dep_777_, lean_object* v_lakeOpts_778_, lean_object* v_leanOpts_779_, uint8_t v_reconfigure_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_ws_783_; lean_object* v_depIdxs_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_813_; 
v_ws_783_ = lean_ctor_get(v_s_776_, 0);
v_depIdxs_784_ = lean_ctor_get(v_s_776_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_s_776_);
if (v_isSharedCheck_813_ == 0)
{
v___x_786_ = v_s_776_;
v_isShared_787_ = v_isSharedCheck_813_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_depIdxs_784_);
lean_inc(v_ws_783_);
lean_dec(v_s_776_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_813_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_packages_788_; lean_object* v_wsIdx_789_; lean_object* v___x_790_; 
v_packages_788_ = lean_ctor_get(v_ws_783_, 4);
v_wsIdx_789_ = lean_array_get_size(v_packages_788_);
v___x_790_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_783_, v_dep_777_, v_lakeOpts_778_, v_leanOpts_779_, v_reconfigure_780_, v_a_781_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_803_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_a_792_ = lean_ctor_get(v___x_790_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_803_ == 0)
{
v___x_794_ = v___x_790_;
v_isShared_795_ = v_isSharedCheck_803_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_803_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_array_push(v_depIdxs_784_, v_wsIdx_789_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_796_);
lean_ctor_set(v___x_786_, 0, v_a_791_);
v___x_798_ = v___x_786_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_791_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_796_);
v___x_798_ = v_reuseFailAlloc_802_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_800_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_798_);
v___x_800_ = v___x_794_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_a_792_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_del_object(v___x_786_);
lean_dec_ref(v_depIdxs_784_);
v_a_804_ = lean_ctor_get(v___x_790_, 0);
v_a_805_ = lean_ctor_get(v___x_790_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_790_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_inc(v_a_804_);
lean_dec(v___x_790_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_804_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed(lean_object* v_n_814_, lean_object* v_s_815_, lean_object* v_dep_816_, lean_object* v_lakeOpts_817_, lean_object* v_leanOpts_818_, lean_object* v_reconfigure_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
uint8_t v_reconfigure_boxed_822_; lean_object* v_res_823_; 
v_reconfigure_boxed_822_ = lean_unbox(v_reconfigure_819_);
v_res_823_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(v_n_814_, v_s_815_, v_dep_816_, v_lakeOpts_817_, v_leanOpts_818_, v_reconfigure_boxed_822_, v_a_820_);
lean_dec(v_n_814_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___redArg(lean_object* v_inst_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = lean_apply_2(v_inst_824_, lean_box(0), lean_box(0));
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(lean_object* v_m_826_, lean_object* v_00_u03b1_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_as_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = lean_apply_2(v_inst_828_, lean_box(0), lean_box(0));
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___boxed(lean_object* v_m_832_, lean_object* v_00_u03b1_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_as_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(v_m_832_, v_00_u03b1_833_, v_inst_834_, v_inst_835_, v_as_836_);
lean_dec_ref(v_as_836_);
lean_dec(v_inst_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object* v_resolve_838_, lean_object* v_pkg_839_, lean_object* v_dep_840_, lean_object* v_ws_841_, lean_object* v_toBind_842_, lean_object* v___f_843_, lean_object* v_____r_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_apply_3(v_resolve_838_, v_pkg_839_, v_dep_840_, v_ws_841_);
v___x_846_ = lean_apply_4(v_toBind_842_, lean_box(0), lean_box(0), v___x_845_, v___f_843_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object* v_start_847_, lean_object* v_s_848_, lean_object* v_opts_849_, lean_object* v_leanOpts_850_, uint8_t v_reconfigure_851_, lean_object* v_inst_852_, lean_object* v_matDep_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_box(v_reconfigure_851_);
v___x_855_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed), 8, 6);
lean_closure_set(v___x_855_, 0, v_start_847_);
lean_closure_set(v___x_855_, 1, v_s_848_);
lean_closure_set(v___x_855_, 2, v_matDep_853_);
lean_closure_set(v___x_855_, 3, v_opts_849_);
lean_closure_set(v___x_855_, 4, v_leanOpts_850_);
lean_closure_set(v___x_855_, 5, v___x_854_);
v___x_856_ = lean_apply_2(v_inst_852_, lean_box(0), v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object* v_start_857_, lean_object* v_s_858_, lean_object* v_opts_859_, lean_object* v_leanOpts_860_, lean_object* v_reconfigure_861_, lean_object* v_inst_862_, lean_object* v_matDep_863_){
_start:
{
uint8_t v_reconfigure_boxed_864_; lean_object* v_res_865_; 
v_reconfigure_boxed_864_ = lean_unbox(v_reconfigure_861_);
v_res_865_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(v_start_857_, v_s_858_, v_opts_859_, v_leanOpts_860_, v_reconfigure_boxed_864_, v_inst_862_, v_matDep_863_);
return v_res_865_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object* v_dep_866_, lean_object* v_x_867_){
_start:
{
lean_object* v_baseName_868_; lean_object* v_name_869_; uint8_t v___x_870_; 
v_baseName_868_ = lean_ctor_get(v_x_867_, 1);
v_name_869_ = lean_ctor_get(v_dep_866_, 0);
v___x_870_ = lean_name_eq(v_baseName_868_, v_name_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed(lean_object* v_dep_871_, lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(v_dep_871_, v_x_872_);
lean_dec_ref(v_x_872_);
lean_dec_ref(v_dep_871_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object* v___f_875_, lean_object* v_____r_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_apply_1(v___f_875_, v_____r_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object* v_toPure_879_, lean_object* v_start_880_, lean_object* v_leanOpts_881_, uint8_t v_reconfigure_882_, lean_object* v_inst_883_, lean_object* v_resolve_884_, lean_object* v_pkg_885_, lean_object* v_toBind_886_, lean_object* v_baseName_887_, lean_object* v_inst_888_, lean_object* v_dep_889_, lean_object* v_s_890_){
_start:
{
lean_object* v_ws_891_; lean_object* v_depIdxs_892_; lean_object* v_packages_893_; lean_object* v___f_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_ws_891_ = lean_ctor_get(v_s_890_, 0);
lean_inc_ref(v_ws_891_);
v_depIdxs_892_ = lean_ctor_get(v_s_890_, 1);
v_packages_893_ = lean_ctor_get(v_ws_891_, 4);
lean_inc_ref(v_dep_889_);
v___f_894_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_894_, 0, v_dep_889_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_894_, v_packages_893_, v___x_895_);
if (lean_obj_tag(v___x_896_) == 1)
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_906_; 
lean_inc_ref(v_depIdxs_892_);
lean_dec_ref(v_dep_889_);
lean_dec(v_inst_888_);
lean_dec(v_baseName_887_);
lean_dec(v_toBind_886_);
lean_dec_ref(v_pkg_885_);
lean_dec(v_resolve_884_);
lean_dec(v_inst_883_);
lean_dec_ref(v_leanOpts_881_);
lean_dec(v_start_880_);
v_isSharedCheck_906_ = !lean_is_exclusive(v_s_890_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; lean_object* v_unused_908_; 
v_unused_907_ = lean_ctor_get(v_s_890_, 1);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_s_890_, 0);
lean_dec(v_unused_908_);
v___x_898_ = v_s_890_;
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
else
{
lean_dec(v_s_890_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_val_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v_val_900_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v___x_896_, 1);
v___x_901_ = lean_array_push(v_depIdxs_892_, v_val_900_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_901_);
v___x_903_ = v___x_898_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_ws_891_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_905_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; 
v___x_904_ = lean_apply_2(v_toPure_879_, lean_box(0), v___x_903_);
return v___x_904_;
}
}
}
else
{
lean_object* v_name_909_; lean_object* v_opts_910_; lean_object* v___x_911_; lean_object* v___f_912_; lean_object* v___f_913_; uint8_t v___x_914_; 
lean_dec(v___x_896_);
lean_dec(v_toPure_879_);
v_name_909_ = lean_ctor_get(v_dep_889_, 0);
v_opts_910_ = lean_ctor_get(v_dep_889_, 4);
v___x_911_ = lean_box(v_reconfigure_882_);
lean_inc(v_opts_910_);
v___f_912_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_912_, 0, v_start_880_);
lean_closure_set(v___f_912_, 1, v_s_890_);
lean_closure_set(v___f_912_, 2, v_opts_910_);
lean_closure_set(v___f_912_, 3, v_leanOpts_881_);
lean_closure_set(v___f_912_, 4, v___x_911_);
lean_closure_set(v___f_912_, 5, v_inst_883_);
lean_inc_ref(v___f_912_);
lean_inc(v_toBind_886_);
lean_inc_ref(v_ws_891_);
lean_inc_ref(v_dep_889_);
lean_inc_ref(v_pkg_885_);
lean_inc(v_resolve_884_);
v___f_913_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4), 7, 6);
lean_closure_set(v___f_913_, 0, v_resolve_884_);
lean_closure_set(v___f_913_, 1, v_pkg_885_);
lean_closure_set(v___f_913_, 2, v_dep_889_);
lean_closure_set(v___f_913_, 3, v_ws_891_);
lean_closure_set(v___f_913_, 4, v_toBind_886_);
lean_closure_set(v___f_913_, 5, v___f_912_);
v___x_914_ = lean_name_eq(v_baseName_887_, v_name_909_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec_ref(v___f_913_);
lean_dec(v_inst_888_);
lean_dec(v_baseName_887_);
v___x_915_ = lean_box(0);
v___x_916_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(v_resolve_884_, v_pkg_885_, v_dep_889_, v_ws_891_, v_toBind_886_, v___f_912_, v___x_915_);
return v___x_916_;
}
else
{
lean_object* v___f_917_; uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec_ref(v___f_912_);
lean_dec_ref(v_ws_891_);
lean_dec_ref(v_dep_889_);
lean_dec_ref(v_pkg_885_);
lean_dec(v_resolve_884_);
v___f_917_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5), 2, 1);
lean_closure_set(v___f_917_, 0, v___f_913_);
v___x_918_ = 0;
v___x_919_ = l_Lean_Name_toString(v_baseName_887_, v___x_918_);
v___x_920_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_921_ = lean_string_append(v___x_919_, v___x_920_);
v___x_922_ = lean_apply_2(v_inst_888_, lean_box(0), v___x_921_);
v___x_923_ = lean_apply_4(v_toBind_886_, lean_box(0), lean_box(0), v___x_922_, v___f_917_);
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object* v_toPure_924_, lean_object* v_start_925_, lean_object* v_leanOpts_926_, lean_object* v_reconfigure_927_, lean_object* v_inst_928_, lean_object* v_resolve_929_, lean_object* v_pkg_930_, lean_object* v_toBind_931_, lean_object* v_baseName_932_, lean_object* v_inst_933_, lean_object* v_dep_934_, lean_object* v_s_935_){
_start:
{
uint8_t v_reconfigure_boxed_936_; lean_object* v_res_937_; 
v_reconfigure_boxed_936_ = lean_unbox(v_reconfigure_927_);
v_res_937_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(v_toPure_924_, v_start_925_, v_leanOpts_926_, v_reconfigure_boxed_936_, v_inst_928_, v_resolve_929_, v_pkg_930_, v_toBind_931_, v_baseName_932_, v_inst_933_, v_dep_934_, v_s_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0___boxed(lean_object* v_next_938_, lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_resolve_942_, lean_object* v_leanOpts_943_, lean_object* v_reconfigure_944_, lean_object* v_ws_945_, lean_object* v_____x_946_){
_start:
{
uint8_t v_reconfigure_boxed_947_; lean_object* v_res_948_; 
v_reconfigure_boxed_947_ = lean_unbox(v_reconfigure_944_);
v_res_948_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(v_next_938_, v_inst_939_, v_inst_940_, v_inst_941_, v_resolve_942_, v_leanOpts_943_, v_reconfigure_boxed_947_, v_ws_945_, v_____x_946_);
lean_dec(v_next_938_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object* v_pkg_949_, lean_object* v_next_950_, lean_object* v_toPure_951_, lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_resolve_955_, lean_object* v_leanOpts_956_, uint8_t v_reconfigure_957_, lean_object* v_toBind_958_, lean_object* v_____x_959_){
_start:
{
lean_object* v_ws_960_; lean_object* v_depIdxs_961_; lean_object* v_ws_962_; lean_object* v_packages_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v_ws_960_ = lean_ctor_get(v_____x_959_, 0);
lean_inc_ref(v_ws_960_);
v_depIdxs_961_ = lean_ctor_get(v_____x_959_, 1);
lean_inc_ref(v_depIdxs_961_);
lean_dec_ref(v_____x_959_);
v_ws_962_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_960_, v_pkg_949_, v_depIdxs_961_);
v_packages_963_ = lean_ctor_get(v_ws_962_, 4);
v___x_964_ = lean_array_get_size(v_packages_963_);
v___x_965_ = lean_nat_dec_lt(v_next_950_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
lean_dec(v_toBind_958_);
lean_dec_ref(v_leanOpts_956_);
lean_dec(v_resolve_955_);
lean_dec(v_inst_954_);
lean_dec(v_inst_953_);
lean_dec_ref(v_inst_952_);
lean_dec(v_next_950_);
v___x_966_ = lean_apply_2(v_toPure_951_, lean_box(0), v_ws_962_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v___f_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = lean_box(v_reconfigure_957_);
v___f_968_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_968_, 0, v_next_950_);
lean_closure_set(v___f_968_, 1, v_inst_952_);
lean_closure_set(v___f_968_, 2, v_inst_953_);
lean_closure_set(v___f_968_, 3, v_inst_954_);
lean_closure_set(v___f_968_, 4, v_resolve_955_);
lean_closure_set(v___f_968_, 5, v_leanOpts_956_);
lean_closure_set(v___f_968_, 6, v___x_967_);
lean_closure_set(v___f_968_, 7, v_ws_962_);
v___x_969_ = lean_apply_2(v_toPure_951_, lean_box(0), lean_box(0));
v___x_970_ = lean_apply_4(v_toBind_958_, lean_box(0), lean_box(0), v___x_969_, v___f_968_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed(lean_object* v_pkg_971_, lean_object* v_next_972_, lean_object* v_toPure_973_, lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_resolve_977_, lean_object* v_leanOpts_978_, lean_object* v_reconfigure_979_, lean_object* v_toBind_980_, lean_object* v_____x_981_){
_start:
{
uint8_t v_reconfigure_boxed_982_; lean_object* v_res_983_; 
v_reconfigure_boxed_982_ = lean_unbox(v_reconfigure_979_);
v_res_983_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(v_pkg_971_, v_next_972_, v_toPure_973_, v_inst_974_, v_inst_975_, v_inst_976_, v_resolve_977_, v_leanOpts_978_, v_reconfigure_boxed_982_, v_toBind_980_, v_____x_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object* v_inst_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_resolve_987_, lean_object* v_leanOpts_988_, uint8_t v_reconfigure_989_, lean_object* v_ws_990_, lean_object* v_i_991_, lean_object* v_next_992_){
_start:
{
lean_object* v_packages_993_; lean_object* v_pkg_994_; lean_object* v_toApplicative_995_; lean_object* v_baseName_996_; lean_object* v_depConfigs_997_; lean_object* v_toBind_998_; lean_object* v_toPure_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_s_1002_; lean_object* v___x_1003_; lean_object* v___f_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v_packages_993_ = lean_ctor_get(v_ws_990_, 4);
lean_inc_ref(v_packages_993_);
v_pkg_994_ = lean_array_fget(v_packages_993_, v_i_991_);
v_toApplicative_995_ = lean_ctor_get(v_inst_984_, 0);
v_baseName_996_ = lean_ctor_get(v_pkg_994_, 1);
lean_inc(v_baseName_996_);
v_depConfigs_997_ = lean_ctor_get(v_pkg_994_, 12);
lean_inc_ref(v_depConfigs_997_);
v_toBind_998_ = lean_ctor_get(v_inst_984_, 1);
lean_inc_n(v_toBind_998_, 2);
v_toPure_999_ = lean_ctor_get(v_toApplicative_995_, 1);
v___x_1000_ = lean_array_get_size(v_depConfigs_997_);
v___x_1001_ = lean_mk_empty_array_with_capacity(v___x_1000_);
v_s_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_1002_, 0, v_ws_990_);
lean_ctor_set(v_s_1002_, 1, v___x_1001_);
v___x_1003_ = lean_box(v_reconfigure_989_);
lean_inc_ref(v_leanOpts_988_);
lean_inc(v_resolve_987_);
lean_inc(v_inst_986_);
lean_inc(v_inst_985_);
lean_inc_ref(v_inst_984_);
lean_inc(v_toPure_999_);
lean_inc(v_pkg_994_);
v___f_1004_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_1004_, 0, v_pkg_994_);
lean_closure_set(v___f_1004_, 1, v_next_992_);
lean_closure_set(v___f_1004_, 2, v_toPure_999_);
lean_closure_set(v___f_1004_, 3, v_inst_984_);
lean_closure_set(v___f_1004_, 4, v_inst_985_);
lean_closure_set(v___f_1004_, 5, v_inst_986_);
lean_closure_set(v___f_1004_, 6, v_resolve_987_);
lean_closure_set(v___f_1004_, 7, v_leanOpts_988_);
lean_closure_set(v___f_1004_, 8, v___x_1003_);
lean_closure_set(v___f_1004_, 9, v_toBind_998_);
v___x_1005_ = lean_unsigned_to_nat(0u);
v___x_1006_ = lean_nat_dec_lt(v___x_1005_, v___x_1000_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_inc(v_toPure_999_);
lean_dec_ref(v_depConfigs_997_);
lean_dec(v_baseName_996_);
lean_dec(v_pkg_994_);
lean_dec_ref(v_packages_993_);
lean_dec_ref(v_leanOpts_988_);
lean_dec(v_resolve_987_);
lean_dec(v_inst_986_);
lean_dec(v_inst_985_);
lean_dec_ref(v_inst_984_);
v___x_1007_ = lean_apply_2(v_toPure_999_, lean_box(0), v_s_1002_);
v___x_1008_ = lean_apply_4(v_toBind_998_, lean_box(0), lean_box(0), v___x_1007_, v___f_1004_);
return v___x_1008_;
}
else
{
lean_object* v_start_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; size_t v___x_1012_; size_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_start_1009_ = lean_array_get_size(v_packages_993_);
lean_dec_ref(v_packages_993_);
v___x_1010_ = lean_box(v_reconfigure_989_);
lean_inc(v_toBind_998_);
lean_inc(v_toPure_999_);
v___f_1011_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed), 12, 10);
lean_closure_set(v___f_1011_, 0, v_toPure_999_);
lean_closure_set(v___f_1011_, 1, v_start_1009_);
lean_closure_set(v___f_1011_, 2, v_leanOpts_988_);
lean_closure_set(v___f_1011_, 3, v___x_1010_);
lean_closure_set(v___f_1011_, 4, v_inst_986_);
lean_closure_set(v___f_1011_, 5, v_resolve_987_);
lean_closure_set(v___f_1011_, 6, v_pkg_994_);
lean_closure_set(v___f_1011_, 7, v_toBind_998_);
lean_closure_set(v___f_1011_, 8, v_baseName_996_);
lean_closure_set(v___f_1011_, 9, v_inst_985_);
v___x_1012_ = lean_usize_of_nat(v___x_1000_);
v___x_1013_ = ((size_t)0ULL);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_984_, v___f_1011_, v_depConfigs_997_, v___x_1012_, v___x_1013_, v_s_1002_);
v___x_1015_ = lean_apply_4(v_toBind_998_, lean_box(0), lean_box(0), v___x_1014_, v___f_1004_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object* v_next_1016_, lean_object* v_inst_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_resolve_1020_, lean_object* v_leanOpts_1021_, uint8_t v_reconfigure_1022_, lean_object* v_ws_1023_, lean_object* v_____x_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_unsigned_to_nat(1u);
v___x_1026_ = lean_nat_add(v_next_1016_, v___x_1025_);
v___x_1027_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1017_, v_inst_1018_, v_inst_1019_, v_resolve_1020_, v_leanOpts_1021_, v_reconfigure_1022_, v_ws_1023_, v_next_1016_, v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_resolve_1031_, lean_object* v_leanOpts_1032_, lean_object* v_reconfigure_1033_, lean_object* v_ws_1034_, lean_object* v_i_1035_, lean_object* v_next_1036_){
_start:
{
uint8_t v_reconfigure_boxed_1037_; lean_object* v_res_1038_; 
v_reconfigure_boxed_1037_ = lean_unbox(v_reconfigure_1033_);
v_res_1038_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1028_, v_inst_1029_, v_inst_1030_, v_resolve_1031_, v_leanOpts_1032_, v_reconfigure_boxed_1037_, v_ws_1034_, v_i_1035_, v_next_1036_);
lean_dec(v_i_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* v_m_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_resolve_1043_, lean_object* v_leanOpts_1044_, uint8_t v_reconfigure_1045_, lean_object* v_ws_1046_, lean_object* v_i_1047_, lean_object* v_i__lt_1048_, lean_object* v_next_1049_, lean_object* v_lt__next_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1040_, v_inst_1041_, v_inst_1042_, v_resolve_1043_, v_leanOpts_1044_, v_reconfigure_1045_, v_ws_1046_, v_i_1047_, v_next_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object* v_m_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_resolve_1056_, lean_object* v_leanOpts_1057_, lean_object* v_reconfigure_1058_, lean_object* v_ws_1059_, lean_object* v_i_1060_, lean_object* v_i__lt_1061_, lean_object* v_next_1062_, lean_object* v_lt__next_1063_){
_start:
{
uint8_t v_reconfigure_boxed_1064_; lean_object* v_res_1065_; 
v_reconfigure_boxed_1064_ = lean_unbox(v_reconfigure_1058_);
v_res_1065_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(v_m_1052_, v_inst_1053_, v_inst_1054_, v_inst_1055_, v_resolve_1056_, v_leanOpts_1057_, v_reconfigure_boxed_1064_, v_ws_1059_, v_i_1060_, v_i__lt_1061_, v_next_1062_, v_lt__next_1063_);
lean_dec(v_i_1060_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___redArg(lean_object* v_x_1066_, lean_object* v_h__1_1067_, lean_object* v_h__2_1068_){
_start:
{
if (lean_obj_tag(v_x_1066_) == 1)
{
lean_object* v_val_1069_; lean_object* v___x_1070_; 
lean_dec(v_h__2_1068_);
v_val_1069_ = lean_ctor_get(v_x_1066_, 0);
lean_inc(v_val_1069_);
lean_dec_ref_known(v_x_1066_, 1);
v___x_1070_ = lean_apply_1(v_h__1_1067_, v_val_1069_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; 
lean_dec(v_h__1_1067_);
v___x_1071_ = lean_apply_2(v_h__2_1068_, v_x_1066_, lean_box(0));
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(lean_object* v_ws_1072_, lean_object* v_s_1073_, lean_object* v_motive_1074_, lean_object* v_x_1075_, lean_object* v_h__1_1076_, lean_object* v_h__2_1077_){
_start:
{
if (lean_obj_tag(v_x_1075_) == 1)
{
lean_object* v_val_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__2_1077_);
v_val_1078_ = lean_ctor_get(v_x_1075_, 0);
lean_inc(v_val_1078_);
lean_dec_ref_known(v_x_1075_, 1);
v___x_1079_ = lean_apply_1(v_h__1_1076_, v_val_1078_);
return v___x_1079_;
}
else
{
lean_object* v___x_1080_; 
lean_dec(v_h__1_1076_);
v___x_1080_ = lean_apply_2(v_h__2_1077_, v_x_1075_, lean_box(0));
return v___x_1080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___boxed(lean_object* v_ws_1081_, lean_object* v_s_1082_, lean_object* v_motive_1083_, lean_object* v_x_1084_, lean_object* v_h__1_1085_, lean_object* v_h__2_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(v_ws_1081_, v_s_1082_, v_motive_1083_, v_x_1084_, v_h__1_1085_, v_h__2_1086_);
lean_dec_ref(v_s_1082_);
lean_dec_ref(v_ws_1081_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___redArg(lean_object* v_x_1088_, lean_object* v_h__1_1089_){
_start:
{
lean_object* v_ws_1090_; lean_object* v_depIdxs_1091_; lean_object* v___x_1092_; 
v_ws_1090_ = lean_ctor_get(v_x_1088_, 0);
lean_inc_ref(v_ws_1090_);
v_depIdxs_1091_ = lean_ctor_get(v_x_1088_, 1);
lean_inc_ref(v_depIdxs_1091_);
lean_dec_ref(v_x_1088_);
v___x_1092_ = lean_apply_4(v_h__1_1089_, v_ws_1090_, v_depIdxs_1091_, lean_box(0), lean_box(0));
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(lean_object* v_ws_1093_, lean_object* v_motive_1094_, lean_object* v_x_1095_, lean_object* v_h__1_1096_){
_start:
{
lean_object* v_ws_1097_; lean_object* v_depIdxs_1098_; lean_object* v___x_1099_; 
v_ws_1097_ = lean_ctor_get(v_x_1095_, 0);
lean_inc_ref(v_ws_1097_);
v_depIdxs_1098_ = lean_ctor_get(v_x_1095_, 1);
lean_inc_ref(v_depIdxs_1098_);
lean_dec_ref(v_x_1095_);
v___x_1099_ = lean_apply_4(v_h__1_1096_, v_ws_1097_, v_depIdxs_1098_, lean_box(0), lean_box(0));
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___boxed(lean_object* v_ws_1100_, lean_object* v_motive_1101_, lean_object* v_x_1102_, lean_object* v_h__1_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(v_ws_1100_, v_motive_1101_, v_x_1102_, v_h__1_1103_);
lean_dec_ref(v_ws_1100_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___redArg(lean_object* v_h__1_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_apply_1(v_h__1_1105_, lean_box(0));
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(lean_object* v_ws_1107_, lean_object* v_motive_1108_, lean_object* v_x_1109_, lean_object* v_h__1_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_apply_1(v_h__1_1110_, lean_box(0));
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___boxed(lean_object* v_ws_1112_, lean_object* v_motive_1113_, lean_object* v_x_1114_, lean_object* v_h__1_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(v_ws_1112_, v_motive_1113_, v_x_1114_, v_h__1_1115_);
lean_dec_ref(v_ws_1112_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_ws_1121_, lean_object* v_resolve_1122_, lean_object* v_root_1123_, lean_object* v_next_1124_, lean_object* v_leanOpts_1125_, uint8_t v_reconfigure_1126_){
_start:
{
lean_object* v_toApplicative_1127_; lean_object* v_toFunctor_1128_; lean_object* v_map_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_toApplicative_1127_ = lean_ctor_get(v_inst_1118_, 0);
v_toFunctor_1128_ = lean_ctor_get(v_toApplicative_1127_, 0);
v_map_1129_ = lean_ctor_get(v_toFunctor_1128_, 0);
lean_inc(v_map_1129_);
v___f_1130_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0));
v___x_1131_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1118_, v_inst_1119_, v_inst_1120_, v_resolve_1122_, v_leanOpts_1125_, v_reconfigure_1126_, v_ws_1121_, v_root_1123_, v_next_1124_);
v___x_1132_ = lean_apply_4(v_map_1129_, lean_box(0), lean_box(0), v___f_1130_, v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_ws_1136_, lean_object* v_resolve_1137_, lean_object* v_root_1138_, lean_object* v_next_1139_, lean_object* v_leanOpts_1140_, lean_object* v_reconfigure_1141_){
_start:
{
uint8_t v_reconfigure_boxed_1142_; lean_object* v_res_1143_; 
v_reconfigure_boxed_1142_ = lean_unbox(v_reconfigure_1141_);
v_res_1143_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(v_inst_1133_, v_inst_1134_, v_inst_1135_, v_ws_1136_, v_resolve_1137_, v_root_1138_, v_next_1139_, v_leanOpts_1140_, v_reconfigure_boxed_1142_);
lean_dec(v_root_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* v_m_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_ws_1148_, lean_object* v_resolve_1149_, lean_object* v_root_1150_, lean_object* v_root__lt_1151_, lean_object* v_next_1152_, lean_object* v_next__lt_1153_, lean_object* v_leanOpts_1154_, uint8_t v_reconfigure_1155_){
_start:
{
lean_object* v_toApplicative_1156_; lean_object* v_toFunctor_1157_; lean_object* v_map_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_toApplicative_1156_ = lean_ctor_get(v_inst_1145_, 0);
v_toFunctor_1157_ = lean_ctor_get(v_toApplicative_1156_, 0);
v_map_1158_ = lean_ctor_get(v_toFunctor_1157_, 0);
lean_inc(v_map_1158_);
v___f_1159_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0));
v___x_1160_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1145_, v_inst_1146_, v_inst_1147_, v_resolve_1149_, v_leanOpts_1154_, v_reconfigure_1155_, v_ws_1148_, v_root_1150_, v_next_1152_);
v___x_1161_ = lean_apply_4(v_map_1158_, lean_box(0), lean_box(0), v___f_1159_, v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object* v_m_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_ws_1166_, lean_object* v_resolve_1167_, lean_object* v_root_1168_, lean_object* v_root__lt_1169_, lean_object* v_next_1170_, lean_object* v_next__lt_1171_, lean_object* v_leanOpts_1172_, lean_object* v_reconfigure_1173_){
_start:
{
uint8_t v_reconfigure_boxed_1174_; lean_object* v_res_1175_; 
v_reconfigure_boxed_1174_ = lean_unbox(v_reconfigure_1173_);
v_res_1175_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(v_m_1162_, v_inst_1163_, v_inst_1164_, v_inst_1165_, v_ws_1166_, v_resolve_1167_, v_root_1168_, v_root__lt_1169_, v_next_1170_, v_next__lt_1171_, v_leanOpts_1172_, v_reconfigure_boxed_1174_);
lean_dec(v_root_1168_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object* v_x_1176_, lean_object* v_init_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_apply_1(v_x_1176_, v_init_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object* v_m_1179_, lean_object* v_00_u03b1_1180_, lean_object* v_x_1181_, lean_object* v_init_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_apply_1(v_x_1181_, v_init_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(lean_object* v_as_1184_, size_t v_i_1185_, size_t v_stop_1186_, lean_object* v_b_1187_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_usize_dec_eq(v_i_1185_, v_stop_1186_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v_name_1190_; lean_object* v___x_1191_; size_t v___x_1192_; size_t v___x_1193_; 
v___x_1189_ = lean_array_uget_borrowed(v_as_1184_, v_i_1185_);
v_name_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_name_1190_);
v___x_1191_ = l_Lean_NameSet_insert(v_b_1187_, v_name_1190_);
v___x_1192_ = ((size_t)1ULL);
v___x_1193_ = lean_usize_add(v_i_1185_, v___x_1192_);
v_i_1185_ = v___x_1193_;
v_b_1187_ = v___x_1191_;
goto _start;
}
else
{
return v_b_1187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2___boxed(lean_object* v_as_1195_, lean_object* v_i_1196_, lean_object* v_stop_1197_, lean_object* v_b_1198_){
_start:
{
size_t v_i_boxed_1199_; size_t v_stop_boxed_1200_; lean_object* v_res_1201_; 
v_i_boxed_1199_ = lean_unbox_usize(v_i_1196_);
lean_dec(v_i_1196_);
v_stop_boxed_1200_ = lean_unbox_usize(v_stop_1197_);
lean_dec(v_stop_1197_);
v_res_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_as_1195_, v_i_boxed_1199_, v_stop_boxed_1200_, v_b_1198_);
lean_dec_ref(v_as_1195_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(lean_object* v_as_1202_, size_t v_sz_1203_, size_t v_i_1204_, lean_object* v_b_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_usize_dec_lt(v_i_1204_, v_sz_1203_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v_b_1205_);
lean_ctor_set(v___x_1209_, 1, v___y_1206_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
else
{
lean_object* v_a_1211_; lean_object* v_name_1212_; lean_object* v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; 
v_a_1211_ = lean_array_uget_borrowed(v_as_1202_, v_i_1204_);
v_name_1212_ = lean_ctor_get(v_a_1211_, 0);
lean_inc(v_name_1212_);
v___x_1213_ = l_Lean_NameSet_insert(v_b_1205_, v_name_1212_);
v___x_1214_ = ((size_t)1ULL);
v___x_1215_ = lean_usize_add(v_i_1204_, v___x_1214_);
v_i_1204_ = v___x_1215_;
v_b_1205_ = v___x_1213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg___boxed(lean_object* v_as_1217_, lean_object* v_sz_1218_, lean_object* v_i_1219_, lean_object* v_b_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
size_t v_sz_boxed_1223_; size_t v_i_boxed_1224_; lean_object* v_res_1225_; 
v_sz_boxed_1223_ = lean_unbox_usize(v_sz_1218_);
lean_dec(v_sz_1218_);
v_i_boxed_1224_ = lean_unbox_usize(v_i_1219_);
lean_dec(v_i_1219_);
v_res_1225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1217_, v_sz_boxed_1223_, v_i_boxed_1224_, v_b_1220_, v___y_1221_);
lean_dec_ref(v_as_1217_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_fst_1228_, lean_object* v_init_1229_, lean_object* v_x_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
lean_object* v_k_1234_; lean_object* v_l_1235_; lean_object* v_r_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_k_1234_ = lean_ctor_get(v_x_1230_, 1);
lean_inc(v_k_1234_);
v_l_1235_ = lean_ctor_get(v_x_1230_, 3);
lean_inc(v_l_1235_);
v_r_1236_ = lean_ctor_get(v_x_1230_, 4);
lean_inc(v_r_1236_);
lean_dec_ref_known(v_x_1230_, 5);
v___x_1237_ = lean_box(0);
v___x_1238_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1228_, v_init_1229_, v_l_1235_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1257_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1257_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1257_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_snd_1243_; uint8_t v___x_1244_; 
v_snd_1243_ = lean_ctor_get(v_a_1239_, 1);
lean_inc(v_snd_1243_);
lean_dec(v_a_1239_);
v___x_1244_ = l_Lean_NameSet_contains(v_fst_1228_, v_k_1234_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
lean_dec(v_snd_1243_);
lean_dec(v_r_1236_);
v___x_1245_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__0));
v___x_1246_ = l_Lean_Name_toString(v_k_1234_, v___x_1244_);
v___x_1247_ = lean_string_append(v___x_1245_, v___x_1246_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__1));
v___x_1249_ = lean_string_append(v___x_1247_, v___x_1248_);
v___x_1250_ = 3;
v___x_1251_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*1, v___x_1250_);
lean_inc_ref(v___y_1232_);
v___x_1252_ = lean_apply_2(v___y_1232_, v___x_1251_, lean_box(0));
if (v_isShared_1242_ == 0)
{
lean_ctor_set_tag(v___x_1241_, 1);
lean_ctor_set(v___x_1241_, 0, v___x_1237_);
v___x_1254_ = v___x_1241_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1237_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
else
{
lean_del_object(v___x_1241_);
lean_dec(v_k_1234_);
v_init_1229_ = v___x_1237_;
v_x_1230_ = v_r_1236_;
v___y_1231_ = v_snd_1243_;
goto _start;
}
}
}
else
{
lean_dec(v_r_1236_);
lean_dec(v_k_1234_);
return v___x_1238_;
}
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_init_1229_);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___y_1231_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_fst_1261_, lean_object* v_init_1262_, lean_object* v_x_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1261_, v_init_1262_, v_x_1263_, v___y_1264_, v___y_1265_);
lean_dec_ref(v___y_1265_);
lean_dec(v_fst_1261_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(lean_object* v_toUpdate_1268_, lean_object* v_depConfigs_1269_, lean_object* v___x_1270_, lean_object* v_entries_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___y_1276_; 
if (lean_obj_tag(v_toUpdate_1268_) == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1318_ = l_Lean_NameSet_empty;
v___x_1319_ = lean_array_get_size(v_depConfigs_1269_);
v___x_1320_ = lean_nat_dec_lt(v___x_1270_, v___x_1319_);
if (v___x_1320_ == 0)
{
v___y_1276_ = v___x_1318_;
goto v___jp_1275_;
}
else
{
size_t v___x_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = lean_usize_of_nat(v___x_1319_);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_1269_, v___x_1321_, v___x_1322_, v___x_1318_);
v___y_1276_ = v___x_1323_;
goto v___jp_1275_;
}
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___y_1272_);
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
return v___x_1326_;
}
v___jp_1275_:
{
size_t v_sz_1277_; size_t v___x_1278_; lean_object* v___x_1279_; 
v_sz_1277_ = lean_array_size(v_entries_1271_);
v___x_1278_ = ((size_t)0ULL);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_entries_1271_, v_sz_1277_, v___x_1278_, v___y_1276_, v___y_1272_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v_fst_1281_; lean_object* v_snd_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v_fst_1281_ = lean_ctor_get(v_a_1280_, 0);
lean_inc(v_fst_1281_);
v_snd_1282_ = lean_ctor_get(v_a_1280_, 1);
lean_inc(v_snd_1282_);
lean_dec(v_a_1280_);
v___x_1283_ = lean_box(0);
v___x_1284_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1281_, v___x_1283_, v_toUpdate_1268_, v_snd_1282_, v___y_1273_);
lean_dec(v_fst_1281_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1301_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1301_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1301_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_snd_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1299_; 
v_snd_1289_ = lean_ctor_get(v_a_1285_, 1);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_a_1285_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v_a_1285_, 0);
lean_dec(v_unused_1300_);
v___x_1291_ = v_a_1285_;
v_isShared_1292_ = v_isSharedCheck_1299_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_snd_1289_);
lean_dec(v_a_1285_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1299_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1283_);
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_snd_1289_);
v___x_1294_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1296_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1294_);
v___x_1296_ = v___x_1287_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
v_a_1302_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1284_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1284_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec(v_toUpdate_1268_);
v_a_1310_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1279_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1279_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0___boxed(lean_object* v_toUpdate_1327_, lean_object* v_depConfigs_1328_, lean_object* v___x_1329_, lean_object* v_entries_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1327_, v_depConfigs_1328_, v___x_1329_, v_entries_1330_, v___y_1331_, v___y_1332_);
lean_dec_ref(v___y_1332_);
lean_dec_ref(v_entries_1330_);
lean_dec(v___x_1329_);
lean_dec_ref(v_depConfigs_1328_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(lean_object* v_as_1335_, size_t v_i_1336_, size_t v_stop_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_eq(v_i_1336_, v_stop_1337_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; 
v___x_1342_ = lean_array_uget_borrowed(v_as_1335_, v_i_1336_);
lean_inc_ref(v___y_1339_);
lean_inc(v___x_1342_);
v___x_1343_ = lean_apply_2(v___y_1339_, v___x_1342_, lean_box(0));
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = lean_usize_add(v_i_1336_, v___x_1344_);
v_i_1336_ = v___x_1345_;
v_b_1338_ = v___x_1343_;
goto _start;
}
else
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v_b_1338_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3___boxed(lean_object* v_as_1348_, lean_object* v_i_1349_, lean_object* v_stop_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
size_t v_i_boxed_1354_; size_t v_stop_boxed_1355_; lean_object* v_res_1356_; 
v_i_boxed_1354_ = lean_unbox_usize(v_i_1349_);
lean_dec(v_i_1349_);
v_stop_boxed_1355_ = lean_unbox_usize(v_stop_1350_);
lean_dec(v_stop_1350_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_as_1348_, v_i_boxed_1354_, v_stop_boxed_1355_, v_b_1351_, v___y_1352_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v_as_1348_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(lean_object* v_toUpdate_1357_, lean_object* v_as_1358_, size_t v_i_1359_, size_t v_stop_1360_, lean_object* v_b_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_fst_1365_; lean_object* v_snd_1366_; uint8_t v___x_1372_; 
v___x_1372_ = lean_usize_dec_eq(v_i_1359_, v_stop_1360_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; uint8_t v_inherited_1374_; 
v___x_1373_ = lean_array_uget_borrowed(v_as_1358_, v_i_1359_);
v_inherited_1374_ = lean_ctor_get_uint8(v___x_1373_, sizeof(void*)*5);
if (v_inherited_1374_ == 0)
{
lean_object* v_name_1375_; uint8_t v___x_1376_; 
v_name_1375_ = lean_ctor_get(v___x_1373_, 0);
v___x_1376_ = l_Lean_NameSet_contains(v_toUpdate_1357_, v_name_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_box(0);
lean_inc(v___x_1373_);
lean_inc(v_name_1375_);
v___x_1378_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1375_, v___x_1373_, v___y_1362_);
v_fst_1365_ = v___x_1377_;
v_snd_1366_ = v___x_1378_;
goto v___jp_1364_;
}
else
{
goto v___jp_1370_;
}
}
else
{
goto v___jp_1370_;
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_b_1361_);
lean_ctor_set(v___x_1379_, 1, v___y_1362_);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
v___jp_1364_:
{
size_t v___x_1367_; size_t v___x_1368_; 
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_add(v_i_1359_, v___x_1367_);
v_i_1359_ = v___x_1368_;
v_b_1361_ = v_fst_1365_;
v___y_1362_ = v_snd_1366_;
goto _start;
}
v___jp_1370_:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_box(0);
v_fst_1365_ = v___x_1371_;
v_snd_1366_ = v___y_1362_;
goto v___jp_1364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg___boxed(lean_object* v_toUpdate_1381_, lean_object* v_as_1382_, lean_object* v_i_1383_, lean_object* v_stop_1384_, lean_object* v_b_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
size_t v_i_boxed_1388_; size_t v_stop_boxed_1389_; lean_object* v_res_1390_; 
v_i_boxed_1388_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_stop_boxed_1389_ = lean_unbox_usize(v_stop_1384_);
lean_dec(v_stop_1384_);
v_res_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1381_, v_as_1382_, v_i_boxed_1388_, v_stop_boxed_1389_, v_b_1385_, v___y_1386_);
lean_dec_ref(v_as_1382_);
lean_dec(v_toUpdate_1381_);
return v_res_1390_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1398_ = lean_array_get_size(v___x_1397_);
return v___x_1398_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1399_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_nat_dec_lt(v___x_1400_, v___x_1399_);
return v___x_1401_;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7(void){
_start:
{
lean_object* v___x_1402_; size_t v___x_1403_; 
v___x_1402_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1403_ = lean_usize_of_nat(v___x_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* v_ws_1406_, lean_object* v_toUpdate_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___y_1412_; lean_object* v___y_1417_; lean_object* v_fst_1418_; lean_object* v_snd_1419_; lean_object* v_packages_1438_; lean_object* v___x_1439_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v_val_1444_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v_a_1463_; lean_object* v___x_1465_; lean_object* v_baseName_1466_; lean_object* v_dir_1467_; lean_object* v_config_1468_; lean_object* v_relManifestFile_1469_; lean_object* v_depConfigs_1470_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; uint8_t v_fst_1475_; lean_object* v_snd_1476_; lean_object* v_packagesDir_x3f_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; uint8_t v___x_1530_; lean_object* v_rootName_1531_; lean_object* v_fst_1533_; lean_object* v_snd_1534_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v_val_1601_; lean_object* v___x_1615_; 
v_packages_1438_ = lean_ctor_get(v_ws_1406_, 4);
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1465_ = lean_array_fget_borrowed(v_packages_1438_, v___x_1439_);
v_baseName_1466_ = lean_ctor_get(v___x_1465_, 1);
v_dir_1467_ = lean_ctor_get(v___x_1465_, 4);
v_config_1468_ = lean_ctor_get(v___x_1465_, 6);
v_relManifestFile_1469_ = lean_ctor_get(v___x_1465_, 9);
v_depConfigs_1470_ = lean_ctor_get(v___x_1465_, 12);
v___x_1530_ = 0;
lean_inc(v_baseName_1466_);
v_rootName_1531_ = l_Lean_Name_toString(v_baseName_1466_, v___x_1530_);
lean_inc_ref(v_relManifestFile_1469_);
lean_inc_ref(v_dir_1467_);
v___x_1598_ = l_Lake_joinRelative(v_dir_1467_, v_relManifestFile_1469_);
v___x_1599_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1615_ = l_Lake_Manifest_load(v___x_1598_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 1);
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
v_val_1601_ = v___x_1621_;
goto v___jp_1600_;
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
v_a_1624_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1615_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1615_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 0);
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
v_val_1601_ = v___x_1629_;
goto v___jp_1600_;
}
}
}
v___jp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v___y_1412_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
v___jp_1416_:
{
if (lean_obj_tag(v_fst_1418_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v_snd_1419_);
v_a_1420_ = lean_ctor_get(v_fst_1418_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_fst_1418_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1422_ = v_fst_1418_;
v_isShared_1423_ = v_isSharedCheck_1434_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v_fst_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1434_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1424_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_1425_ = lean_io_error_to_string(v_a_1420_);
v___x_1426_ = lean_string_append(v___x_1424_, v___x_1425_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = 3;
v___x_1428_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1428_, 0, v___x_1426_);
lean_ctor_set_uint8(v___x_1428_, sizeof(void*)*1, v___x_1427_);
lean_inc_ref(v___y_1417_);
v___x_1429_ = lean_apply_2(v___y_1417_, v___x_1428_, lean_box(0));
v___x_1430_ = lean_box(0);
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 1);
lean_ctor_set(v___x_1422_, 0, v___x_1430_);
v___x_1432_ = v___x_1422_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec_ref(v_fst_1418_);
v___x_1435_ = lean_box(0);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v_snd_1419_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
}
v___jp_1440_:
{
lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1445_ = lean_array_get_size(v___y_1442_);
v___x_1446_ = lean_nat_dec_lt(v___x_1439_, v___x_1445_);
if (v___x_1446_ == 0)
{
v___y_1417_ = v___y_1441_;
v_fst_1418_ = v_val_1444_;
v_snd_1419_ = v___y_1443_;
goto v___jp_1416_;
}
else
{
lean_object* v___x_1447_; size_t v___x_1448_; size_t v___x_1449_; lean_object* v___x_1450_; 
v___x_1447_ = lean_box(0);
v___x_1448_ = ((size_t)0ULL);
v___x_1449_ = lean_usize_of_nat(v___x_1445_);
v___x_1450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1442_, v___x_1448_, v___x_1449_, v___x_1447_, v___y_1441_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_dec_ref_known(v___x_1450_, 1);
v___y_1417_ = v___y_1441_;
v_fst_1418_ = v_val_1444_;
v_snd_1419_ = v___y_1443_;
goto v___jp_1416_;
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v_val_1444_);
lean_dec(v___y_1443_);
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
v___jp_1459_:
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_a_1463_);
v___y_1441_ = v___y_1460_;
v___y_1442_ = v___y_1461_;
v___y_1443_ = v___y_1462_;
v_val_1444_ = v___x_1464_;
goto v___jp_1440_;
}
v___jp_1471_:
{
lean_object* v_toWorkspaceConfig_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v_toWorkspaceConfig_1477_ = lean_ctor_get(v_config_1468_, 0);
v___x_1478_ = l_System_FilePath_normalize(v___y_1473_);
lean_inc_ref(v_toWorkspaceConfig_1477_);
v___x_1479_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1477_);
lean_inc_ref(v___x_1479_);
v___x_1480_ = l_System_FilePath_normalize(v___x_1479_);
v___x_1481_ = lean_string_dec_eq(v___x_1478_, v___x_1480_);
lean_dec_ref(v___x_1480_);
lean_dec_ref(v___x_1478_);
if (v___x_1481_ == 0)
{
if (v_fst_1475_ == 0)
{
lean_dec_ref(v___x_1479_);
lean_dec_ref(v___y_1474_);
v___y_1412_ = v_snd_1476_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1482_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_1483_ = lean_string_append(v___x_1482_, v___y_1474_);
v___x_1484_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_1485_ = lean_string_append(v___x_1483_, v___x_1484_);
lean_inc_ref(v_dir_1467_);
v___x_1486_ = l_Lake_joinRelative(v_dir_1467_, v___x_1479_);
v___x_1487_ = lean_string_append(v___x_1485_, v___x_1486_);
v___x_1488_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1489_ = lean_string_append(v___x_1487_, v___x_1488_);
v___x_1490_ = 1;
v___x_1491_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*1, v___x_1490_);
lean_inc_ref(v___y_1472_);
v___x_1492_ = lean_apply_2(v___y_1472_, v___x_1491_, lean_box(0));
v___x_1493_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_1486_);
v___x_1494_ = l_Lake_createParentDirs(v___x_1486_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v___x_1495_; 
lean_dec_ref_known(v___x_1494_, 1);
v___x_1495_ = lean_io_rename(v___y_1474_, v___x_1486_);
lean_dec_ref(v___x_1486_);
lean_dec_ref(v___y_1474_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 1);
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
v___y_1441_ = v___y_1472_;
v___y_1442_ = v___x_1493_;
v___y_1443_ = v_snd_1476_;
v_val_1444_ = v___x_1501_;
goto v___jp_1440_;
}
}
}
else
{
lean_object* v_a_1504_; 
v_a_1504_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1495_, 1);
v___y_1460_ = v___y_1472_;
v___y_1461_ = v___x_1493_;
v___y_1462_ = v_snd_1476_;
v_a_1463_ = v_a_1504_;
goto v___jp_1459_;
}
}
else
{
lean_object* v_a_1505_; 
lean_dec_ref(v___x_1486_);
lean_dec_ref(v___y_1474_);
v_a_1505_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1494_, 1);
v___y_1460_ = v___y_1472_;
v___y_1461_ = v___x_1493_;
v___y_1462_ = v_snd_1476_;
v_a_1463_ = v_a_1505_;
goto v___jp_1459_;
}
}
}
else
{
lean_dec_ref(v___x_1479_);
lean_dec_ref(v___y_1474_);
v___y_1412_ = v_snd_1476_;
goto v___jp_1411_;
}
}
v___jp_1506_:
{
if (lean_obj_tag(v_packagesDir_x3f_1507_) == 1)
{
lean_object* v_val_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; uint8_t v___x_1514_; 
v_val_1510_ = lean_ctor_get(v_packagesDir_x3f_1507_, 0);
lean_inc_n(v_val_1510_, 2);
lean_dec_ref_known(v_packagesDir_x3f_1507_, 1);
lean_inc_ref(v_dir_1467_);
v___x_1511_ = l_Lake_joinRelative(v_dir_1467_, v_val_1510_);
v___x_1512_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1513_ = l_System_FilePath_pathExists(v___x_1511_);
v___x_1514_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1514_ == 0)
{
v___y_1472_ = v___y_1509_;
v___y_1473_ = v_val_1510_;
v___y_1474_ = v___x_1511_;
v_fst_1475_ = v___x_1513_;
v_snd_1476_ = v___y_1508_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1515_; size_t v___x_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
v___x_1515_ = lean_box(0);
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1512_, v___x_1516_, v___x_1517_, v___x_1515_, v___y_1509_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_dec_ref_known(v___x_1518_, 1);
v___y_1472_ = v___y_1509_;
v___y_1473_ = v_val_1510_;
v___y_1474_ = v___x_1511_;
v_fst_1475_ = v___x_1513_;
v_snd_1476_ = v___y_1508_;
goto v___jp_1471_;
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v___x_1511_);
lean_dec(v_val_1510_);
lean_dec(v___y_1508_);
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_packagesDir_x3f_1507_);
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
lean_ctor_set(v___x_1528_, 1, v___y_1508_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
v___jp_1532_:
{
if (lean_obj_tag(v_fst_1533_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1582_; 
v_a_1535_ = lean_ctor_get(v_fst_1533_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_fst_1533_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1537_ = v_fst_1533_;
v_isShared_1538_ = v_isSharedCheck_1582_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v_fst_1533_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1582_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
if (lean_obj_tag(v_a_1535_) == 11)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec_ref_known(v_a_1535_, 2);
lean_del_object(v___x_1537_);
v___x_1539_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_1540_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1407_, v_depConfigs_1470_, v___x_1439_, v___x_1539_, v_snd_1534_, v_a_1409_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1562_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1562_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1562_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_snd_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1560_; 
v_snd_1545_ = lean_ctor_get(v_a_1541_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_a_1541_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_a_1541_, 0);
lean_dec(v_unused_1561_);
v___x_1547_ = v_a_1541_;
v_isShared_1548_ = v_isSharedCheck_1560_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_snd_1545_);
lean_dec(v_a_1541_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1560_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1549_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8));
v___x_1550_ = lean_string_append(v_rootName_1531_, v___x_1549_);
v___x_1551_ = 1;
v___x_1552_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*1, v___x_1551_);
lean_inc_ref(v_a_1409_);
v___x_1553_ = lean_apply_2(v_a_1409_, v___x_1552_, lean_box(0));
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1553_);
v___x_1555_ = v___x_1547_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_snd_1545_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1555_);
v___x_1557_ = v___x_1543_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_1531_);
return v___x_1540_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_1407_) == 0)
{
lean_object* v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_dec_ref_known(v_toUpdate_1407_, 5);
lean_dec(v_snd_1534_);
lean_dec_ref(v_rootName_1531_);
v___x_1563_ = lean_io_error_to_string(v_a_1535_);
v___x_1564_ = 3;
v___x_1565_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*1, v___x_1564_);
lean_inc_ref(v_a_1409_);
v___x_1566_ = lean_apply_2(v_a_1409_, v___x_1565_, lean_box(0));
v___x_1567_ = lean_box(0);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 1);
lean_ctor_set(v___x_1537_, 0, v___x_1567_);
v___x_1569_ = v___x_1537_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1571_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_1572_ = lean_string_append(v_rootName_1531_, v___x_1571_);
v___x_1573_ = lean_io_error_to_string(v_a_1535_);
v___x_1574_ = lean_string_append(v___x_1572_, v___x_1573_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = 2;
v___x_1576_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*1, v___x_1575_);
lean_inc_ref(v_a_1409_);
v___x_1577_ = lean_apply_2(v_a_1409_, v___x_1576_, lean_box(0));
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v_snd_1534_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1578_);
v___x_1580_ = v___x_1537_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v_packagesDir_x3f_1584_; lean_object* v_packages_1585_; lean_object* v___x_1586_; 
lean_dec_ref(v_rootName_1531_);
v_a_1583_ = lean_ctor_get(v_fst_1533_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v_fst_1533_, 1);
v_packagesDir_x3f_1584_ = lean_ctor_get(v_a_1583_, 2);
lean_inc(v_packagesDir_x3f_1584_);
v_packages_1585_ = lean_ctor_get(v_a_1583_, 3);
lean_inc_ref(v_packages_1585_);
lean_dec(v_a_1583_);
lean_inc(v_toUpdate_1407_);
v___x_1586_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1407_, v_depConfigs_1470_, v___x_1439_, v_packages_1585_, v_snd_1534_, v_a_1409_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
if (lean_obj_tag(v_toUpdate_1407_) == 0)
{
lean_object* v_snd_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_snd_1588_ = lean_ctor_get(v_a_1587_, 1);
lean_inc(v_snd_1588_);
lean_dec(v_a_1587_);
v___x_1589_ = lean_array_get_size(v_packages_1585_);
v___x_1590_ = lean_nat_dec_lt(v___x_1439_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_dec_ref_known(v_toUpdate_1407_, 5);
lean_dec_ref(v_packages_1585_);
v_packagesDir_x3f_1507_ = v_packagesDir_x3f_1584_;
v___y_1508_ = v_snd_1588_;
v___y_1509_ = v_a_1409_;
goto v___jp_1506_;
}
else
{
lean_object* v___x_1591_; size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1591_ = lean_box(0);
v___x_1592_ = ((size_t)0ULL);
v___x_1593_ = lean_usize_of_nat(v___x_1589_);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1407_, v_packages_1585_, v___x_1592_, v___x_1593_, v___x_1591_, v_snd_1588_);
lean_dec_ref(v_packages_1585_);
lean_dec_ref_known(v_toUpdate_1407_, 5);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v_snd_1596_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v_snd_1596_ = lean_ctor_get(v_a_1595_, 1);
lean_inc(v_snd_1596_);
lean_dec(v_a_1595_);
v_packagesDir_x3f_1507_ = v_packagesDir_x3f_1584_;
v___y_1508_ = v_snd_1596_;
v___y_1509_ = v_a_1409_;
goto v___jp_1506_;
}
else
{
lean_dec(v_packagesDir_x3f_1584_);
return v___x_1594_;
}
}
}
else
{
lean_object* v_snd_1597_; 
lean_dec_ref(v_packages_1585_);
v_snd_1597_ = lean_ctor_get(v_a_1587_, 1);
lean_inc(v_snd_1597_);
lean_dec(v_a_1587_);
v_packagesDir_x3f_1507_ = v_packagesDir_x3f_1584_;
v___y_1508_ = v_snd_1597_;
v___y_1509_ = v_a_1409_;
goto v___jp_1506_;
}
}
else
{
lean_dec_ref(v_packages_1585_);
lean_dec(v_packagesDir_x3f_1584_);
lean_dec(v_toUpdate_1407_);
return v___x_1586_;
}
}
}
v___jp_1600_:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1602_ == 0)
{
v_fst_1533_ = v_val_1601_;
v_snd_1534_ = v_a_1408_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1603_; size_t v___x_1604_; size_t v___x_1605_; lean_object* v___x_1606_; 
v___x_1603_ = lean_box(0);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_1606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1599_, v___x_1604_, v___x_1605_, v___x_1603_, v_a_1409_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_dec_ref_known(v___x_1606_, 1);
v_fst_1533_ = v_val_1601_;
v_snd_1534_ = v_a_1408_;
goto v___jp_1532_;
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v_val_1601_);
lean_dec_ref(v_rootName_1531_);
lean_dec(v_a_1408_);
lean_dec(v_toUpdate_1407_);
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_1632_, lean_object* v_toUpdate_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1632_, v_toUpdate_1633_, v_a_1634_, v_a_1635_);
lean_dec_ref(v_a_1635_);
lean_dec_ref(v_ws_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* v_as_1638_, size_t v_sz_1639_, size_t v_i_1640_, lean_object* v_b_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1638_, v_sz_1639_, v_i_1640_, v_b_1641_, v___y_1642_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* v_as_1646_, lean_object* v_sz_1647_, lean_object* v_i_1648_, lean_object* v_b_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
size_t v_sz_boxed_1653_; size_t v_i_boxed_1654_; lean_object* v_res_1655_; 
v_sz_boxed_1653_ = lean_unbox_usize(v_sz_1647_);
lean_dec(v_sz_1647_);
v_i_boxed_1654_ = lean_unbox_usize(v_i_1648_);
lean_dec(v_i_1648_);
v_res_1655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_1646_, v_sz_boxed_1653_, v_i_boxed_1654_, v_b_1649_, v___y_1650_, v___y_1651_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_as_1646_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(lean_object* v_toUpdate_1656_, lean_object* v_as_1657_, size_t v_i_1658_, size_t v_stop_1659_, lean_object* v_b_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1656_, v_as_1657_, v_i_1658_, v_stop_1659_, v_b_1660_, v___y_1661_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___boxed(lean_object* v_toUpdate_1665_, lean_object* v_as_1666_, lean_object* v_i_1667_, lean_object* v_stop_1668_, lean_object* v_b_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
size_t v_i_boxed_1673_; size_t v_stop_boxed_1674_; lean_object* v_res_1675_; 
v_i_boxed_1673_ = lean_unbox_usize(v_i_1667_);
lean_dec(v_i_1667_);
v_stop_boxed_1674_ = lean_unbox_usize(v_stop_1668_);
lean_dec(v_stop_1668_);
v_res_1675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(v_toUpdate_1665_, v_as_1666_, v_i_boxed_1673_, v_stop_boxed_1674_, v_b_1669_, v___y_1670_, v___y_1671_);
lean_dec_ref(v___y_1671_);
lean_dec_ref(v_as_1666_);
lean_dec(v_toUpdate_1665_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_dep_1676_, lean_object* v_as_1677_, size_t v_i_1678_, size_t v_stop_1679_, lean_object* v_b_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_fst_1684_; lean_object* v_snd_1685_; lean_object* v___y_1690_; lean_object* v_name_1691_; uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_eq(v_i_1678_, v_stop_1679_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v_name_1696_; lean_object* v_scope_1697_; lean_object* v_configFile_1698_; lean_object* v_manifestFile_x3f_1699_; lean_object* v_src_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1727_; 
v___x_1695_ = lean_array_uget(v_as_1677_, v_i_1678_);
v_name_1696_ = lean_ctor_get(v___x_1695_, 0);
v_scope_1697_ = lean_ctor_get(v___x_1695_, 1);
v_configFile_1698_ = lean_ctor_get(v___x_1695_, 2);
v_manifestFile_x3f_1699_ = lean_ctor_get(v___x_1695_, 3);
v_src_1700_ = lean_ctor_get(v___x_1695_, 4);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1702_ = v___x_1695_;
v_isShared_1703_ = v_isSharedCheck_1727_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_src_1700_);
lean_inc(v_manifestFile_x3f_1699_);
lean_inc(v_configFile_1698_);
lean_inc(v_scope_1697_);
lean_inc(v_name_1696_);
lean_dec(v___x_1695_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1727_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
uint8_t v___x_1704_; 
v___x_1704_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1696_, v___y_1681_);
if (v___x_1704_ == 0)
{
uint8_t v___x_1705_; 
v___x_1705_ = 1;
if (lean_obj_tag(v_src_1700_) == 0)
{
uint8_t v_copy_1706_; 
v_copy_1706_ = lean_ctor_get_uint8(v_src_1700_, sizeof(void*)*1);
if (v_copy_1706_ == 0)
{
lean_object* v_dir_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1719_; 
v_dir_1707_ = lean_ctor_get(v_src_1700_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_src_1700_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1709_ = v_src_1700_;
v_isShared_1710_ = v_isSharedCheck_1719_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_dir_1707_);
lean_dec(v_src_1700_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1719_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_relPkgDir_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v_relPkgDir_1711_ = lean_ctor_get(v_dep_1676_, 1);
lean_inc_ref(v_relPkgDir_1711_);
v___x_1712_ = l_Lake_joinRelative(v_relPkgDir_1711_, v_dir_1707_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1712_);
v___x_1714_ = v___x_1709_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*1, v_copy_1706_);
v___x_1714_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
lean_inc(v_name_1696_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 4, v___x_1714_);
v___x_1716_ = v___x_1702_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_name_1696_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_scope_1697_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_configFile_1698_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v_manifestFile_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*5, v___x_1705_);
v___y_1690_ = v___x_1716_;
v_name_1691_ = v_name_1696_;
goto v___jp_1689_;
}
}
}
}
else
{
lean_object* v___x_1721_; 
lean_inc(v_name_1696_);
if (v_isShared_1703_ == 0)
{
v___x_1721_ = v___x_1702_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_name_1696_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_scope_1697_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_configFile_1698_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_manifestFile_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_src_1700_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*5, v___x_1705_);
v___y_1690_ = v___x_1721_;
v_name_1691_ = v_name_1696_;
goto v___jp_1689_;
}
}
}
else
{
lean_object* v___x_1724_; 
lean_inc(v_name_1696_);
if (v_isShared_1703_ == 0)
{
v___x_1724_ = v___x_1702_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_name_1696_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_scope_1697_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_configFile_1698_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_manifestFile_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v_src_1700_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*5, v___x_1705_);
v___y_1690_ = v___x_1724_;
v_name_1691_ = v_name_1696_;
goto v___jp_1689_;
}
}
}
else
{
lean_object* v___x_1726_; 
lean_del_object(v___x_1702_);
lean_dec_ref(v_src_1700_);
lean_dec(v_manifestFile_x3f_1699_);
lean_dec_ref(v_configFile_1698_);
lean_dec_ref(v_scope_1697_);
lean_dec(v_name_1696_);
v___x_1726_ = lean_box(0);
v_fst_1684_ = v___x_1726_;
v_snd_1685_ = v___y_1681_;
goto v___jp_1683_;
}
}
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec_ref(v_dep_1676_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_b_1680_);
lean_ctor_set(v___x_1728_, 1, v___y_1681_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
v___jp_1683_:
{
size_t v___x_1686_; size_t v___x_1687_; 
v___x_1686_ = ((size_t)1ULL);
v___x_1687_ = lean_usize_add(v_i_1678_, v___x_1686_);
v_i_1678_ = v___x_1687_;
v_b_1680_ = v_fst_1684_;
v___y_1681_ = v_snd_1685_;
goto _start;
}
v___jp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_box(0);
v___x_1693_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1691_, v___y_1690_, v___y_1681_);
v_fst_1684_ = v___x_1692_;
v_snd_1685_ = v___x_1693_;
goto v___jp_1683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1730_, lean_object* v_as_1731_, lean_object* v_i_1732_, lean_object* v_stop_1733_, lean_object* v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
size_t v_i_boxed_1737_; size_t v_stop_boxed_1738_; lean_object* v_res_1739_; 
v_i_boxed_1737_ = lean_unbox_usize(v_i_1732_);
lean_dec(v_i_1732_);
v_stop_boxed_1738_ = lean_unbox_usize(v_stop_1733_);
lean_dec(v_stop_1733_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1730_, v_as_1731_, v_i_boxed_1737_, v_stop_boxed_1738_, v_b_1734_, v___y_1735_);
lean_dec_ref(v_as_1731_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_manifestEntry_1746_; lean_object* v_pkgDir_1747_; lean_object* v_name_1748_; lean_object* v_manifestFile_x3f_1749_; lean_object* v___y_1751_; lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v_val_1805_; lean_object* v___y_1821_; 
v_manifestEntry_1746_ = lean_ctor_get(v_dep_1742_, 4);
v_pkgDir_1747_ = lean_ctor_get(v_dep_1742_, 0);
v_name_1748_ = lean_ctor_get(v_manifestEntry_1746_, 0);
v_manifestFile_x3f_1749_ = lean_ctor_get(v_manifestEntry_1746_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1749_) == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1747_);
v___x_1842_ = l_Lake_joinRelative(v_pkgDir_1747_, v___x_1841_);
v___y_1821_ = v___x_1842_;
goto v___jp_1820_;
}
else
{
lean_object* v_val_1843_; lean_object* v___x_1844_; 
v_val_1843_ = lean_ctor_get(v_manifestFile_x3f_1749_, 0);
lean_inc(v_val_1843_);
lean_inc_ref(v_pkgDir_1747_);
v___x_1844_ = l_Lake_joinRelative(v_pkgDir_1747_, v_val_1843_);
v___y_1821_ = v___x_1844_;
goto v___jp_1820_;
}
v___jp_1750_:
{
if (lean_obj_tag(v_fst_1752_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1783_; 
lean_inc(v_name_1748_);
lean_dec_ref(v_dep_1742_);
v_a_1754_ = lean_ctor_get(v_fst_1752_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_fst_1752_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1756_ = v_fst_1752_;
v_isShared_1757_ = v_isSharedCheck_1783_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v_fst_1752_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1783_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
if (lean_obj_tag(v_a_1754_) == 11)
{
uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec_ref_known(v_a_1754_, 2);
v___x_1758_ = 0;
v___x_1759_ = l_Lean_Name_toString(v_name_1748_, v___x_1758_);
v___x_1760_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1761_ = lean_string_append(v___x_1759_, v___x_1760_);
v___x_1762_ = lean_string_append(v___x_1761_, v___y_1751_);
lean_dec_ref(v___y_1751_);
v___x_1763_ = 2;
v___x_1764_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1764_, 0, v___x_1762_);
lean_ctor_set_uint8(v___x_1764_, sizeof(void*)*1, v___x_1763_);
lean_inc_ref(v_a_1744_);
v___x_1765_ = lean_apply_2(v_a_1744_, v___x_1764_, lean_box(0));
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v_snd_1753_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1766_);
v___x_1768_ = v___x_1756_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
else
{
uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
lean_dec_ref(v___y_1751_);
v___x_1770_ = 0;
v___x_1771_ = l_Lean_Name_toString(v_name_1748_, v___x_1770_);
v___x_1772_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1773_ = lean_string_append(v___x_1771_, v___x_1772_);
v___x_1774_ = lean_io_error_to_string(v_a_1754_);
v___x_1775_ = lean_string_append(v___x_1773_, v___x_1774_);
lean_dec_ref(v___x_1774_);
v___x_1776_ = 2;
v___x_1777_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set_uint8(v___x_1777_, sizeof(void*)*1, v___x_1776_);
lean_inc_ref(v_a_1744_);
v___x_1778_ = lean_apply_2(v_a_1744_, v___x_1777_, lean_box(0));
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v_snd_1753_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1779_);
v___x_1781_ = v___x_1756_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v___y_1751_);
v_a_1784_ = lean_ctor_get(v_fst_1752_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_fst_1752_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1786_ = v_fst_1752_;
v_isShared_1787_ = v_isSharedCheck_1800_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v_fst_1752_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1800_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v_packages_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_packages_1788_ = lean_ctor_get(v_a_1784_, 3);
lean_inc_ref(v_packages_1788_);
lean_dec(v_a_1784_);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_array_get_size(v_packages_1788_);
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_nat_dec_lt(v___x_1789_, v___x_1790_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_dec_ref(v_packages_1788_);
lean_dec_ref(v_dep_1742_);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v_snd_1753_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1793_);
v___x_1795_ = v___x_1786_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
else
{
size_t v___x_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
lean_del_object(v___x_1786_);
v___x_1797_ = ((size_t)0ULL);
v___x_1798_ = lean_usize_of_nat(v___x_1790_);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1742_, v_packages_1788_, v___x_1797_, v___x_1798_, v___x_1791_, v_snd_1753_);
lean_dec_ref(v_packages_1788_);
return v___x_1799_;
}
}
}
}
v___jp_1801_:
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_array_get_size(v___y_1803_);
v___x_1807_ = lean_nat_dec_lt(v___y_1802_, v___x_1806_);
if (v___x_1807_ == 0)
{
v___y_1751_ = v___y_1804_;
v_fst_1752_ = v_val_1805_;
v_snd_1753_ = v_a_1743_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1808_; size_t v___x_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1808_ = lean_box(0);
v___x_1809_ = ((size_t)0ULL);
v___x_1810_ = lean_usize_of_nat(v___x_1806_);
v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1803_, v___x_1809_, v___x_1810_, v___x_1808_, v_a_1744_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_dec_ref_known(v___x_1811_, 1);
v___y_1751_ = v___y_1804_;
v_fst_1752_ = v_val_1805_;
v_snd_1753_ = v_a_1743_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref(v_val_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_a_1743_);
lean_dec_ref(v_dep_1742_);
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1821_);
v___x_1824_ = l_Lake_Manifest_load(v___y_1821_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 1);
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
v___y_1802_ = v___x_1822_;
v___y_1803_ = v___x_1823_;
v___y_1804_ = v___y_1821_;
v_val_1805_ = v___x_1830_;
goto v___jp_1801_;
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
v_a_1833_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1824_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1824_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 0);
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
v___y_1802_ = v___x_1822_;
v___y_1803_ = v___x_1823_;
v___y_1804_ = v___y_1821_;
v_val_1805_ = v___x_1838_;
goto v___jp_1801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1845_, v_a_1846_, v_a_1847_);
lean_dec_ref(v_a_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1850_, lean_object* v_as_1851_, size_t v_i_1852_, size_t v_stop_1853_, lean_object* v_b_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1850_, v_as_1851_, v_i_1852_, v_stop_1853_, v_b_1854_, v___y_1855_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1859_, lean_object* v_as_1860_, lean_object* v_i_1861_, lean_object* v_stop_1862_, lean_object* v_b_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
size_t v_i_boxed_1867_; size_t v_stop_boxed_1868_; lean_object* v_res_1869_; 
v_i_boxed_1867_ = lean_unbox_usize(v_i_1861_);
lean_dec(v_i_1861_);
v_stop_boxed_1868_ = lean_unbox_usize(v_stop_1862_);
lean_dec(v_stop_1862_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1859_, v_as_1860_, v_i_boxed_1867_, v_stop_boxed_1868_, v_b_1863_, v___y_1864_, v___y_1865_);
lean_dec_ref(v___y_1865_);
lean_dec_ref(v_as_1860_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1871_, lean_object* v_pkg_1872_, lean_object* v_dep_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
uint8_t v___y_1878_; lean_object* v___y_1879_; lean_object* v_name_1909_; lean_object* v___x_1910_; 
v_name_1909_ = lean_ctor_get(v_dep_1873_, 0);
v___x_1910_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1874_, v_name_1909_);
if (lean_obj_tag(v___x_1910_) == 1)
{
lean_object* v_val_1911_; lean_object* v_lakeEnv_1912_; lean_object* v_packages_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v_config_1916_; lean_object* v_dir_1917_; lean_object* v_toWorkspaceConfig_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec_ref(v_dep_1873_);
lean_dec_ref(v_pkg_1872_);
v_val_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_val_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v_lakeEnv_1912_ = lean_ctor_get(v_ws_1871_, 0);
lean_inc_ref(v_lakeEnv_1912_);
v_packages_1913_ = lean_ctor_get(v_ws_1871_, 4);
lean_inc_ref(v_packages_1913_);
lean_dec_ref(v_ws_1871_);
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_array_fget(v_packages_1913_, v___x_1914_);
lean_dec_ref(v_packages_1913_);
v_config_1916_ = lean_ctor_get(v___x_1915_, 6);
lean_inc_ref(v_config_1916_);
v_dir_1917_ = lean_ctor_get(v___x_1915_, 4);
lean_inc_ref(v_dir_1917_);
lean_dec(v___x_1915_);
v_toWorkspaceConfig_1918_ = lean_ctor_get(v_config_1916_, 0);
lean_inc_ref(v_toWorkspaceConfig_1918_);
lean_dec_ref(v_config_1916_);
v___x_1919_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1918_);
v___x_1920_ = l_Lake_PackageEntry_materialize(v_val_1911_, v_lakeEnv_1912_, v_dir_1917_, v___x_1919_, v_a_1875_);
lean_dec_ref(v_lakeEnv_1912_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1929_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_a_1921_);
lean_ctor_set(v___x_1925_, 1, v_a_1874_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_a_1874_);
v_a_1930_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1920_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1920_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_wsIdx_1938_; lean_object* v_relDir_1939_; uint8_t v___y_1941_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
lean_dec(v___x_1910_);
v_wsIdx_1938_ = lean_ctor_get(v_pkg_1872_, 0);
lean_inc(v_wsIdx_1938_);
v_relDir_1939_ = lean_ctor_get(v_pkg_1872_, 5);
lean_inc_ref(v_relDir_1939_);
lean_dec_ref(v_pkg_1872_);
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = lean_nat_dec_eq(v_wsIdx_1938_, v___x_1945_);
lean_dec(v_wsIdx_1938_);
if (v___x_1946_ == 0)
{
uint8_t v___x_1947_; 
v___x_1947_ = 1;
v___y_1941_ = v___x_1947_;
goto v___jp_1940_;
}
else
{
uint8_t v___x_1948_; 
v___x_1948_ = 0;
v___y_1941_ = v___x_1948_;
goto v___jp_1940_;
}
v___jp_1940_:
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1943_ = lean_string_dec_eq(v_relDir_1939_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lake_joinRelative(v_relDir_1939_, v___x_1942_);
v___y_1878_ = v___y_1941_;
v___y_1879_ = v___x_1944_;
goto v___jp_1877_;
}
else
{
v___y_1878_ = v___y_1941_;
v___y_1879_ = v_relDir_1939_;
goto v___jp_1877_;
}
}
}
v___jp_1877_:
{
lean_object* v_lakeEnv_1880_; lean_object* v_packages_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v_config_1884_; lean_object* v_dir_1885_; lean_object* v_toWorkspaceConfig_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_lakeEnv_1880_ = lean_ctor_get(v_ws_1871_, 0);
lean_inc_ref(v_lakeEnv_1880_);
v_packages_1881_ = lean_ctor_get(v_ws_1871_, 4);
lean_inc_ref(v_packages_1881_);
lean_dec_ref(v_ws_1871_);
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = lean_array_fget(v_packages_1881_, v___x_1882_);
lean_dec_ref(v_packages_1881_);
v_config_1884_ = lean_ctor_get(v___x_1883_, 6);
lean_inc_ref(v_config_1884_);
v_dir_1885_ = lean_ctor_get(v___x_1883_, 4);
lean_inc_ref(v_dir_1885_);
lean_dec(v___x_1883_);
v_toWorkspaceConfig_1886_ = lean_ctor_get(v_config_1884_, 0);
lean_inc_ref(v_toWorkspaceConfig_1886_);
lean_dec_ref(v_config_1884_);
v___x_1887_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1886_);
v___x_1888_ = l_Lake_Dependency_materialize(v_dep_1873_, v___y_1878_, v_lakeEnv_1880_, v_dir_1885_, v___x_1887_, v___y_1879_, v_a_1875_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1900_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_manifestEntry_1893_; lean_object* v_name_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v_manifestEntry_1893_ = lean_ctor_get(v_a_1889_, 4);
v_name_1894_ = lean_ctor_get(v_manifestEntry_1893_, 0);
lean_inc_ref(v_manifestEntry_1893_);
lean_inc(v_name_1894_);
v___x_1895_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1894_, v_manifestEntry_1893_, v_a_1874_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1889_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1896_);
v___x_1898_ = v___x_1891_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_a_1874_);
v_a_1901_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1888_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1888_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_1949_, lean_object* v_pkg_1950_, lean_object* v_dep_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1949_, v_pkg_1950_, v_dep_1951_, v_a_1952_, v_a_1953_);
lean_dec_ref(v_a_1953_);
return v_res_1955_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_1956_; 
v___x_1956_ = 4;
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_1957_, lean_object* v_tc_x3f_1958_, uint8_t v_fixed_1959_, lean_object* v_self_1960_){
_start:
{
lean_object* v_clashes_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
v_clashes_1961_ = lean_ctor_get(v_self_1960_, 2);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_self_1960_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; lean_object* v_unused_1970_; 
v_unused_1969_ = lean_ctor_get(v_self_1960_, 1);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v_self_1960_, 0);
lean_dec(v_unused_1970_);
v___x_1963_ = v_self_1960_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_clashes_1961_);
lean_dec(v_self_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v_tc_x3f_1958_);
lean_ctor_set(v___x_1963_, 0, v_src_1957_);
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_src_1957_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_tc_x3f_1958_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_clashes_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_ctor_set_uint8(v___x_1966_, sizeof(void*)*3, v_fixed_1959_);
return v___x_1966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_1971_, lean_object* v_tc_x3f_1972_, lean_object* v_fixed_1973_, lean_object* v_self_1974_){
_start:
{
uint8_t v_fixed_boxed_1975_; lean_object* v_res_1976_; 
v_fixed_boxed_1975_ = lean_unbox(v_fixed_1973_);
v_res_1976_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_1971_, v_tc_x3f_1972_, v_fixed_boxed_1975_, v_self_1974_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_1977_, lean_object* v_ver_1978_, uint8_t v_fixed_1979_, lean_object* v_self_1980_){
_start:
{
lean_object* v_src_1981_; lean_object* v_tc_x3f_1982_; lean_object* v_clashes_1983_; uint8_t v_fixed_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1993_; 
v_src_1981_ = lean_ctor_get(v_self_1980_, 0);
v_tc_x3f_1982_ = lean_ctor_get(v_self_1980_, 1);
v_clashes_1983_ = lean_ctor_get(v_self_1980_, 2);
v_fixed_1984_ = lean_ctor_get_uint8(v_self_1980_, sizeof(void*)*3);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_self_1980_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1986_ = v_self_1980_;
v_isShared_1987_ = v_isSharedCheck_1993_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_clashes_1983_);
lean_inc(v_tc_x3f_1982_);
lean_inc(v_src_1981_);
lean_dec(v_self_1980_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1993_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1988_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1988_, 0, v_src_1977_);
lean_ctor_set(v___x_1988_, 1, v_ver_1978_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*2, v_fixed_1979_);
v___x_1989_ = lean_array_push(v_clashes_1983_, v___x_1988_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 2, v___x_1989_);
v___x_1991_ = v___x_1986_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_src_1981_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_tc_x3f_1982_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v___x_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*3, v_fixed_1984_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_1994_, lean_object* v_ver_1995_, lean_object* v_fixed_1996_, lean_object* v_self_1997_){
_start:
{
uint8_t v_fixed_boxed_1998_; lean_object* v_res_1999_; 
v_fixed_boxed_1998_ = lean_unbox(v_fixed_1996_);
v_res_1999_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_1994_, v_ver_1995_, v_fixed_boxed_1998_, v_self_1997_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v___x_2004_, lean_object* v_as_2005_, size_t v_i_2006_, size_t v_stop_2007_, lean_object* v_b_2008_){
_start:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_usize_dec_eq(v_i_2006_, v_stop_2007_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v_src_2011_; lean_object* v_ver_2012_; uint8_t v_fixed_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2030_; 
v___x_2010_ = lean_array_uget_borrowed(v_as_2005_, v_i_2006_);
v_src_2011_ = lean_ctor_get(v___x_2010_, 0);
v_ver_2012_ = lean_ctor_get(v___x_2010_, 1);
v_fixed_2013_ = lean_ctor_get_uint8(v___x_2010_, sizeof(void*)*2);
v___x_2014_ = lean_unsigned_to_nat(0u);
v___x_2015_ = lean_nat_dec_lt(v___x_2014_, v___x_2004_);
if (v_fixed_2013_ == 0)
{
lean_object* v___x_2034_; 
v___x_2034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2030_ = v___x_2034_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2035_; 
v___x_2035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2030_ = v___x_2035_;
goto v___jp_2029_;
}
v___jp_2016_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; 
v___x_2020_ = lean_string_append(v___y_2018_, v___y_2019_);
lean_dec_ref(v___y_2019_);
v___x_2021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2022_ = lean_string_append(v___x_2020_, v___x_2021_);
lean_inc(v_src_2011_);
v___x_2023_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2011_, v___x_2015_);
v___x_2024_ = lean_string_append(v___x_2022_, v___x_2023_);
lean_dec_ref(v___x_2023_);
v___x_2025_ = lean_string_append(v___x_2024_, v___y_2017_);
v___x_2026_ = ((size_t)1ULL);
v___x_2027_ = lean_usize_add(v_i_2006_, v___x_2026_);
v_i_2006_ = v___x_2027_;
v_b_2008_ = v___x_2025_;
goto _start;
}
v___jp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v_toString_2033_; 
v___x_2031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2032_ = lean_string_append(v_b_2008_, v___x_2031_);
v_toString_2033_ = lean_ctor_get(v_ver_2012_, 0);
lean_inc_ref(v_toString_2033_);
v___y_2017_ = v___y_2030_;
v___y_2018_ = v___x_2032_;
v___y_2019_ = v_toString_2033_;
goto v___jp_2016_;
}
}
else
{
return v_b_2008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v___x_2036_, lean_object* v_as_2037_, lean_object* v_i_2038_, lean_object* v_stop_2039_, lean_object* v_b_2040_){
_start:
{
size_t v_i_boxed_2041_; size_t v_stop_boxed_2042_; lean_object* v_res_2043_; 
v_i_boxed_2041_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_stop_boxed_2042_ = lean_unbox_usize(v_stop_2039_);
lean_dec(v_stop_2039_);
v_res_2043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2036_, v_as_2037_, v_i_boxed_2041_, v_stop_boxed_2042_, v_b_2040_);
lean_dec_ref(v_as_2037_);
lean_dec(v___x_2036_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v___x_2044_, lean_object* v_as_2045_, size_t v_i_2046_, size_t v_stop_2047_, lean_object* v_b_2048_){
_start:
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_eq(v_i_2046_, v_stop_2047_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; lean_object* v_src_2051_; lean_object* v_ver_2052_; uint8_t v_fixed_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2070_; 
v___x_2050_ = lean_array_uget_borrowed(v_as_2045_, v_i_2046_);
v_src_2051_ = lean_ctor_get(v___x_2050_, 0);
v_ver_2052_ = lean_ctor_get(v___x_2050_, 1);
v_fixed_2053_ = lean_ctor_get_uint8(v___x_2050_, sizeof(void*)*2);
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = lean_nat_dec_lt(v___x_2054_, v___x_2044_);
if (v_fixed_2053_ == 0)
{
lean_object* v___x_2074_; 
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2070_ = v___x_2074_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2075_; 
v___x_2075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2070_ = v___x_2075_;
goto v___jp_2069_;
}
v___jp_2056_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; size_t v___x_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
v___x_2060_ = lean_string_append(v___y_2058_, v___y_2059_);
lean_dec_ref(v___y_2059_);
v___x_2061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2062_ = lean_string_append(v___x_2060_, v___x_2061_);
lean_inc(v_src_2051_);
v___x_2063_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2051_, v___x_2055_);
v___x_2064_ = lean_string_append(v___x_2062_, v___x_2063_);
lean_dec_ref(v___x_2063_);
v___x_2065_ = lean_string_append(v___x_2064_, v___y_2057_);
v___x_2066_ = ((size_t)1ULL);
v___x_2067_ = lean_usize_add(v_i_2046_, v___x_2066_);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2044_, v_as_2045_, v___x_2067_, v_stop_2047_, v___x_2065_);
return v___x_2068_;
}
v___jp_2069_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_toString_2073_; 
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2072_ = lean_string_append(v_b_2048_, v___x_2071_);
v_toString_2073_ = lean_ctor_get(v_ver_2052_, 0);
lean_inc_ref(v_toString_2073_);
v___y_2057_ = v___y_2070_;
v___y_2058_ = v___x_2072_;
v___y_2059_ = v_toString_2073_;
goto v___jp_2056_;
}
}
else
{
return v_b_2048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v___x_2076_, lean_object* v_as_2077_, lean_object* v_i_2078_, lean_object* v_stop_2079_, lean_object* v_b_2080_){
_start:
{
size_t v_i_boxed_2081_; size_t v_stop_boxed_2082_; lean_object* v_res_2083_; 
v_i_boxed_2081_ = lean_unbox_usize(v_i_2078_);
lean_dec(v_i_2078_);
v_stop_boxed_2082_ = lean_unbox_usize(v_stop_2079_);
lean_dec(v_stop_2079_);
v_res_2083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___x_2076_, v_as_2077_, v_i_boxed_2081_, v_stop_boxed_2082_, v_b_2080_);
lean_dec_ref(v_as_2077_);
lean_dec(v___x_2076_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_2084_, lean_object* v_as_2085_, size_t v_i_2086_, size_t v_stop_2087_, lean_object* v_b_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_a_2092_; uint8_t v___x_2096_; 
v___x_2096_ = lean_usize_dec_eq(v_i_2086_, v_stop_2087_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v_relPkgDir_2098_; lean_object* v_manifestEntry_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2097_ = lean_array_uget_borrowed(v_as_2085_, v_i_2086_);
v_relPkgDir_2098_ = lean_ctor_get(v___x_2097_, 1);
v_manifestEntry_2099_ = lean_ctor_get(v___x_2097_, 4);
lean_inc_ref(v_relPkgDir_2098_);
lean_inc_ref(v___x_2084_);
v___x_2100_ = l_Lake_joinRelative(v___x_2084_, v_relPkgDir_2098_);
v___x_2101_ = l_Lake_toolchainFileName;
v___x_2102_ = l_System_FilePath_join(v___x_2100_, v___x_2101_);
v___x_2103_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2102_);
lean_dec_ref(v___x_2102_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
if (lean_obj_tag(v_a_2104_) == 1)
{
lean_object* v_tc_x3f_2105_; 
v_tc_x3f_2105_ = lean_ctor_get(v_b_2088_, 1);
if (lean_obj_tag(v_tc_x3f_2105_) == 1)
{
lean_object* v_val_2106_; lean_object* v_src_2107_; lean_object* v_clashes_2108_; uint8_t v_fixed_2109_; lean_object* v_val_2110_; uint8_t v___x_2111_; 
v_val_2106_ = lean_ctor_get(v_a_2104_, 0);
v_src_2107_ = lean_ctor_get(v_b_2088_, 0);
v_clashes_2108_ = lean_ctor_get(v_b_2088_, 2);
v_fixed_2109_ = lean_ctor_get_uint8(v_b_2088_, sizeof(void*)*3);
v_val_2110_ = lean_ctor_get(v_tc_x3f_2105_, 0);
v___x_2111_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2097_);
if (v___x_2111_ == 0)
{
uint8_t v___x_2117_; 
v___x_2117_ = l_Lake_ToolchainVer_ble(v_val_2106_, v_val_2110_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2126_; 
lean_inc_ref(v_clashes_2108_);
lean_inc(v_src_2107_);
lean_inc_ref(v_tc_x3f_2105_);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_b_2088_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; lean_object* v_unused_2128_; lean_object* v_unused_2129_; 
v_unused_2127_ = lean_ctor_get(v_b_2088_, 2);
lean_dec(v_unused_2127_);
v_unused_2128_ = lean_ctor_get(v_b_2088_, 1);
lean_dec(v_unused_2128_);
v_unused_2129_ = lean_ctor_get(v_b_2088_, 0);
lean_dec(v_unused_2129_);
v___x_2119_ = v_b_2088_;
v_isShared_2120_ = v_isSharedCheck_2126_;
goto v_resetjp_2118_;
}
else
{
lean_dec(v_b_2088_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2126_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
if (v_fixed_2109_ == 0)
{
uint8_t v___x_2121_; 
v___x_2121_ = l_Lake_ToolchainVer_blt(v_val_2110_, v_val_2106_);
if (v___x_2121_ == 0)
{
lean_inc(v_val_2106_);
lean_del_object(v___x_2119_);
lean_dec_ref_known(v_a_2104_, 1);
goto v___jp_2112_;
}
else
{
lean_object* v_name_2122_; lean_object* v___x_2124_; 
lean_dec(v_src_2107_);
lean_dec_ref_known(v_tc_x3f_2105_, 1);
v_name_2122_ = lean_ctor_get(v_manifestEntry_2099_, 0);
lean_inc(v_name_2122_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v_a_2104_);
lean_ctor_set(v___x_2119_, 0, v_name_2122_);
v___x_2124_ = v___x_2119_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_name_2122_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_a_2104_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_clashes_2108_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*3, v___x_2111_);
v_a_2092_ = v___x_2124_;
goto v___jp_2091_;
}
}
}
else
{
lean_inc(v_val_2106_);
lean_del_object(v___x_2119_);
lean_dec_ref_known(v_a_2104_, 1);
goto v___jp_2112_;
}
}
}
else
{
lean_dec_ref_known(v_a_2104_, 1);
v_a_2092_ = v_b_2088_;
goto v___jp_2091_;
}
}
else
{
if (v_fixed_2109_ == 0)
{
lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2144_; 
lean_inc_ref(v_clashes_2108_);
lean_inc(v_src_2107_);
lean_inc_ref(v_tc_x3f_2105_);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_b_2088_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; lean_object* v_unused_2146_; lean_object* v_unused_2147_; 
v_unused_2145_ = lean_ctor_get(v_b_2088_, 2);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_b_2088_, 1);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_b_2088_, 0);
lean_dec(v_unused_2147_);
v___x_2131_ = v_b_2088_;
v_isShared_2132_ = v_isSharedCheck_2144_;
goto v_resetjp_2130_;
}
else
{
lean_dec(v_b_2088_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2144_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
uint8_t v___x_2133_; 
v___x_2133_ = l_Lake_ToolchainVer_ble(v_val_2110_, v_val_2106_);
if (v___x_2133_ == 0)
{
lean_object* v_name_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
lean_inc(v_val_2106_);
lean_dec_ref_known(v_a_2104_, 1);
v_name_2134_ = lean_ctor_get(v_manifestEntry_2099_, 0);
lean_inc(v_name_2134_);
v___x_2135_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2135_, 0, v_name_2134_);
lean_ctor_set(v___x_2135_, 1, v_val_2106_);
lean_ctor_set_uint8(v___x_2135_, sizeof(void*)*2, v___x_2111_);
v___x_2136_ = lean_array_push(v_clashes_2108_, v___x_2135_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 2, v___x_2136_);
v___x_2138_ = v___x_2131_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_src_2107_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_tc_x3f_2105_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v___x_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2139_, sizeof(void*)*3, v_fixed_2109_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
v_a_2092_ = v___x_2138_;
goto v___jp_2091_;
}
}
else
{
lean_object* v_name_2140_; lean_object* v___x_2142_; 
lean_dec(v_src_2107_);
lean_dec_ref_known(v_tc_x3f_2105_, 1);
v_name_2140_ = lean_ctor_get(v_manifestEntry_2099_, 0);
lean_inc(v_name_2140_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 1, v_a_2104_);
lean_ctor_set(v___x_2131_, 0, v_name_2140_);
v___x_2142_ = v___x_2131_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_name_2140_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_a_2104_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_clashes_2108_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_ctor_set_uint8(v___x_2142_, sizeof(void*)*3, v___x_2111_);
v_a_2092_ = v___x_2142_;
goto v___jp_2091_;
}
}
}
}
else
{
uint8_t v___x_2148_; 
lean_inc_n(v_val_2106_, 2);
lean_dec_ref_known(v_a_2104_, 1);
lean_inc(v_val_2110_);
v___x_2148_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2110_, v_val_2106_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2158_; 
lean_inc_ref(v_clashes_2108_);
lean_inc(v_src_2107_);
lean_inc_ref(v_tc_x3f_2105_);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_b_2088_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2159_ = lean_ctor_get(v_b_2088_, 2);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_b_2088_, 1);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_b_2088_, 0);
lean_dec(v_unused_2161_);
v___x_2150_ = v_b_2088_;
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
else
{
lean_dec(v_b_2088_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v_name_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
v_name_2152_ = lean_ctor_get(v_manifestEntry_2099_, 0);
lean_inc(v_name_2152_);
v___x_2153_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2153_, 0, v_name_2152_);
lean_ctor_set(v___x_2153_, 1, v_val_2106_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*2, v___x_2111_);
v___x_2154_ = lean_array_push(v_clashes_2108_, v___x_2153_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 2, v___x_2154_);
v___x_2156_ = v___x_2150_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_src_2107_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_tc_x3f_2105_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v___x_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*3, v_fixed_2109_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
v_a_2092_ = v___x_2156_;
goto v___jp_2091_;
}
}
}
else
{
lean_dec(v_val_2106_);
v_a_2092_ = v_b_2088_;
goto v___jp_2091_;
}
}
}
v___jp_2112_:
{
lean_object* v_name_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_name_2113_ = lean_ctor_get(v_manifestEntry_2099_, 0);
lean_inc(v_name_2113_);
v___x_2114_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2114_, 0, v_name_2113_);
lean_ctor_set(v___x_2114_, 1, v_val_2106_);
lean_ctor_set_uint8(v___x_2114_, sizeof(void*)*2, v___x_2111_);
v___x_2115_ = lean_array_push(v_clashes_2108_, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2116_, 0, v_src_2107_);
lean_ctor_set(v___x_2116_, 1, v_tc_x3f_2105_);
lean_ctor_set(v___x_2116_, 2, v___x_2115_);
lean_ctor_set_uint8(v___x_2116_, sizeof(void*)*3, v_fixed_2109_);
v_a_2092_ = v___x_2116_;
goto v___jp_2091_;
}
}
else
{
lean_object* v_clashes_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2171_; 
v_clashes_2162_ = lean_ctor_get(v_b_2088_, 2);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_b_2088_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; lean_object* v_unused_2173_; 
v_unused_2172_ = lean_ctor_get(v_b_2088_, 1);
lean_dec(v_unused_2172_);
v_unused_2173_ = lean_ctor_get(v_b_2088_, 0);
lean_dec(v_unused_2173_);
v___x_2164_ = v_b_2088_;
v_isShared_2165_ = v_isSharedCheck_2171_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_clashes_2162_);
lean_dec(v_b_2088_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2171_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v_name_2166_; uint8_t v___x_2167_; lean_object* v___x_2169_; 
v_name_2166_ = lean_ctor_get(v_manifestEntry_2099_, 0);
v___x_2167_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2097_);
lean_inc(v_name_2166_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v_a_2104_);
lean_ctor_set(v___x_2164_, 0, v_name_2166_);
v___x_2169_ = v___x_2164_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_name_2166_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_a_2104_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_clashes_2162_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*3, v___x_2167_);
v_a_2092_ = v___x_2169_;
goto v___jp_2091_;
}
}
}
}
else
{
lean_dec(v_a_2104_);
v_a_2092_ = v_b_2088_;
goto v___jp_2091_;
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v_b_2088_);
lean_dec_ref(v___x_2084_);
v_a_2174_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2176_ = v___x_2103_;
v_isShared_2177_ = v_isSharedCheck_2186_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2103_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2186_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2178_ = lean_io_error_to_string(v_a_2174_);
v___x_2179_ = 3;
v___x_2180_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set_uint8(v___x_2180_, sizeof(void*)*1, v___x_2179_);
lean_inc_ref(v___y_2089_);
v___x_2181_ = lean_apply_2(v___y_2089_, v___x_2180_, lean_box(0));
v___x_2182_ = lean_box(0);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2182_);
v___x_2184_ = v___x_2176_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
else
{
lean_object* v___x_2187_; 
lean_dec_ref(v___x_2084_);
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_b_2088_);
return v___x_2187_;
}
v___jp_2091_:
{
size_t v___x_2093_; size_t v___x_2094_; 
v___x_2093_ = ((size_t)1ULL);
v___x_2094_ = lean_usize_add(v_i_2086_, v___x_2093_);
v_i_2086_ = v___x_2094_;
v_b_2088_ = v_a_2092_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2188_, lean_object* v_as_2189_, lean_object* v_i_2190_, lean_object* v_stop_2191_, lean_object* v_b_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
size_t v_i_boxed_2195_; size_t v_stop_boxed_2196_; lean_object* v_res_2197_; 
v_i_boxed_2195_ = lean_unbox_usize(v_i_2190_);
lean_dec(v_i_2190_);
v_stop_boxed_2196_ = lean_unbox_usize(v_stop_2191_);
lean_dec(v_stop_2191_);
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2188_, v_as_2189_, v_i_boxed_2195_, v_stop_boxed_2196_, v_b_2192_, v___y_2193_);
lean_dec_ref(v___y_2193_);
lean_dec_ref(v_as_2189_);
return v_res_2197_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2208_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2209_ = lean_unsigned_to_nat(4u);
v___x_2210_ = lean_mk_empty_array_with_capacity(v___x_2209_);
v___x_2211_ = lean_array_push(v___x_2210_, v___x_2208_);
return v___x_2211_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2213_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2214_ = lean_array_push(v___x_2213_, v___x_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2235_, lean_object* v_rootDeps_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___y_2240_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2253_; lean_object* v___y_2254_; uint8_t v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; uint8_t v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v_lakeEnv_2275_; lean_object* v_lakeArgs_x3f_2276_; lean_object* v_packages_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v_baseName_2280_; lean_object* v_dir_2281_; lean_object* v_config_2282_; lean_object* v___x_2283_; lean_object* v_rootToolchainFile_2284_; uint8_t v___y_2286_; uint8_t v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2430_; uint8_t v___y_2431_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_lakeEnv_2275_ = lean_ctor_get(v_ws_2235_, 0);
lean_inc_ref(v_lakeEnv_2275_);
v_lakeArgs_x3f_2276_ = lean_ctor_get(v_ws_2235_, 3);
lean_inc(v_lakeArgs_x3f_2276_);
v_packages_2277_ = lean_ctor_get(v_ws_2235_, 4);
lean_inc_ref(v_packages_2277_);
lean_dec_ref(v_ws_2235_);
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = lean_array_fget(v_packages_2277_, v___x_2278_);
lean_dec_ref(v_packages_2277_);
v_baseName_2280_ = lean_ctor_get(v___x_2279_, 1);
lean_inc(v_baseName_2280_);
v_dir_2281_ = lean_ctor_get(v___x_2279_, 4);
lean_inc_ref_n(v_dir_2281_, 3);
v_config_2282_ = lean_ctor_get(v___x_2279_, 6);
lean_inc_ref(v_config_2282_);
lean_dec(v___x_2279_);
v___x_2283_ = l_Lake_toolchainFileName;
v_rootToolchainFile_2284_ = l_Lake_joinRelative(v_dir_2281_, v___x_2283_);
v___x_2435_ = l_System_FilePath_join(v_dir_2281_, v___x_2283_);
v___x_2436_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2435_);
lean_dec_ref(v___x_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2489_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2489_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2489_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v_src_2442_; lean_object* v_tc_x3f_2443_; lean_object* v_clashes_2444_; uint8_t v_fixed_2445_; uint8_t v_fixedToolchain_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v_fixedToolchain_2468_ = lean_ctor_get_uint8(v_config_2282_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_2282_);
v___x_2469_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___x_2470_ = lean_array_get_size(v_rootDeps_2236_);
v___x_2471_ = lean_nat_dec_lt(v___x_2278_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_dec_ref(v_dir_2281_);
lean_inc(v_a_2437_);
v_src_2442_ = v_baseName_2280_;
v_tc_x3f_2443_ = v_a_2437_;
v_clashes_2444_ = v___x_2469_;
v_fixed_2445_ = v_fixedToolchain_2468_;
goto v___jp_2441_;
}
else
{
lean_object* v___x_2472_; size_t v___x_2473_; size_t v___x_2474_; lean_object* v___x_2475_; 
lean_inc(v_a_2437_);
v___x_2472_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2472_, 0, v_baseName_2280_);
lean_ctor_set(v___x_2472_, 1, v_a_2437_);
lean_ctor_set(v___x_2472_, 2, v___x_2469_);
lean_ctor_set_uint8(v___x_2472_, sizeof(void*)*3, v_fixedToolchain_2468_);
v___x_2473_ = ((size_t)0ULL);
v___x_2474_ = lean_usize_of_nat(v___x_2470_);
v___x_2475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2281_, v_rootDeps_2236_, v___x_2473_, v___x_2474_, v___x_2472_, v_a_2237_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v_src_2477_; lean_object* v_tc_x3f_2478_; lean_object* v_clashes_2479_; uint8_t v_fixed_2480_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
v_src_2477_ = lean_ctor_get(v_a_2476_, 0);
lean_inc(v_src_2477_);
v_tc_x3f_2478_ = lean_ctor_get(v_a_2476_, 1);
lean_inc(v_tc_x3f_2478_);
v_clashes_2479_ = lean_ctor_get(v_a_2476_, 2);
lean_inc_ref(v_clashes_2479_);
v_fixed_2480_ = lean_ctor_get_uint8(v_a_2476_, sizeof(void*)*3);
lean_dec(v_a_2476_);
v_src_2442_ = v_src_2477_;
v_tc_x3f_2443_ = v_tc_x3f_2478_;
v_clashes_2444_ = v_clashes_2479_;
v_fixed_2445_ = v_fixed_2480_;
goto v___jp_2441_;
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_del_object(v___x_2439_);
lean_dec(v_a_2437_);
lean_dec_ref(v_rootToolchainFile_2284_);
lean_dec(v_lakeArgs_x3f_2276_);
lean_dec_ref(v_lakeEnv_2275_);
v_a_2481_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2475_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2475_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
v___jp_2441_:
{
lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2446_ = lean_array_get_size(v_clashes_2444_);
v___x_2447_ = lean_nat_dec_lt(v___x_2278_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_dec_ref(v_clashes_2444_);
lean_dec(v_src_2442_);
if (lean_obj_tag(v_tc_x3f_2443_) == 1)
{
if (lean_obj_tag(v_a_2437_) == 0)
{
lean_object* v_val_2448_; 
lean_del_object(v___x_2439_);
v_val_2448_ = lean_ctor_get(v_tc_x3f_2443_, 0);
lean_inc(v_val_2448_);
lean_dec_ref_known(v_tc_x3f_2443_, 1);
v___y_2430_ = v_val_2448_;
v___y_2431_ = v___x_2447_;
goto v___jp_2429_;
}
else
{
lean_object* v_val_2449_; lean_object* v_val_2450_; uint8_t v___x_2451_; 
v_val_2449_ = lean_ctor_get(v_tc_x3f_2443_, 0);
lean_inc_n(v_val_2449_, 2);
lean_dec_ref_known(v_tc_x3f_2443_, 1);
v_val_2450_ = lean_ctor_get(v_a_2437_, 0);
lean_inc(v_val_2450_);
lean_dec_ref_known(v_a_2437_, 1);
v___x_2451_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2450_, v_val_2449_);
if (v___x_2451_ == 0)
{
lean_del_object(v___x_2439_);
v___y_2430_ = v_val_2449_;
v___y_2431_ = v___x_2451_;
goto v___jp_2429_;
}
else
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_dec(v_val_2449_);
lean_dec_ref(v_rootToolchainFile_2284_);
lean_dec(v_lakeArgs_x3f_2276_);
lean_dec_ref(v_lakeEnv_2275_);
v___x_2452_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15));
lean_inc_ref(v_a_2237_);
v___x_2453_ = lean_apply_2(v_a_2237_, v___x_2452_, lean_box(0));
v___x_2454_ = lean_box(0);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2454_);
v___x_2456_ = v___x_2439_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
lean_dec(v_tc_x3f_2443_);
lean_dec(v_a_2437_);
lean_dec_ref(v_rootToolchainFile_2284_);
lean_dec(v_lakeArgs_x3f_2276_);
lean_dec_ref(v_lakeEnv_2275_);
v___x_2458_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17));
lean_inc_ref(v_a_2237_);
v___x_2459_ = lean_apply_2(v_a_2237_, v___x_2458_, lean_box(0));
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2459_);
v___x_2461_ = v___x_2439_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
else
{
lean_del_object(v___x_2439_);
lean_dec(v_a_2437_);
lean_dec_ref(v_rootToolchainFile_2284_);
lean_dec(v_lakeArgs_x3f_2276_);
lean_dec_ref(v_lakeEnv_2275_);
if (lean_obj_tag(v_tc_x3f_2443_) == 1)
{
if (v_fixed_2445_ == 0)
{
lean_object* v_val_2463_; lean_object* v___x_2464_; 
v_val_2463_ = lean_ctor_get(v_tc_x3f_2443_, 0);
lean_inc(v_val_2463_);
lean_dec_ref_known(v_tc_x3f_2443_, 1);
v___x_2464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2267_ = v___x_2447_;
v___y_2268_ = v___x_2446_;
v___y_2269_ = v_clashes_2444_;
v___y_2270_ = v_src_2442_;
v___y_2271_ = v_val_2463_;
v___y_2272_ = v___x_2464_;
goto v___jp_2266_;
}
else
{
lean_object* v_val_2465_; lean_object* v___x_2466_; 
v_val_2465_ = lean_ctor_get(v_tc_x3f_2443_, 0);
lean_inc(v_val_2465_);
lean_dec_ref_known(v_tc_x3f_2443_, 1);
v___x_2466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2267_ = v___x_2447_;
v___y_2268_ = v___x_2446_;
v___y_2269_ = v_clashes_2444_;
v___y_2270_ = v_src_2442_;
v___y_2271_ = v_val_2465_;
v___y_2272_ = v___x_2466_;
goto v___jp_2266_;
}
}
else
{
lean_object* v___x_2467_; 
lean_dec(v_tc_x3f_2443_);
lean_dec(v_src_2442_);
v___x_2467_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
v___y_2246_ = v___x_2446_;
v___y_2247_ = v_clashes_2444_;
v___y_2248_ = v___x_2467_;
goto v___jp_2245_;
}
}
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v_rootToolchainFile_2284_);
lean_dec_ref(v_config_2282_);
lean_dec_ref(v_dir_2281_);
lean_dec(v_baseName_2280_);
lean_dec(v_lakeArgs_x3f_2276_);
lean_dec_ref(v_lakeEnv_2275_);
v_a_2490_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2492_ = v___x_2436_;
v_isShared_2493_ = v_isSharedCheck_2502_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2436_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2502_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2494_ = lean_io_error_to_string(v_a_2490_);
v___x_2495_ = 3;
v___x_2496_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*1, v___x_2495_);
lean_inc_ref(v_a_2237_);
v___x_2497_ = lean_apply_2(v_a_2237_, v___x_2496_, lean_box(0));
v___x_2498_ = lean_box(0);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2498_);
v___x_2500_ = v___x_2492_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
v___jp_2239_:
{
uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2241_ = 2;
v___x_2242_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2242_, 0, v___y_2240_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*1, v___x_2241_);
lean_inc_ref(v_a_2237_);
v___x_2243_ = lean_apply_2(v_a_2237_, v___x_2242_, lean_box(0));
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
v___jp_2245_:
{
size_t v___x_2249_; size_t v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = ((size_t)0ULL);
v___x_2250_ = lean_usize_of_nat(v___y_2246_);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2246_, v___y_2247_, v___x_2249_, v___x_2250_, v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
v___y_2240_ = v___x_2251_;
goto v___jp_2239_;
}
v___jp_2252_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_inc_ref(v___y_2258_);
v___x_2260_ = lean_string_append(v___y_2258_, v___y_2259_);
lean_dec_ref(v___y_2259_);
v___x_2261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2262_ = lean_string_append(v___x_2260_, v___x_2261_);
v___x_2263_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2257_, v___y_2255_);
v___x_2264_ = lean_string_append(v___x_2262_, v___x_2263_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = lean_string_append(v___x_2264_, v___y_2254_);
if (v___y_2255_ == 0)
{
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2253_);
v___y_2240_ = v___x_2265_;
goto v___jp_2239_;
}
else
{
v___y_2246_ = v___y_2253_;
v___y_2247_ = v___y_2256_;
v___y_2248_ = v___x_2265_;
goto v___jp_2245_;
}
}
v___jp_2266_:
{
lean_object* v___x_2273_; lean_object* v_toString_2274_; 
v___x_2273_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_2274_ = lean_ctor_get(v___y_2271_, 0);
lean_inc_ref(v_toString_2274_);
lean_dec_ref(v___y_2271_);
v___y_2253_ = v___y_2268_;
v___y_2254_ = v___y_2272_;
v___y_2255_ = v___y_2267_;
v___y_2256_ = v___y_2269_;
v___y_2257_ = v___y_2270_;
v___y_2258_ = v___x_2273_;
v___y_2259_ = v_toString_2274_;
goto v___jp_2252_;
}
v___jp_2285_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_inc_ref(v___y_2288_);
v___x_2290_ = lean_string_append(v___y_2288_, v___y_2289_);
v___x_2291_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2292_ = lean_string_append(v___x_2290_, v___x_2291_);
v___x_2293_ = 1;
v___x_2294_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*1, v___x_2293_);
lean_inc_ref(v_a_2237_);
v___x_2295_ = lean_apply_2(v_a_2237_, v___x_2294_, lean_box(0));
v___x_2296_ = l_IO_FS_writeFile(v_rootToolchainFile_2284_, v___y_2289_);
lean_dec_ref(v_rootToolchainFile_2284_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_dec_ref_known(v___x_2296_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2276_) == 1)
{
lean_object* v_elan_x3f_2297_; 
v_elan_x3f_2297_ = lean_ctor_get(v_lakeEnv_2275_, 2);
if (lean_obj_tag(v_elan_x3f_2297_) == 1)
{
lean_object* v_val_2298_; lean_object* v_val_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v_elan_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_val_2298_ = lean_ctor_get(v_lakeArgs_x3f_2276_, 0);
lean_inc(v_val_2298_);
lean_dec_ref_known(v_lakeArgs_x3f_2276_, 1);
v_val_2299_ = lean_ctor_get(v_elan_x3f_2297_, 0);
v___x_2300_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_2237_);
v___x_2301_ = lean_apply_2(v_a_2237_, v___x_2300_, lean_box(0));
v___x_2302_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_2303_ = lean_ctor_get(v_val_2299_, 1);
lean_inc_ref(v_elan_2303_);
v___x_2304_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_2305_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_2306_ = lean_array_push(v___x_2305_, v___y_2289_);
v___x_2307_ = lean_array_push(v___x_2306_, v___x_2304_);
v___x_2308_ = l_Array_append___redArg(v___x_2307_, v_val_2298_);
lean_dec(v_val_2298_);
v___x_2309_ = lean_box(0);
v___x_2310_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2275_);
v___x_2311_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2311_, 0, v___x_2302_);
lean_ctor_set(v___x_2311_, 1, v_elan_2303_);
lean_ctor_set(v___x_2311_, 2, v___x_2308_);
lean_ctor_set(v___x_2311_, 3, v___x_2309_);
lean_ctor_set(v___x_2311_, 4, v___x_2310_);
lean_ctor_set_uint8(v___x_2311_, sizeof(void*)*5, v___y_2287_);
lean_ctor_set_uint8(v___x_2311_, sizeof(void*)*5 + 1, v___y_2286_);
v___x_2312_ = lean_io_process_spawn(v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2314_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 1);
v___x_2314_ = lean_io_process_child_wait(v___x_2302_, v_a_2313_);
lean_dec(v_a_2313_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; uint32_t v___x_2316_; uint8_t v___x_2317_; lean_object* v___x_2318_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = lean_unbox_uint32(v_a_2315_);
lean_dec(v_a_2315_);
v___x_2317_ = lean_uint32_to_uint8(v___x_2316_);
v___x_2318_ = lean_io_exit(v___x_2317_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2339_; 
v_a_2327_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2329_ = v___x_2318_;
v_isShared_2330_ = v_isSharedCheck_2339_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2318_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2339_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; uint8_t v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2331_ = lean_io_error_to_string(v_a_2327_);
v___x_2332_ = 3;
v___x_2333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*1, v___x_2332_);
lean_inc_ref(v_a_2237_);
v___x_2334_ = lean_apply_2(v_a_2237_, v___x_2333_, lean_box(0));
v___x_2335_ = lean_box(0);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2335_);
v___x_2337_ = v___x_2329_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2352_; 
v_a_2340_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2342_ = v___x_2314_;
v_isShared_2343_ = v_isSharedCheck_2352_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2314_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2352_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2344_ = lean_io_error_to_string(v_a_2340_);
v___x_2345_ = 3;
v___x_2346_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*1, v___x_2345_);
lean_inc_ref(v_a_2237_);
v___x_2347_ = lean_apply_2(v_a_2237_, v___x_2346_, lean_box(0));
v___x_2348_ = lean_box(0);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2348_);
v___x_2350_ = v___x_2342_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2365_; 
v_a_2353_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2355_ = v___x_2312_;
v_isShared_2356_ = v_isSharedCheck_2365_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2312_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2365_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2357_ = lean_io_error_to_string(v_a_2353_);
v___x_2358_ = 3;
v___x_2359_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set_uint8(v___x_2359_, sizeof(void*)*1, v___x_2358_);
lean_inc_ref(v_a_2237_);
v___x_2360_ = lean_apply_2(v_a_2237_, v___x_2359_, lean_box(0));
v___x_2361_ = lean_box(0);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2361_);
v___x_2363_ = v___x_2355_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; 
lean_dec_ref_known(v_lakeArgs_x3f_2276_, 1);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v_lakeEnv_2275_);
v___x_2366_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_2237_);
v___x_2367_ = lean_apply_2(v_a_2237_, v___x_2366_, lean_box(0));
v___x_2368_ = 4;
v___x_2369_ = lean_io_exit(v___x_2368_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2390_; 
v_a_2378_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2380_ = v___x_2369_;
v_isShared_2381_ = v_isSharedCheck_2390_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2369_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2390_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2382_ = lean_io_error_to_string(v_a_2378_);
v___x_2383_ = 3;
v___x_2384_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*1, v___x_2383_);
lean_inc_ref(v_a_2237_);
v___x_2385_ = lean_apply_2(v_a_2237_, v___x_2384_, lean_box(0));
v___x_2386_ = lean_box(0);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2386_);
v___x_2388_ = v___x_2380_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; 
lean_dec_ref(v___y_2289_);
lean_dec(v_lakeArgs_x3f_2276_);
lean_dec_ref(v_lakeEnv_2275_);
v___x_2391_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2237_);
v___x_2392_ = lean_apply_2(v_a_2237_, v___x_2391_, lean_box(0));
v___x_2393_ = 4;
v___x_2394_ = lean_io_exit(v___x_2393_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2415_; 
v_a_2403_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2405_ = v___x_2394_;
v_isShared_2406_ = v_isSharedCheck_2415_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2394_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2415_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2407_ = lean_io_error_to_string(v_a_2403_);
v___x_2408_ = 3;
v___x_2409_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set_uint8(v___x_2409_, sizeof(void*)*1, v___x_2408_);
lean_inc_ref(v_a_2237_);
v___x_2410_ = lean_apply_2(v_a_2237_, v___x_2409_, lean_box(0));
v___x_2411_ = lean_box(0);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2411_);
v___x_2413_ = v___x_2405_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v___y_2289_);
lean_dec(v_lakeArgs_x3f_2276_);
lean_dec_ref(v_lakeEnv_2275_);
v_a_2416_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2418_ = v___x_2296_;
v_isShared_2419_ = v_isSharedCheck_2428_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2296_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2428_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2420_ = lean_io_error_to_string(v_a_2416_);
v___x_2421_ = 3;
v___x_2422_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2420_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*1, v___x_2421_);
lean_inc_ref(v_a_2237_);
v___x_2423_ = lean_apply_2(v_a_2237_, v___x_2422_, lean_box(0));
v___x_2424_ = lean_box(0);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2424_);
v___x_2426_ = v___x_2418_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
v___jp_2429_:
{
uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v_toString_2434_; 
v___x_2432_ = 1;
v___x_2433_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2434_ = lean_ctor_get(v___y_2430_, 0);
lean_inc_ref(v_toString_2434_);
lean_dec_ref(v___y_2430_);
v___y_2286_ = v___y_2431_;
v___y_2287_ = v___x_2432_;
v___y_2288_ = v___x_2433_;
v___y_2289_ = v_toString_2434_;
goto v___jp_2285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2503_, lean_object* v_rootDeps_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2503_, v_rootDeps_2504_, v_a_2505_);
lean_dec_ref(v_a_2505_);
lean_dec_ref(v_rootDeps_2504_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2508_, lean_object* v_dep_2509_, lean_object* v_ws_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2510_, v_pkg_2508_, v_dep_2509_, v_a_2511_, v_a_2512_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v_fst_2516_; lean_object* v_snd_2517_; lean_object* v___x_2518_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v_fst_2516_ = lean_ctor_get(v_a_2515_, 0);
lean_inc_n(v_fst_2516_, 2);
v_snd_2517_ = lean_ctor_get(v_a_2515_, 1);
lean_inc(v_snd_2517_);
lean_dec(v_a_2515_);
v___x_2518_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2516_, v_snd_2517_, v_a_2512_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2535_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2535_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2535_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v_snd_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2533_; 
v_snd_2523_ = lean_ctor_get(v_a_2519_, 1);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_a_2519_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v_a_2519_, 0);
lean_dec(v_unused_2534_);
v___x_2525_ = v_a_2519_;
v_isShared_2526_ = v_isSharedCheck_2533_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_snd_2523_);
lean_dec(v_a_2519_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2533_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v_fst_2516_);
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_fst_2516_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_snd_2523_);
v___x_2528_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2530_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2528_);
v___x_2530_ = v___x_2521_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_fst_2516_);
v_a_2536_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2518_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2518_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2544_, lean_object* v_dep_2545_, lean_object* v_ws_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2544_, v_dep_2545_, v_ws_2546_, v_a_2547_, v_a_2548_);
lean_dec_ref(v_a_2548_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2551_, lean_object* v_ws_2552_, lean_object* v_pkg_2553_, lean_object* v_dep_2554_, lean_object* v_a_2555_){
_start:
{
uint8_t v___y_2558_; lean_object* v___y_2559_; lean_object* v_name_2589_; lean_object* v___x_2590_; 
v_name_2589_ = lean_ctor_get(v_dep_2554_, 0);
v___x_2590_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2555_, v_name_2589_);
if (lean_obj_tag(v___x_2590_) == 1)
{
lean_object* v_val_2591_; lean_object* v_lakeEnv_2592_; lean_object* v_packages_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v_config_2596_; lean_object* v_dir_2597_; lean_object* v_toWorkspaceConfig_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec_ref(v_dep_2554_);
lean_dec_ref(v_pkg_2553_);
v_val_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_val_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v_lakeEnv_2592_ = lean_ctor_get(v_ws_2552_, 0);
lean_inc_ref(v_lakeEnv_2592_);
v_packages_2593_ = lean_ctor_get(v_ws_2552_, 4);
lean_inc_ref(v_packages_2593_);
lean_dec_ref(v_ws_2552_);
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = lean_array_fget(v_packages_2593_, v___x_2594_);
lean_dec_ref(v_packages_2593_);
v_config_2596_ = lean_ctor_get(v___x_2595_, 6);
lean_inc_ref(v_config_2596_);
v_dir_2597_ = lean_ctor_get(v___x_2595_, 4);
lean_inc_ref(v_dir_2597_);
lean_dec(v___x_2595_);
v_toWorkspaceConfig_2598_ = lean_ctor_get(v_config_2596_, 0);
lean_inc_ref(v_toWorkspaceConfig_2598_);
lean_dec_ref(v_config_2596_);
v___x_2599_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2598_);
v___x_2600_ = l_Lake_PackageEntry_materialize(v_val_2591_, v_lakeEnv_2592_, v_dir_2597_, v___x_2599_, v___y_2551_);
lean_dec_ref(v_lakeEnv_2592_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2609_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2603_ = v___x_2600_;
v_isShared_2604_ = v_isSharedCheck_2609_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2600_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2609_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v_a_2601_);
lean_ctor_set(v___x_2605_, 1, v_a_2555_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2605_);
v___x_2607_ = v___x_2603_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_a_2555_);
v_a_2610_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2600_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2600_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v_wsIdx_2618_; lean_object* v_relDir_2619_; uint8_t v___y_2621_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
lean_dec(v___x_2590_);
v_wsIdx_2618_ = lean_ctor_get(v_pkg_2553_, 0);
lean_inc(v_wsIdx_2618_);
v_relDir_2619_ = lean_ctor_get(v_pkg_2553_, 5);
lean_inc_ref(v_relDir_2619_);
lean_dec_ref(v_pkg_2553_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = lean_nat_dec_eq(v_wsIdx_2618_, v___x_2625_);
lean_dec(v_wsIdx_2618_);
if (v___x_2626_ == 0)
{
uint8_t v___x_2627_; 
v___x_2627_ = 1;
v___y_2621_ = v___x_2627_;
goto v___jp_2620_;
}
else
{
uint8_t v___x_2628_; 
v___x_2628_ = 0;
v___y_2621_ = v___x_2628_;
goto v___jp_2620_;
}
v___jp_2620_:
{
lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2623_ = lean_string_dec_eq(v_relDir_2619_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lake_joinRelative(v_relDir_2619_, v___x_2622_);
v___y_2558_ = v___y_2621_;
v___y_2559_ = v___x_2624_;
goto v___jp_2557_;
}
else
{
v___y_2558_ = v___y_2621_;
v___y_2559_ = v_relDir_2619_;
goto v___jp_2557_;
}
}
}
v___jp_2557_:
{
lean_object* v_lakeEnv_2560_; lean_object* v_packages_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v_config_2564_; lean_object* v_dir_2565_; lean_object* v_toWorkspaceConfig_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_lakeEnv_2560_ = lean_ctor_get(v_ws_2552_, 0);
lean_inc_ref(v_lakeEnv_2560_);
v_packages_2561_ = lean_ctor_get(v_ws_2552_, 4);
lean_inc_ref(v_packages_2561_);
lean_dec_ref(v_ws_2552_);
v___x_2562_ = lean_unsigned_to_nat(0u);
v___x_2563_ = lean_array_fget(v_packages_2561_, v___x_2562_);
lean_dec_ref(v_packages_2561_);
v_config_2564_ = lean_ctor_get(v___x_2563_, 6);
lean_inc_ref(v_config_2564_);
v_dir_2565_ = lean_ctor_get(v___x_2563_, 4);
lean_inc_ref(v_dir_2565_);
lean_dec(v___x_2563_);
v_toWorkspaceConfig_2566_ = lean_ctor_get(v_config_2564_, 0);
lean_inc_ref(v_toWorkspaceConfig_2566_);
lean_dec_ref(v_config_2564_);
v___x_2567_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2566_);
v___x_2568_ = l_Lake_Dependency_materialize(v_dep_2554_, v___y_2558_, v_lakeEnv_2560_, v_dir_2565_, v___x_2567_, v___y_2559_, v___y_2551_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2580_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2580_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2580_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v_manifestEntry_2573_; lean_object* v_name_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v_manifestEntry_2573_ = lean_ctor_get(v_a_2569_, 4);
v_name_2574_ = lean_ctor_get(v_manifestEntry_2573_, 0);
lean_inc_ref(v_manifestEntry_2573_);
lean_inc(v_name_2574_);
v___x_2575_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2574_, v_manifestEntry_2573_, v_a_2555_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_a_2569_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2576_);
v___x_2578_ = v___x_2571_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_a_2555_);
v_a_2581_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2568_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2568_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2629_, lean_object* v_ws_2630_, lean_object* v_pkg_2631_, lean_object* v_dep_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2629_, v_ws_2630_, v_pkg_2631_, v_dep_2632_, v_a_2633_);
lean_dec_ref(v___y_2629_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2636_, lean_object* v_dep_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v_manifestEntry_2640_; lean_object* v_pkgDir_2641_; lean_object* v_name_2642_; lean_object* v_manifestFile_x3f_2643_; lean_object* v___y_2645_; lean_object* v_fst_2646_; lean_object* v_snd_2647_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v_val_2699_; lean_object* v___y_2715_; 
v_manifestEntry_2640_ = lean_ctor_get(v_dep_2637_, 4);
v_pkgDir_2641_ = lean_ctor_get(v_dep_2637_, 0);
v_name_2642_ = lean_ctor_get(v_manifestEntry_2640_, 0);
v_manifestFile_x3f_2643_ = lean_ctor_get(v_manifestEntry_2640_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2643_) == 0)
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2641_);
v___x_2736_ = l_Lake_joinRelative(v_pkgDir_2641_, v___x_2735_);
v___y_2715_ = v___x_2736_;
goto v___jp_2714_;
}
else
{
lean_object* v_val_2737_; lean_object* v___x_2738_; 
v_val_2737_ = lean_ctor_get(v_manifestFile_x3f_2643_, 0);
lean_inc(v_val_2737_);
lean_inc_ref(v_pkgDir_2641_);
v___x_2738_ = l_Lake_joinRelative(v_pkgDir_2641_, v_val_2737_);
v___y_2715_ = v___x_2738_;
goto v___jp_2714_;
}
v___jp_2644_:
{
if (lean_obj_tag(v_fst_2646_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2677_; 
lean_inc(v_name_2642_);
lean_dec_ref(v_dep_2637_);
v_a_2648_ = lean_ctor_get(v_fst_2646_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_fst_2646_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2650_ = v_fst_2646_;
v_isShared_2651_ = v_isSharedCheck_2677_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v_fst_2646_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2677_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
if (lean_obj_tag(v_a_2648_) == 11)
{
uint8_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
lean_dec_ref_known(v_a_2648_, 2);
v___x_2652_ = 0;
v___x_2653_ = l_Lean_Name_toString(v_name_2642_, v___x_2652_);
v___x_2654_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2655_ = lean_string_append(v___x_2653_, v___x_2654_);
v___x_2656_ = lean_string_append(v___x_2655_, v___y_2645_);
lean_dec_ref(v___y_2645_);
v___x_2657_ = 2;
v___x_2658_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*1, v___x_2657_);
v___x_2659_ = lean_apply_2(v___y_2636_, v___x_2658_, lean_box(0));
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
lean_ctor_set(v___x_2660_, 1, v_snd_2647_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2660_);
v___x_2662_ = v___x_2650_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
else
{
uint8_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
lean_dec_ref(v___y_2645_);
v___x_2664_ = 0;
v___x_2665_ = l_Lean_Name_toString(v_name_2642_, v___x_2664_);
v___x_2666_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2667_ = lean_string_append(v___x_2665_, v___x_2666_);
v___x_2668_ = lean_io_error_to_string(v_a_2648_);
v___x_2669_ = lean_string_append(v___x_2667_, v___x_2668_);
lean_dec_ref(v___x_2668_);
v___x_2670_ = 2;
v___x_2671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*1, v___x_2670_);
v___x_2672_ = lean_apply_2(v___y_2636_, v___x_2671_, lean_box(0));
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
lean_ctor_set(v___x_2673_, 1, v_snd_2647_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2673_);
v___x_2675_ = v___x_2650_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref(v___y_2645_);
lean_dec_ref(v___y_2636_);
v_a_2678_ = lean_ctor_get(v_fst_2646_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_fst_2646_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2680_ = v_fst_2646_;
v_isShared_2681_ = v_isSharedCheck_2694_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v_fst_2646_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2694_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v_packages_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v_packages_2682_ = lean_ctor_get(v_a_2678_, 3);
lean_inc_ref(v_packages_2682_);
lean_dec(v_a_2678_);
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = lean_array_get_size(v_packages_2682_);
v___x_2685_ = lean_box(0);
v___x_2686_ = lean_nat_dec_lt(v___x_2683_, v___x_2684_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
lean_dec_ref(v_packages_2682_);
lean_dec_ref(v_dep_2637_);
v___x_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v_snd_2647_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2687_);
v___x_2689_ = v___x_2680_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
else
{
size_t v___x_2691_; size_t v___x_2692_; lean_object* v___x_2693_; 
lean_del_object(v___x_2680_);
v___x_2691_ = ((size_t)0ULL);
v___x_2692_ = lean_usize_of_nat(v___x_2684_);
v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2637_, v_packages_2682_, v___x_2691_, v___x_2692_, v___x_2685_, v_snd_2647_);
lean_dec_ref(v_packages_2682_);
return v___x_2693_;
}
}
}
}
v___jp_2695_:
{
lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2700_ = lean_array_get_size(v___y_2698_);
v___x_2701_ = lean_nat_dec_lt(v___y_2697_, v___x_2700_);
if (v___x_2701_ == 0)
{
v___y_2645_ = v___y_2696_;
v_fst_2646_ = v_val_2699_;
v_snd_2647_ = v_a_2638_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2702_; size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
v___x_2702_ = lean_box(0);
v___x_2703_ = ((size_t)0ULL);
v___x_2704_ = lean_usize_of_nat(v___x_2700_);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2698_, v___x_2703_, v___x_2704_, v___x_2702_, v___y_2636_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_dec_ref_known(v___x_2705_, 1);
v___y_2645_ = v___y_2696_;
v_fst_2646_ = v_val_2699_;
v_snd_2647_ = v_a_2638_;
goto v___jp_2644_;
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v_val_2699_);
lean_dec_ref(v___y_2696_);
lean_dec(v_a_2638_);
lean_dec_ref(v_dep_2637_);
lean_dec_ref(v___y_2636_);
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
v___jp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = lean_unsigned_to_nat(0u);
v___x_2717_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2715_);
v___x_2718_ = l_Lake_Manifest_load(v___y_2715_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
lean_ctor_set_tag(v___x_2721_, 1);
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
v___y_2696_ = v___y_2715_;
v___y_2697_ = v___x_2716_;
v___y_2698_ = v___x_2717_;
v_val_2699_ = v___x_2724_;
goto v___jp_2695_;
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
v_a_2727_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2718_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2718_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set_tag(v___x_2729_, 0);
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
v___y_2696_ = v___y_2715_;
v___y_2697_ = v___x_2716_;
v___y_2698_ = v___x_2717_;
v_val_2699_ = v___x_2732_;
goto v___jp_2695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2739_, lean_object* v_dep_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2739_, v_dep_2740_, v_a_2741_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2748_, v___y_2746_, v___y_2744_, v___y_2745_, v___y_2747_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v_fst_2752_; lean_object* v_snd_2753_; lean_object* v___x_2754_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v_fst_2752_ = lean_ctor_get(v_a_2751_, 0);
lean_inc_n(v_fst_2752_, 2);
v_snd_2753_ = lean_ctor_get(v_a_2751_, 1);
lean_inc(v_snd_2753_);
lean_dec(v_a_2751_);
v___x_2754_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2748_, v_fst_2752_, v_snd_2753_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2771_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2771_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2771_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v_snd_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2769_; 
v_snd_2759_ = lean_ctor_get(v_a_2755_, 1);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_a_2755_);
if (v_isSharedCheck_2769_ == 0)
{
lean_object* v_unused_2770_; 
v_unused_2770_ = lean_ctor_get(v_a_2755_, 0);
lean_dec(v_unused_2770_);
v___x_2761_ = v_a_2755_;
v_isShared_2762_ = v_isSharedCheck_2769_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_snd_2759_);
lean_dec(v_a_2755_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2769_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v_fst_2752_);
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_fst_2752_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_snd_2759_);
v___x_2764_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2766_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2764_);
v___x_2766_ = v___x_2757_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_fst_2752_);
v_a_2772_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2754_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2754_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
else
{
lean_dec_ref(v___y_2748_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2787_, lean_object* v_ws_2788_, lean_object* v_toUpdate_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v___y_2793_; lean_object* v___y_2798_; lean_object* v_fst_2799_; lean_object* v_snd_2800_; lean_object* v_packages_2819_; lean_object* v___x_2820_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v_val_2825_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v_a_2844_; lean_object* v___x_2846_; lean_object* v_baseName_2847_; lean_object* v_dir_2848_; lean_object* v_config_2849_; lean_object* v_relManifestFile_2850_; lean_object* v_depConfigs_2851_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; uint8_t v_fst_2856_; lean_object* v_snd_2857_; lean_object* v_packagesDir_x3f_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; uint8_t v___x_2911_; lean_object* v_rootName_2912_; lean_object* v_fst_2914_; lean_object* v_snd_2915_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v_val_2982_; lean_object* v___x_2996_; 
v_packages_2819_ = lean_ctor_get(v_ws_2788_, 4);
v___x_2820_ = lean_unsigned_to_nat(0u);
v___x_2846_ = lean_array_fget_borrowed(v_packages_2819_, v___x_2820_);
v_baseName_2847_ = lean_ctor_get(v___x_2846_, 1);
v_dir_2848_ = lean_ctor_get(v___x_2846_, 4);
v_config_2849_ = lean_ctor_get(v___x_2846_, 6);
v_relManifestFile_2850_ = lean_ctor_get(v___x_2846_, 9);
v_depConfigs_2851_ = lean_ctor_get(v___x_2846_, 12);
v___x_2911_ = 0;
lean_inc(v_baseName_2847_);
v_rootName_2912_ = l_Lean_Name_toString(v_baseName_2847_, v___x_2911_);
lean_inc_ref(v_relManifestFile_2850_);
lean_inc_ref(v_dir_2848_);
v___x_2979_ = l_Lake_joinRelative(v_dir_2848_, v_relManifestFile_2850_);
v___x_2980_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2996_ = l_Lake_Manifest_load(v___x_2979_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2996_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2996_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
lean_ctor_set_tag(v___x_2999_, 1);
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
v_val_2982_ = v___x_3002_;
goto v___jp_2981_;
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
v_a_3005_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2996_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2996_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set_tag(v___x_3007_, 0);
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
v_val_2982_ = v___x_3010_;
goto v___jp_2981_;
}
}
}
v___jp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2794_ = lean_box(0);
v___x_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
lean_ctor_set(v___x_2795_, 1, v___y_2793_);
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
return v___x_2796_;
}
v___jp_2797_:
{
if (lean_obj_tag(v_fst_2799_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_snd_2800_);
v_a_2801_ = lean_ctor_get(v_fst_2799_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_fst_2799_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2803_ = v_fst_2799_;
v_isShared_2804_ = v_isSharedCheck_2815_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v_fst_2799_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2815_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2805_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2806_ = lean_io_error_to_string(v_a_2801_);
v___x_2807_ = lean_string_append(v___x_2805_, v___x_2806_);
lean_dec_ref(v___x_2806_);
v___x_2808_ = 3;
v___x_2809_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2809_, 0, v___x_2807_);
lean_ctor_set_uint8(v___x_2809_, sizeof(void*)*1, v___x_2808_);
lean_inc_ref(v___y_2798_);
v___x_2810_ = lean_apply_2(v___y_2798_, v___x_2809_, lean_box(0));
v___x_2811_ = lean_box(0);
if (v_isShared_2804_ == 0)
{
lean_ctor_set_tag(v___x_2803_, 1);
lean_ctor_set(v___x_2803_, 0, v___x_2811_);
v___x_2813_ = v___x_2803_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v_fst_2799_);
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
lean_ctor_set(v___x_2817_, 1, v_snd_2800_);
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
return v___x_2818_;
}
}
v___jp_2821_:
{
lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2826_ = lean_array_get_size(v___y_2824_);
v___x_2827_ = lean_nat_dec_lt(v___x_2820_, v___x_2826_);
if (v___x_2827_ == 0)
{
v___y_2798_ = v___y_2822_;
v_fst_2799_ = v_val_2825_;
v_snd_2800_ = v___y_2823_;
goto v___jp_2797_;
}
else
{
lean_object* v___x_2828_; size_t v___x_2829_; size_t v___x_2830_; lean_object* v___x_2831_; 
v___x_2828_ = lean_box(0);
v___x_2829_ = ((size_t)0ULL);
v___x_2830_ = lean_usize_of_nat(v___x_2826_);
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2824_, v___x_2829_, v___x_2830_, v___x_2828_, v___y_2822_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_dec_ref_known(v___x_2831_, 1);
v___y_2798_ = v___y_2822_;
v_fst_2799_ = v_val_2825_;
v_snd_2800_ = v___y_2823_;
goto v___jp_2797_;
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec_ref(v_val_2825_);
lean_dec(v___y_2823_);
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
v___jp_2840_:
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2845_, 0, v_a_2844_);
v___y_2822_ = v___y_2841_;
v___y_2823_ = v___y_2842_;
v___y_2824_ = v___y_2843_;
v_val_2825_ = v___x_2845_;
goto v___jp_2821_;
}
v___jp_2852_:
{
lean_object* v_toWorkspaceConfig_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v_toWorkspaceConfig_2858_ = lean_ctor_get(v_config_2849_, 0);
v___x_2859_ = l_System_FilePath_normalize(v___y_2854_);
lean_inc_ref(v_toWorkspaceConfig_2858_);
v___x_2860_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2858_);
lean_inc_ref(v___x_2860_);
v___x_2861_ = l_System_FilePath_normalize(v___x_2860_);
v___x_2862_ = lean_string_dec_eq(v___x_2859_, v___x_2861_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2859_);
if (v___x_2862_ == 0)
{
if (v_fst_2856_ == 0)
{
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___y_2855_);
v___y_2793_ = v_snd_2857_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2863_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2864_ = lean_string_append(v___x_2863_, v___y_2855_);
v___x_2865_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2866_ = lean_string_append(v___x_2864_, v___x_2865_);
lean_inc_ref(v_dir_2848_);
v___x_2867_ = l_Lake_joinRelative(v_dir_2848_, v___x_2860_);
v___x_2868_ = lean_string_append(v___x_2866_, v___x_2867_);
v___x_2869_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2870_ = lean_string_append(v___x_2868_, v___x_2869_);
v___x_2871_ = 1;
v___x_2872_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*1, v___x_2871_);
lean_inc_ref(v___y_2853_);
v___x_2873_ = lean_apply_2(v___y_2853_, v___x_2872_, lean_box(0));
v___x_2874_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2867_);
v___x_2875_ = l_Lake_createParentDirs(v___x_2867_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v___x_2876_; 
lean_dec_ref_known(v___x_2875_, 1);
v___x_2876_ = lean_io_rename(v___y_2855_, v___x_2867_);
lean_dec_ref(v___x_2867_);
lean_dec_ref(v___y_2855_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set_tag(v___x_2879_, 1);
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
v___y_2822_ = v___y_2853_;
v___y_2823_ = v_snd_2857_;
v___y_2824_ = v___x_2874_;
v_val_2825_ = v___x_2882_;
goto v___jp_2821_;
}
}
}
else
{
lean_object* v_a_2885_; 
v_a_2885_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2876_, 1);
v___y_2841_ = v___y_2853_;
v___y_2842_ = v_snd_2857_;
v___y_2843_ = v___x_2874_;
v_a_2844_ = v_a_2885_;
goto v___jp_2840_;
}
}
else
{
lean_object* v_a_2886_; 
lean_dec_ref(v___x_2867_);
lean_dec_ref(v___y_2855_);
v_a_2886_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2875_, 1);
v___y_2841_ = v___y_2853_;
v___y_2842_ = v_snd_2857_;
v___y_2843_ = v___x_2874_;
v_a_2844_ = v_a_2886_;
goto v___jp_2840_;
}
}
}
else
{
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___y_2855_);
v___y_2793_ = v_snd_2857_;
goto v___jp_2792_;
}
}
v___jp_2887_:
{
if (lean_obj_tag(v_packagesDir_x3f_2888_) == 1)
{
lean_object* v_val_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; uint8_t v___x_2895_; 
v_val_2891_ = lean_ctor_get(v_packagesDir_x3f_2888_, 0);
lean_inc_n(v_val_2891_, 2);
lean_dec_ref_known(v_packagesDir_x3f_2888_, 1);
lean_inc_ref(v_dir_2848_);
v___x_2892_ = l_Lake_joinRelative(v_dir_2848_, v_val_2891_);
v___x_2893_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2894_ = l_System_FilePath_pathExists(v___x_2892_);
v___x_2895_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2895_ == 0)
{
v___y_2853_ = v___y_2890_;
v___y_2854_ = v_val_2891_;
v___y_2855_ = v___x_2892_;
v_fst_2856_ = v___x_2894_;
v_snd_2857_ = v___y_2889_;
goto v___jp_2852_;
}
else
{
lean_object* v___x_2896_; size_t v___x_2897_; size_t v___x_2898_; lean_object* v___x_2899_; 
v___x_2896_ = lean_box(0);
v___x_2897_ = ((size_t)0ULL);
v___x_2898_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_2899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_2893_, v___x_2897_, v___x_2898_, v___x_2896_, v___y_2890_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_dec_ref_known(v___x_2899_, 1);
v___y_2853_ = v___y_2890_;
v___y_2854_ = v_val_2891_;
v___y_2855_ = v___x_2892_;
v_fst_2856_ = v___x_2894_;
v_snd_2857_ = v___y_2889_;
goto v___jp_2852_;
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec_ref(v___x_2892_);
lean_dec(v_val_2891_);
lean_dec(v___y_2889_);
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_dec(v_packagesDir_x3f_2888_);
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v___y_2889_);
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
return v___x_2910_;
}
}
v___jp_2913_:
{
if (lean_obj_tag(v_fst_2914_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2963_; 
v_a_2916_ = lean_ctor_get(v_fst_2914_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_fst_2914_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2918_ = v_fst_2914_;
v_isShared_2919_ = v_isSharedCheck_2963_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v_fst_2914_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2963_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
if (lean_obj_tag(v_a_2916_) == 11)
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
lean_dec_ref_known(v_a_2916_, 2);
lean_del_object(v___x_2918_);
v___x_2920_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_2921_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_2789_, v_depConfigs_2851_, v___x_2820_, v___x_2920_, v_snd_2915_, v_a_2787_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2943_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2924_ = v___x_2921_;
v_isShared_2925_ = v_isSharedCheck_2943_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2921_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2943_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v_snd_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2941_; 
v_snd_2926_ = lean_ctor_get(v_a_2922_, 1);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_a_2922_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; 
v_unused_2942_ = lean_ctor_get(v_a_2922_, 0);
lean_dec(v_unused_2942_);
v___x_2928_ = v_a_2922_;
v_isShared_2929_ = v_isSharedCheck_2941_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_snd_2926_);
lean_dec(v_a_2922_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2941_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2930_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8));
v___x_2931_ = lean_string_append(v_rootName_2912_, v___x_2930_);
v___x_2932_ = 1;
v___x_2933_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2933_, 0, v___x_2931_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*1, v___x_2932_);
lean_inc_ref(v_a_2787_);
v___x_2934_ = lean_apply_2(v_a_2787_, v___x_2933_, lean_box(0));
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 0, v___x_2934_);
v___x_2936_ = v___x_2928_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_snd_2926_);
v___x_2936_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2938_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v___x_2936_);
v___x_2938_ = v___x_2924_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_2912_);
return v___x_2921_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2789_) == 0)
{
lean_object* v___x_2944_; uint8_t v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
lean_dec_ref_known(v_toUpdate_2789_, 5);
lean_dec(v_snd_2915_);
lean_dec_ref(v_rootName_2912_);
v___x_2944_ = lean_io_error_to_string(v_a_2916_);
v___x_2945_ = 3;
v___x_2946_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2946_, 0, v___x_2944_);
lean_ctor_set_uint8(v___x_2946_, sizeof(void*)*1, v___x_2945_);
lean_inc_ref(v_a_2787_);
v___x_2947_ = lean_apply_2(v_a_2787_, v___x_2946_, lean_box(0));
v___x_2948_ = lean_box(0);
if (v_isShared_2919_ == 0)
{
lean_ctor_set_tag(v___x_2918_, 1);
lean_ctor_set(v___x_2918_, 0, v___x_2948_);
v___x_2950_ = v___x_2918_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
else
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; uint8_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2952_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_2953_ = lean_string_append(v_rootName_2912_, v___x_2952_);
v___x_2954_ = lean_io_error_to_string(v_a_2916_);
v___x_2955_ = lean_string_append(v___x_2953_, v___x_2954_);
lean_dec_ref(v___x_2954_);
v___x_2956_ = 2;
v___x_2957_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set_uint8(v___x_2957_, sizeof(void*)*1, v___x_2956_);
lean_inc_ref(v_a_2787_);
v___x_2958_ = lean_apply_2(v_a_2787_, v___x_2957_, lean_box(0));
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v_snd_2915_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_2959_);
v___x_2961_ = v___x_2918_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v_packagesDir_x3f_2965_; lean_object* v_packages_2966_; lean_object* v___x_2967_; 
lean_dec_ref(v_rootName_2912_);
v_a_2964_ = lean_ctor_get(v_fst_2914_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v_fst_2914_, 1);
v_packagesDir_x3f_2965_ = lean_ctor_get(v_a_2964_, 2);
lean_inc(v_packagesDir_x3f_2965_);
v_packages_2966_ = lean_ctor_get(v_a_2964_, 3);
lean_inc_ref(v_packages_2966_);
lean_dec(v_a_2964_);
lean_inc(v_toUpdate_2789_);
v___x_2967_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_2789_, v_depConfigs_2851_, v___x_2820_, v_packages_2966_, v_snd_2915_, v_a_2787_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
if (lean_obj_tag(v_toUpdate_2789_) == 0)
{
lean_object* v_snd_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v_snd_2969_ = lean_ctor_get(v_a_2968_, 1);
lean_inc(v_snd_2969_);
lean_dec(v_a_2968_);
v___x_2970_ = lean_array_get_size(v_packages_2966_);
v___x_2971_ = lean_nat_dec_lt(v___x_2820_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_dec_ref_known(v_toUpdate_2789_, 5);
lean_dec_ref(v_packages_2966_);
v_packagesDir_x3f_2888_ = v_packagesDir_x3f_2965_;
v___y_2889_ = v_snd_2969_;
v___y_2890_ = v_a_2787_;
goto v___jp_2887_;
}
else
{
lean_object* v___x_2972_; size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v___x_2972_ = lean_box(0);
v___x_2973_ = ((size_t)0ULL);
v___x_2974_ = lean_usize_of_nat(v___x_2970_);
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_2789_, v_packages_2966_, v___x_2973_, v___x_2974_, v___x_2972_, v_snd_2969_);
lean_dec_ref(v_packages_2966_);
lean_dec_ref_known(v_toUpdate_2789_, 5);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v_snd_2977_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref_known(v___x_2975_, 1);
v_snd_2977_ = lean_ctor_get(v_a_2976_, 1);
lean_inc(v_snd_2977_);
lean_dec(v_a_2976_);
v_packagesDir_x3f_2888_ = v_packagesDir_x3f_2965_;
v___y_2889_ = v_snd_2977_;
v___y_2890_ = v_a_2787_;
goto v___jp_2887_;
}
else
{
lean_dec(v_packagesDir_x3f_2965_);
return v___x_2975_;
}
}
}
else
{
lean_object* v_snd_2978_; 
lean_dec_ref(v_packages_2966_);
v_snd_2978_ = lean_ctor_get(v_a_2968_, 1);
lean_inc(v_snd_2978_);
lean_dec(v_a_2968_);
v_packagesDir_x3f_2888_ = v_packagesDir_x3f_2965_;
v___y_2889_ = v_snd_2978_;
v___y_2890_ = v_a_2787_;
goto v___jp_2887_;
}
}
else
{
lean_dec_ref(v_packages_2966_);
lean_dec(v_packagesDir_x3f_2965_);
lean_dec(v_toUpdate_2789_);
return v___x_2967_;
}
}
}
v___jp_2981_:
{
uint8_t v___x_2983_; 
v___x_2983_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2983_ == 0)
{
v_fst_2914_ = v_val_2982_;
v_snd_2915_ = v_a_2790_;
goto v___jp_2913_;
}
else
{
lean_object* v___x_2984_; size_t v___x_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2984_ = lean_box(0);
v___x_2985_ = ((size_t)0ULL);
v___x_2986_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_2980_, v___x_2985_, v___x_2986_, v___x_2984_, v_a_2787_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_dec_ref_known(v___x_2987_, 1);
v_fst_2914_ = v_val_2982_;
v_snd_2915_ = v_a_2790_;
goto v___jp_2913_;
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref(v_val_2982_);
lean_dec_ref(v_rootName_2912_);
lean_dec(v_a_2790_);
lean_dec(v_toUpdate_2789_);
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2987_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_3013_, lean_object* v_ws_3014_, lean_object* v_toUpdate_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_3013_, v_ws_3014_, v_toUpdate_3015_, v_a_3016_);
lean_dec_ref(v_ws_3014_);
lean_dec_ref(v_a_3013_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_a_3019_, lean_object* v_ws_3020_, lean_object* v_rootDeps_3021_){
_start:
{
lean_object* v___y_3024_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; uint8_t v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; uint8_t v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v_lakeEnv_3059_; lean_object* v_lakeArgs_x3f_3060_; lean_object* v_packages_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v_baseName_3064_; lean_object* v_dir_3065_; lean_object* v_config_3066_; lean_object* v___x_3067_; lean_object* v_rootToolchainFile_3068_; uint8_t v___y_3070_; lean_object* v___y_3071_; uint8_t v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3216_; uint8_t v___y_3217_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_lakeEnv_3059_ = lean_ctor_get(v_ws_3020_, 0);
lean_inc_ref(v_lakeEnv_3059_);
v_lakeArgs_x3f_3060_ = lean_ctor_get(v_ws_3020_, 3);
lean_inc(v_lakeArgs_x3f_3060_);
v_packages_3061_ = lean_ctor_get(v_ws_3020_, 4);
lean_inc_ref(v_packages_3061_);
lean_dec_ref(v_ws_3020_);
v___x_3062_ = lean_unsigned_to_nat(0u);
v___x_3063_ = lean_array_fget(v_packages_3061_, v___x_3062_);
lean_dec_ref(v_packages_3061_);
v_baseName_3064_ = lean_ctor_get(v___x_3063_, 1);
lean_inc(v_baseName_3064_);
v_dir_3065_ = lean_ctor_get(v___x_3063_, 4);
lean_inc_ref_n(v_dir_3065_, 3);
v_config_3066_ = lean_ctor_get(v___x_3063_, 6);
lean_inc_ref(v_config_3066_);
lean_dec(v___x_3063_);
v___x_3067_ = l_Lake_toolchainFileName;
v_rootToolchainFile_3068_ = l_Lake_joinRelative(v_dir_3065_, v___x_3067_);
v___x_3221_ = l_System_FilePath_join(v_dir_3065_, v___x_3067_);
v___x_3222_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3221_);
lean_dec_ref(v___x_3221_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3275_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3275_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3275_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v_src_3228_; lean_object* v_tc_x3f_3229_; lean_object* v_clashes_3230_; uint8_t v_fixed_3231_; uint8_t v_fixedToolchain_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
v_fixedToolchain_3254_ = lean_ctor_get_uint8(v_config_3066_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_3066_);
v___x_3255_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___x_3256_ = lean_array_get_size(v_rootDeps_3021_);
v___x_3257_ = lean_nat_dec_lt(v___x_3062_, v___x_3256_);
if (v___x_3257_ == 0)
{
lean_dec_ref(v_dir_3065_);
lean_inc(v_a_3223_);
v_src_3228_ = v_baseName_3064_;
v_tc_x3f_3229_ = v_a_3223_;
v_clashes_3230_ = v___x_3255_;
v_fixed_3231_ = v_fixedToolchain_3254_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3258_; size_t v___x_3259_; size_t v___x_3260_; lean_object* v___x_3261_; 
lean_inc(v_a_3223_);
v___x_3258_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3258_, 0, v_baseName_3064_);
lean_ctor_set(v___x_3258_, 1, v_a_3223_);
lean_ctor_set(v___x_3258_, 2, v___x_3255_);
lean_ctor_set_uint8(v___x_3258_, sizeof(void*)*3, v_fixedToolchain_3254_);
v___x_3259_ = ((size_t)0ULL);
v___x_3260_ = lean_usize_of_nat(v___x_3256_);
v___x_3261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3065_, v_rootDeps_3021_, v___x_3259_, v___x_3260_, v___x_3258_, v_a_3019_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; lean_object* v_src_3263_; lean_object* v_tc_x3f_3264_; lean_object* v_clashes_3265_; uint8_t v_fixed_3266_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v___x_3261_, 1);
v_src_3263_ = lean_ctor_get(v_a_3262_, 0);
lean_inc(v_src_3263_);
v_tc_x3f_3264_ = lean_ctor_get(v_a_3262_, 1);
lean_inc(v_tc_x3f_3264_);
v_clashes_3265_ = lean_ctor_get(v_a_3262_, 2);
lean_inc_ref(v_clashes_3265_);
v_fixed_3266_ = lean_ctor_get_uint8(v_a_3262_, sizeof(void*)*3);
lean_dec(v_a_3262_);
v_src_3228_ = v_src_3263_;
v_tc_x3f_3229_ = v_tc_x3f_3264_;
v_clashes_3230_ = v_clashes_3265_;
v_fixed_3231_ = v_fixed_3266_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_del_object(v___x_3225_);
lean_dec(v_a_3223_);
lean_dec_ref(v_rootToolchainFile_3068_);
lean_dec(v_lakeArgs_x3f_3060_);
lean_dec_ref(v_lakeEnv_3059_);
v_a_3267_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3261_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3261_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
v___jp_3227_:
{
lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3232_ = lean_array_get_size(v_clashes_3230_);
v___x_3233_ = lean_nat_dec_lt(v___x_3062_, v___x_3232_);
if (v___x_3233_ == 0)
{
lean_dec_ref(v_clashes_3230_);
lean_dec(v_src_3228_);
if (lean_obj_tag(v_tc_x3f_3229_) == 1)
{
if (lean_obj_tag(v_a_3223_) == 0)
{
lean_object* v_val_3234_; 
lean_del_object(v___x_3225_);
v_val_3234_ = lean_ctor_get(v_tc_x3f_3229_, 0);
lean_inc(v_val_3234_);
lean_dec_ref_known(v_tc_x3f_3229_, 1);
v___y_3216_ = v_val_3234_;
v___y_3217_ = v___x_3233_;
goto v___jp_3215_;
}
else
{
lean_object* v_val_3235_; lean_object* v_val_3236_; uint8_t v___x_3237_; 
v_val_3235_ = lean_ctor_get(v_tc_x3f_3229_, 0);
lean_inc_n(v_val_3235_, 2);
lean_dec_ref_known(v_tc_x3f_3229_, 1);
v_val_3236_ = lean_ctor_get(v_a_3223_, 0);
lean_inc(v_val_3236_);
lean_dec_ref_known(v_a_3223_, 1);
v___x_3237_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3236_, v_val_3235_);
if (v___x_3237_ == 0)
{
lean_del_object(v___x_3225_);
v___y_3216_ = v_val_3235_;
v___y_3217_ = v___x_3237_;
goto v___jp_3215_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
lean_dec(v_val_3235_);
lean_dec_ref(v_rootToolchainFile_3068_);
lean_dec(v_lakeArgs_x3f_3060_);
lean_dec_ref(v_lakeEnv_3059_);
v___x_3238_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15));
lean_inc_ref(v_a_3019_);
v___x_3239_ = lean_apply_2(v_a_3019_, v___x_3238_, lean_box(0));
v___x_3240_ = lean_box(0);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3240_);
v___x_3242_ = v___x_3225_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_dec(v_tc_x3f_3229_);
lean_dec(v_a_3223_);
lean_dec_ref(v_rootToolchainFile_3068_);
lean_dec(v_lakeArgs_x3f_3060_);
lean_dec_ref(v_lakeEnv_3059_);
v___x_3244_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17));
lean_inc_ref(v_a_3019_);
v___x_3245_ = lean_apply_2(v_a_3019_, v___x_3244_, lean_box(0));
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3245_);
v___x_3247_ = v___x_3225_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
else
{
lean_del_object(v___x_3225_);
lean_dec(v_a_3223_);
lean_dec_ref(v_rootToolchainFile_3068_);
lean_dec(v_lakeArgs_x3f_3060_);
lean_dec_ref(v_lakeEnv_3059_);
if (lean_obj_tag(v_tc_x3f_3229_) == 1)
{
if (v_fixed_3231_ == 0)
{
lean_object* v_val_3249_; lean_object* v___x_3250_; 
v_val_3249_ = lean_ctor_get(v_tc_x3f_3229_, 0);
lean_inc(v_val_3249_);
lean_dec_ref_known(v_tc_x3f_3229_, 1);
v___x_3250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3051_ = v___x_3233_;
v___y_3052_ = v_val_3249_;
v___y_3053_ = v_src_3228_;
v___y_3054_ = v_clashes_3230_;
v___y_3055_ = v___x_3232_;
v___y_3056_ = v___x_3250_;
goto v___jp_3050_;
}
else
{
lean_object* v_val_3251_; lean_object* v___x_3252_; 
v_val_3251_ = lean_ctor_get(v_tc_x3f_3229_, 0);
lean_inc(v_val_3251_);
lean_dec_ref_known(v_tc_x3f_3229_, 1);
v___x_3252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3051_ = v___x_3233_;
v___y_3052_ = v_val_3251_;
v___y_3053_ = v_src_3228_;
v___y_3054_ = v_clashes_3230_;
v___y_3055_ = v___x_3232_;
v___y_3056_ = v___x_3252_;
goto v___jp_3050_;
}
}
else
{
lean_object* v___x_3253_; 
lean_dec(v_tc_x3f_3229_);
lean_dec(v_src_3228_);
v___x_3253_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
v___y_3030_ = v_clashes_3230_;
v___y_3031_ = v___x_3232_;
v___y_3032_ = v___x_3253_;
goto v___jp_3029_;
}
}
}
}
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v_rootToolchainFile_3068_);
lean_dec_ref(v_config_3066_);
lean_dec_ref(v_dir_3065_);
lean_dec(v_baseName_3064_);
lean_dec(v_lakeArgs_x3f_3060_);
lean_dec_ref(v_lakeEnv_3059_);
v_a_3276_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3278_ = v___x_3222_;
v_isShared_3279_ = v_isSharedCheck_3288_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3222_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3288_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; uint8_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3280_ = lean_io_error_to_string(v_a_3276_);
v___x_3281_ = 3;
v___x_3282_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set_uint8(v___x_3282_, sizeof(void*)*1, v___x_3281_);
lean_inc_ref(v_a_3019_);
v___x_3283_ = lean_apply_2(v_a_3019_, v___x_3282_, lean_box(0));
v___x_3284_ = lean_box(0);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3284_);
v___x_3286_ = v___x_3278_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
v___jp_3023_:
{
uint8_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3025_ = 2;
v___x_3026_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3026_, 0, v___y_3024_);
lean_ctor_set_uint8(v___x_3026_, sizeof(void*)*1, v___x_3025_);
lean_inc_ref(v_a_3019_);
v___x_3027_ = lean_apply_2(v_a_3019_, v___x_3026_, lean_box(0));
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
return v___x_3028_;
}
v___jp_3029_:
{
size_t v___x_3033_; size_t v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = ((size_t)0ULL);
v___x_3034_ = lean_usize_of_nat(v___y_3031_);
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3031_, v___y_3030_, v___x_3033_, v___x_3034_, v___y_3032_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3031_);
v___y_3024_ = v___x_3035_;
goto v___jp_3023_;
}
v___jp_3036_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_inc_ref(v___y_3038_);
v___x_3044_ = lean_string_append(v___y_3038_, v___y_3043_);
lean_dec_ref(v___y_3043_);
v___x_3045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3046_ = lean_string_append(v___x_3044_, v___x_3045_);
v___x_3047_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3039_, v___y_3037_);
v___x_3048_ = lean_string_append(v___x_3046_, v___x_3047_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = lean_string_append(v___x_3048_, v___y_3042_);
if (v___y_3037_ == 0)
{
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
v___y_3024_ = v___x_3049_;
goto v___jp_3023_;
}
else
{
v___y_3030_ = v___y_3040_;
v___y_3031_ = v___y_3041_;
v___y_3032_ = v___x_3049_;
goto v___jp_3029_;
}
}
v___jp_3050_:
{
lean_object* v___x_3057_; lean_object* v_toString_3058_; 
v___x_3057_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_3058_ = lean_ctor_get(v___y_3052_, 0);
lean_inc_ref(v_toString_3058_);
lean_dec_ref(v___y_3052_);
v___y_3037_ = v___y_3051_;
v___y_3038_ = v___x_3057_;
v___y_3039_ = v___y_3053_;
v___y_3040_ = v___y_3054_;
v___y_3041_ = v___y_3055_;
v___y_3042_ = v___y_3056_;
v___y_3043_ = v_toString_3058_;
goto v___jp_3036_;
}
v___jp_3069_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_inc_ref(v___y_3071_);
v___x_3074_ = lean_string_append(v___y_3071_, v___y_3073_);
v___x_3075_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_3076_ = lean_string_append(v___x_3074_, v___x_3075_);
v___x_3077_ = 1;
v___x_3078_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set_uint8(v___x_3078_, sizeof(void*)*1, v___x_3077_);
lean_inc_ref(v_a_3019_);
v___x_3079_ = lean_apply_2(v_a_3019_, v___x_3078_, lean_box(0));
v___x_3080_ = l_IO_FS_writeFile(v_rootToolchainFile_3068_, v___y_3073_);
lean_dec_ref(v_rootToolchainFile_3068_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_dec_ref_known(v___x_3080_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_3060_) == 1)
{
lean_object* v_elan_x3f_3081_; 
v_elan_x3f_3081_ = lean_ctor_get(v_lakeEnv_3059_, 2);
if (lean_obj_tag(v_elan_x3f_3081_) == 1)
{
lean_object* v_val_3082_; lean_object* v_val_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v_elan_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_val_3082_ = lean_ctor_get(v_lakeArgs_x3f_3060_, 0);
lean_inc(v_val_3082_);
lean_dec_ref_known(v_lakeArgs_x3f_3060_, 1);
v_val_3083_ = lean_ctor_get(v_elan_x3f_3081_, 0);
v___x_3084_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_3019_);
v___x_3085_ = lean_apply_2(v_a_3019_, v___x_3084_, lean_box(0));
v___x_3086_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_3087_ = lean_ctor_get(v_val_3083_, 1);
lean_inc_ref(v_elan_3087_);
v___x_3088_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_3089_ = lean_unsigned_to_nat(4u);
v___x_3090_ = lean_mk_empty_array_with_capacity(v___x_3089_);
lean_dec_ref(v___x_3090_);
v___x_3091_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_3092_ = lean_array_push(v___x_3091_, v___y_3073_);
v___x_3093_ = lean_array_push(v___x_3092_, v___x_3088_);
v___x_3094_ = l_Array_append___redArg(v___x_3093_, v_val_3082_);
lean_dec(v_val_3082_);
v___x_3095_ = lean_box(0);
v___x_3096_ = l_Lake_Env_noToolchainVars(v_lakeEnv_3059_);
v___x_3097_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3097_, 0, v___x_3086_);
lean_ctor_set(v___x_3097_, 1, v_elan_3087_);
lean_ctor_set(v___x_3097_, 2, v___x_3094_);
lean_ctor_set(v___x_3097_, 3, v___x_3095_);
lean_ctor_set(v___x_3097_, 4, v___x_3096_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*5, v___y_3072_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*5 + 1, v___y_3070_);
v___x_3098_ = lean_io_process_spawn(v___x_3097_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v___x_3100_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3099_);
lean_dec_ref_known(v___x_3098_, 1);
v___x_3100_ = lean_io_process_child_wait(v___x_3086_, v_a_3099_);
lean_dec(v_a_3099_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; uint32_t v___x_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
v___x_3102_ = lean_unbox_uint32(v_a_3101_);
lean_dec(v_a_3101_);
v___x_3103_ = lean_uint32_to_uint8(v___x_3102_);
v___x_3104_ = lean_io_exit(v___x_3103_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3125_; 
v_a_3113_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3115_ = v___x_3104_;
v_isShared_3116_ = v_isSharedCheck_3125_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3104_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3125_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; uint8_t v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3117_ = lean_io_error_to_string(v_a_3113_);
v___x_3118_ = 3;
v___x_3119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3119_, 0, v___x_3117_);
lean_ctor_set_uint8(v___x_3119_, sizeof(void*)*1, v___x_3118_);
lean_inc_ref(v_a_3019_);
v___x_3120_ = lean_apply_2(v_a_3019_, v___x_3119_, lean_box(0));
v___x_3121_ = lean_box(0);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3121_);
v___x_3123_ = v___x_3115_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3138_; 
v_a_3126_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3128_ = v___x_3100_;
v_isShared_3129_ = v_isSharedCheck_3138_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3100_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3138_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; uint8_t v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3130_ = lean_io_error_to_string(v_a_3126_);
v___x_3131_ = 3;
v___x_3132_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3132_, 0, v___x_3130_);
lean_ctor_set_uint8(v___x_3132_, sizeof(void*)*1, v___x_3131_);
lean_inc_ref(v_a_3019_);
v___x_3133_ = lean_apply_2(v_a_3019_, v___x_3132_, lean_box(0));
v___x_3134_ = lean_box(0);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3134_);
v___x_3136_ = v___x_3128_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3151_; 
v_a_3139_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3141_ = v___x_3098_;
v_isShared_3142_ = v_isSharedCheck_3151_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3098_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3151_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; uint8_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3143_ = lean_io_error_to_string(v_a_3139_);
v___x_3144_ = 3;
v___x_3145_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3145_, 0, v___x_3143_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*1, v___x_3144_);
lean_inc_ref(v_a_3019_);
v___x_3146_ = lean_apply_2(v_a_3019_, v___x_3145_, lean_box(0));
v___x_3147_ = lean_box(0);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3147_);
v___x_3149_ = v___x_3141_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; lean_object* v___x_3155_; 
lean_dec_ref_known(v_lakeArgs_x3f_3060_, 1);
lean_dec_ref(v___y_3073_);
lean_dec_ref(v_lakeEnv_3059_);
v___x_3152_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_3019_);
v___x_3153_ = lean_apply_2(v_a_3019_, v___x_3152_, lean_box(0));
v___x_3154_ = 4;
v___x_3155_ = lean_io_exit(v___x_3154_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3155_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3155_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3176_; 
v_a_3164_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3166_ = v___x_3155_;
v_isShared_3167_ = v_isSharedCheck_3176_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3155_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3176_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3168_; uint8_t v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3168_ = lean_io_error_to_string(v_a_3164_);
v___x_3169_ = 3;
v___x_3170_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set_uint8(v___x_3170_, sizeof(void*)*1, v___x_3169_);
lean_inc_ref(v_a_3019_);
v___x_3171_ = lean_apply_2(v_a_3019_, v___x_3170_, lean_box(0));
v___x_3172_ = lean_box(0);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v___x_3172_);
v___x_3174_ = v___x_3166_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; lean_object* v___x_3180_; 
lean_dec_ref(v___y_3073_);
lean_dec(v_lakeArgs_x3f_3060_);
lean_dec_ref(v_lakeEnv_3059_);
v___x_3177_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_3019_);
v___x_3178_ = lean_apply_2(v_a_3019_, v___x_3177_, lean_box(0));
v___x_3179_ = 4;
v___x_3180_ = lean_io_exit(v___x_3179_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3201_; 
v_a_3189_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3191_ = v___x_3180_;
v_isShared_3192_ = v_isSharedCheck_3201_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3180_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3201_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; uint8_t v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_3193_ = lean_io_error_to_string(v_a_3189_);
v___x_3194_ = 3;
v___x_3195_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3195_, 0, v___x_3193_);
lean_ctor_set_uint8(v___x_3195_, sizeof(void*)*1, v___x_3194_);
lean_inc_ref(v_a_3019_);
v___x_3196_ = lean_apply_2(v_a_3019_, v___x_3195_, lean_box(0));
v___x_3197_ = lean_box(0);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3197_);
v___x_3199_ = v___x_3191_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3214_; 
lean_dec_ref(v___y_3073_);
lean_dec(v_lakeArgs_x3f_3060_);
lean_dec_ref(v_lakeEnv_3059_);
v_a_3202_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3204_ = v___x_3080_;
v_isShared_3205_ = v_isSharedCheck_3214_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3080_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3214_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; uint8_t v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3206_ = lean_io_error_to_string(v_a_3202_);
v___x_3207_ = 3;
v___x_3208_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3208_, 0, v___x_3206_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*1, v___x_3207_);
lean_inc_ref(v_a_3019_);
v___x_3209_ = lean_apply_2(v_a_3019_, v___x_3208_, lean_box(0));
v___x_3210_ = lean_box(0);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3210_);
v___x_3212_ = v___x_3204_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
v___jp_3215_:
{
uint8_t v___x_3218_; lean_object* v___x_3219_; lean_object* v_toString_3220_; 
v___x_3218_ = 1;
v___x_3219_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_3220_ = lean_ctor_get(v___y_3216_, 0);
lean_inc_ref(v_toString_3220_);
lean_dec_ref(v___y_3216_);
v___y_3070_ = v___y_3217_;
v___y_3071_ = v___x_3219_;
v___y_3072_ = v___x_3218_;
v___y_3073_ = v_toString_3220_;
goto v___jp_3069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_a_3289_, lean_object* v_ws_3290_, lean_object* v_rootDeps_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_a_3289_, v_ws_3290_, v_rootDeps_3291_);
lean_dec_ref(v_rootDeps_3291_);
lean_dec_ref(v_a_3289_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4_spec__6___redArg(lean_object* v_msg_3294_){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = lean_box(1);
v___x_3296_ = lean_panic_fn_borrowed(v___x_3295_, v_msg_3294_);
return v___x_3296_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3300_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__2));
v___x_3301_ = lean_unsigned_to_nat(35u);
v___x_3302_ = lean_unsigned_to_nat(182u);
v___x_3303_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__1));
v___x_3304_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__0));
v___x_3305_ = l_mkPanicMessageWithDecl(v___x_3304_, v___x_3303_, v___x_3302_, v___x_3301_, v___x_3300_);
return v___x_3305_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__4(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3306_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__2));
v___x_3307_ = lean_unsigned_to_nat(21u);
v___x_3308_ = lean_unsigned_to_nat(183u);
v___x_3309_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__1));
v___x_3310_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__0));
v___x_3311_ = l_mkPanicMessageWithDecl(v___x_3310_, v___x_3309_, v___x_3308_, v___x_3307_, v___x_3306_);
return v___x_3311_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3314_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__6));
v___x_3315_ = lean_unsigned_to_nat(35u);
v___x_3316_ = lean_unsigned_to_nat(276u);
v___x_3317_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__5));
v___x_3318_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__0));
v___x_3319_ = l_mkPanicMessageWithDecl(v___x_3318_, v___x_3317_, v___x_3316_, v___x_3315_, v___x_3314_);
return v___x_3319_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__8(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3320_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__6));
v___x_3321_ = lean_unsigned_to_nat(21u);
v___x_3322_ = lean_unsigned_to_nat(277u);
v___x_3323_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__5));
v___x_3324_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__0));
v___x_3325_ = l_mkPanicMessageWithDecl(v___x_3324_, v___x_3323_, v___x_3322_, v___x_3321_, v___x_3320_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object* v_k_3326_, lean_object* v_v_3327_, lean_object* v_t_3328_){
_start:
{
if (lean_obj_tag(v_t_3328_) == 0)
{
lean_object* v_size_3329_; lean_object* v_k_3330_; lean_object* v_v_3331_; lean_object* v_l_3332_; lean_object* v_r_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3689_; 
v_size_3329_ = lean_ctor_get(v_t_3328_, 0);
v_k_3330_ = lean_ctor_get(v_t_3328_, 1);
v_v_3331_ = lean_ctor_get(v_t_3328_, 2);
v_l_3332_ = lean_ctor_get(v_t_3328_, 3);
v_r_3333_ = lean_ctor_get(v_t_3328_, 4);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_t_3328_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3335_ = v_t_3328_;
v_isShared_3336_ = v_isSharedCheck_3689_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_r_3333_);
lean_inc(v_l_3332_);
lean_inc(v_v_3331_);
lean_inc(v_k_3330_);
lean_inc(v_size_3329_);
lean_dec(v_t_3328_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3689_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
uint8_t v___x_3337_; 
v___x_3337_ = lean_string_compare(v_k_3326_, v_k_3330_);
switch(v___x_3337_)
{
case 0:
{
lean_object* v___x_3338_; 
lean_dec(v_size_3329_);
v___x_3338_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_k_3326_, v_v_3327_, v_l_3332_);
if (lean_obj_tag(v_r_3333_) == 0)
{
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_size_3339_; lean_object* v_size_3340_; lean_object* v_k_3341_; lean_object* v_v_3342_; lean_object* v_l_3343_; lean_object* v_r_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v_size_3339_ = lean_ctor_get(v_r_3333_, 0);
v_size_3340_ = lean_ctor_get(v___x_3338_, 0);
v_k_3341_ = lean_ctor_get(v___x_3338_, 1);
v_v_3342_ = lean_ctor_get(v___x_3338_, 2);
v_l_3343_ = lean_ctor_get(v___x_3338_, 3);
v_r_3344_ = lean_ctor_get(v___x_3338_, 4);
lean_inc(v_r_3344_);
v___x_3345_ = lean_unsigned_to_nat(3u);
v___x_3346_ = lean_nat_mul(v___x_3345_, v_size_3339_);
v___x_3347_ = lean_nat_dec_lt(v___x_3346_, v_size_3340_);
lean_dec(v___x_3346_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3352_; 
lean_dec(v_r_3344_);
v___x_3348_ = lean_unsigned_to_nat(1u);
v___x_3349_ = lean_nat_add(v___x_3348_, v_size_3340_);
v___x_3350_ = lean_nat_add(v___x_3349_, v_size_3339_);
lean_dec(v___x_3349_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 3, v___x_3338_);
lean_ctor_set(v___x_3335_, 0, v___x_3350_);
v___x_3352_ = v___x_3335_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3353_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3353_, 3, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3353_, 4, v_r_3333_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
else
{
lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3425_; 
lean_inc(v_l_3343_);
lean_inc(v_v_3342_);
lean_inc(v_k_3341_);
lean_inc(v_size_3340_);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; lean_object* v_unused_3427_; lean_object* v_unused_3428_; lean_object* v_unused_3429_; lean_object* v_unused_3430_; 
v_unused_3426_ = lean_ctor_get(v___x_3338_, 4);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v___x_3338_, 3);
lean_dec(v_unused_3427_);
v_unused_3428_ = lean_ctor_get(v___x_3338_, 2);
lean_dec(v_unused_3428_);
v_unused_3429_ = lean_ctor_get(v___x_3338_, 1);
lean_dec(v_unused_3429_);
v_unused_3430_ = lean_ctor_get(v___x_3338_, 0);
lean_dec(v_unused_3430_);
v___x_3355_ = v___x_3338_;
v_isShared_3356_ = v_isSharedCheck_3425_;
goto v_resetjp_3354_;
}
else
{
lean_dec(v___x_3338_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3425_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
if (lean_obj_tag(v_l_3343_) == 0)
{
if (lean_obj_tag(v_r_3344_) == 0)
{
lean_object* v_size_3357_; lean_object* v_size_3358_; lean_object* v_k_3359_; lean_object* v_v_3360_; lean_object* v_l_3361_; lean_object* v_r_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v_size_3357_ = lean_ctor_get(v_l_3343_, 0);
v_size_3358_ = lean_ctor_get(v_r_3344_, 0);
v_k_3359_ = lean_ctor_get(v_r_3344_, 1);
v_v_3360_ = lean_ctor_get(v_r_3344_, 2);
v_l_3361_ = lean_ctor_get(v_r_3344_, 3);
v_r_3362_ = lean_ctor_get(v_r_3344_, 4);
v___x_3363_ = lean_unsigned_to_nat(2u);
v___x_3364_ = lean_nat_mul(v___x_3363_, v_size_3357_);
v___x_3365_ = lean_nat_dec_lt(v_size_3358_, v___x_3364_);
lean_dec(v___x_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3395_; 
lean_inc(v_r_3362_);
lean_inc(v_l_3361_);
lean_inc(v_v_3360_);
lean_inc(v_k_3359_);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_r_3344_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; lean_object* v_unused_3397_; lean_object* v_unused_3398_; lean_object* v_unused_3399_; lean_object* v_unused_3400_; 
v_unused_3396_ = lean_ctor_get(v_r_3344_, 4);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_r_3344_, 3);
lean_dec(v_unused_3397_);
v_unused_3398_ = lean_ctor_get(v_r_3344_, 2);
lean_dec(v_unused_3398_);
v_unused_3399_ = lean_ctor_get(v_r_3344_, 1);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v_r_3344_, 0);
lean_dec(v_unused_3400_);
v___x_3367_ = v_r_3344_;
v_isShared_3368_ = v_isSharedCheck_3395_;
goto v_resetjp_3366_;
}
else
{
lean_dec(v_r_3344_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3395_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___x_3383_; lean_object* v___y_3385_; 
v___x_3369_ = lean_unsigned_to_nat(1u);
v___x_3370_ = lean_nat_add(v___x_3369_, v_size_3340_);
lean_dec(v_size_3340_);
v___x_3371_ = lean_nat_add(v___x_3370_, v_size_3339_);
lean_dec(v___x_3370_);
v___x_3383_ = lean_nat_add(v___x_3369_, v_size_3357_);
if (lean_obj_tag(v_l_3361_) == 0)
{
lean_object* v_size_3393_; 
v_size_3393_ = lean_ctor_get(v_l_3361_, 0);
lean_inc(v_size_3393_);
v___y_3385_ = v_size_3393_;
goto v___jp_3384_;
}
else
{
lean_object* v___x_3394_; 
v___x_3394_ = lean_unsigned_to_nat(0u);
v___y_3385_ = v___x_3394_;
goto v___jp_3384_;
}
v___jp_3372_:
{
lean_object* v___x_3376_; lean_object* v___x_3378_; 
v___x_3376_ = lean_nat_add(v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec(v___y_3374_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 4, v_r_3333_);
lean_ctor_set(v___x_3367_, 3, v_r_3362_);
lean_ctor_set(v___x_3367_, 2, v_v_3331_);
lean_ctor_set(v___x_3367_, 1, v_k_3330_);
lean_ctor_set(v___x_3367_, 0, v___x_3376_);
v___x_3378_ = v___x_3367_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3382_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3382_, 3, v_r_3362_);
lean_ctor_set(v_reuseFailAlloc_3382_, 4, v_r_3333_);
v___x_3378_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3380_; 
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 4, v___x_3378_);
lean_ctor_set(v___x_3355_, 3, v___y_3373_);
lean_ctor_set(v___x_3355_, 2, v_v_3360_);
lean_ctor_set(v___x_3355_, 1, v_k_3359_);
lean_ctor_set(v___x_3355_, 0, v___x_3371_);
v___x_3380_ = v___x_3355_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3371_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_k_3359_);
lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_v_3360_);
lean_ctor_set(v_reuseFailAlloc_3381_, 3, v___y_3373_);
lean_ctor_set(v_reuseFailAlloc_3381_, 4, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
v___jp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3386_ = lean_nat_add(v___x_3383_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec(v___x_3383_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v_l_3361_);
lean_ctor_set(v___x_3335_, 3, v_l_3343_);
lean_ctor_set(v___x_3335_, 2, v_v_3342_);
lean_ctor_set(v___x_3335_, 1, v_k_3341_);
lean_ctor_set(v___x_3335_, 0, v___x_3386_);
v___x_3388_ = v___x_3335_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_k_3341_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_v_3342_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_l_3343_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_l_3361_);
v___x_3388_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3389_; 
v___x_3389_ = lean_nat_add(v___x_3369_, v_size_3339_);
if (lean_obj_tag(v_r_3362_) == 0)
{
lean_object* v_size_3390_; 
v_size_3390_ = lean_ctor_get(v_r_3362_, 0);
lean_inc(v_size_3390_);
v___y_3373_ = v___x_3388_;
v___y_3374_ = v___x_3389_;
v___y_3375_ = v_size_3390_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3391_; 
v___x_3391_ = lean_unsigned_to_nat(0u);
v___y_3373_ = v___x_3388_;
v___y_3374_ = v___x_3389_;
v___y_3375_ = v___x_3391_;
goto v___jp_3372_;
}
}
}
}
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
lean_del_object(v___x_3335_);
v___x_3401_ = lean_unsigned_to_nat(1u);
v___x_3402_ = lean_nat_add(v___x_3401_, v_size_3340_);
lean_dec(v_size_3340_);
v___x_3403_ = lean_nat_add(v___x_3402_, v_size_3339_);
lean_dec(v___x_3402_);
v___x_3404_ = lean_nat_add(v___x_3401_, v_size_3339_);
v___x_3405_ = lean_nat_add(v___x_3404_, v_size_3358_);
lean_dec(v___x_3404_);
lean_inc_ref(v_r_3333_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 4, v_r_3333_);
lean_ctor_set(v___x_3355_, 3, v_r_3344_);
lean_ctor_set(v___x_3355_, 2, v_v_3331_);
lean_ctor_set(v___x_3355_, 1, v_k_3330_);
lean_ctor_set(v___x_3355_, 0, v___x_3405_);
v___x_3407_ = v___x_3355_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3420_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3420_, 3, v_r_3344_);
lean_ctor_set(v_reuseFailAlloc_3420_, 4, v_r_3333_);
v___x_3407_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
v_isSharedCheck_3414_ = !lean_is_exclusive(v_r_3333_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; lean_object* v_unused_3416_; lean_object* v_unused_3417_; lean_object* v_unused_3418_; lean_object* v_unused_3419_; 
v_unused_3415_ = lean_ctor_get(v_r_3333_, 4);
lean_dec(v_unused_3415_);
v_unused_3416_ = lean_ctor_get(v_r_3333_, 3);
lean_dec(v_unused_3416_);
v_unused_3417_ = lean_ctor_get(v_r_3333_, 2);
lean_dec(v_unused_3417_);
v_unused_3418_ = lean_ctor_get(v_r_3333_, 1);
lean_dec(v_unused_3418_);
v_unused_3419_ = lean_ctor_get(v_r_3333_, 0);
lean_dec(v_unused_3419_);
v___x_3409_ = v_r_3333_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_dec(v_r_3333_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 4, v___x_3407_);
lean_ctor_set(v___x_3409_, 3, v_l_3343_);
lean_ctor_set(v___x_3409_, 2, v_v_3342_);
lean_ctor_set(v___x_3409_, 1, v_k_3341_);
lean_ctor_set(v___x_3409_, 0, v___x_3403_);
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3403_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_k_3341_);
lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_v_3342_);
lean_ctor_set(v_reuseFailAlloc_3413_, 3, v_l_3343_);
lean_ctor_set(v_reuseFailAlloc_3413_, 4, v___x_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_dec_ref_known(v_l_3343_, 5);
lean_del_object(v___x_3355_);
lean_dec(v_v_3342_);
lean_dec(v_k_3341_);
lean_dec(v_size_3340_);
lean_dec_ref_known(v_r_3333_, 5);
lean_del_object(v___x_3335_);
lean_dec(v_v_3331_);
lean_dec(v_k_3330_);
v___x_3421_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__3);
v___x_3422_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4_spec__6___redArg(v___x_3421_);
return v___x_3422_;
}
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_del_object(v___x_3355_);
lean_dec(v_r_3344_);
lean_dec(v_v_3342_);
lean_dec(v_k_3341_);
lean_dec(v_size_3340_);
lean_dec_ref_known(v_r_3333_, 5);
lean_del_object(v___x_3335_);
lean_dec(v_v_3331_);
lean_dec(v_k_3330_);
v___x_3423_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__4);
v___x_3424_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4_spec__6___redArg(v___x_3423_);
return v___x_3424_;
}
}
}
}
else
{
lean_object* v_size_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v_size_3431_ = lean_ctor_get(v_r_3333_, 0);
v___x_3432_ = lean_unsigned_to_nat(1u);
v___x_3433_ = lean_nat_add(v___x_3432_, v_size_3431_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 3, v___x_3338_);
lean_ctor_set(v___x_3335_, 0, v___x_3433_);
v___x_3435_ = v___x_3335_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3436_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3436_, 3, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3436_, 4, v_r_3333_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
else
{
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_l_3437_; 
v_l_3437_ = lean_ctor_get(v___x_3338_, 3);
if (lean_obj_tag(v_l_3437_) == 0)
{
lean_object* v_r_3438_; 
lean_inc_ref(v_l_3437_);
v_r_3438_ = lean_ctor_get(v___x_3338_, 4);
lean_inc(v_r_3438_);
if (lean_obj_tag(v_r_3438_) == 0)
{
lean_object* v_size_3439_; lean_object* v_k_3440_; lean_object* v_v_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3455_; 
v_size_3439_ = lean_ctor_get(v___x_3338_, 0);
v_k_3440_ = lean_ctor_get(v___x_3338_, 1);
v_v_3441_ = lean_ctor_get(v___x_3338_, 2);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3455_ == 0)
{
lean_object* v_unused_3456_; lean_object* v_unused_3457_; 
v_unused_3456_ = lean_ctor_get(v___x_3338_, 4);
lean_dec(v_unused_3456_);
v_unused_3457_ = lean_ctor_get(v___x_3338_, 3);
lean_dec(v_unused_3457_);
v___x_3443_ = v___x_3338_;
v_isShared_3444_ = v_isSharedCheck_3455_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_v_3441_);
lean_inc(v_k_3440_);
lean_inc(v_size_3439_);
lean_dec(v___x_3338_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3455_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v_size_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v_size_3445_ = lean_ctor_get(v_r_3438_, 0);
v___x_3446_ = lean_unsigned_to_nat(1u);
v___x_3447_ = lean_nat_add(v___x_3446_, v_size_3439_);
lean_dec(v_size_3439_);
v___x_3448_ = lean_nat_add(v___x_3446_, v_size_3445_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 4, v_r_3333_);
lean_ctor_set(v___x_3443_, 3, v_r_3438_);
lean_ctor_set(v___x_3443_, 2, v_v_3331_);
lean_ctor_set(v___x_3443_, 1, v_k_3330_);
lean_ctor_set(v___x_3443_, 0, v___x_3448_);
v___x_3450_ = v___x_3443_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3454_, 3, v_r_3438_);
lean_ctor_set(v_reuseFailAlloc_3454_, 4, v_r_3333_);
v___x_3450_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v___x_3450_);
lean_ctor_set(v___x_3335_, 3, v_l_3437_);
lean_ctor_set(v___x_3335_, 2, v_v_3441_);
lean_ctor_set(v___x_3335_, 1, v_k_3440_);
lean_ctor_set(v___x_3335_, 0, v___x_3447_);
v___x_3452_ = v___x_3335_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_k_3440_);
lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_v_3441_);
lean_ctor_set(v_reuseFailAlloc_3453_, 3, v_l_3437_);
lean_ctor_set(v_reuseFailAlloc_3453_, 4, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
else
{
lean_object* v_k_3458_; lean_object* v_v_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3471_; 
v_k_3458_ = lean_ctor_get(v___x_3338_, 1);
v_v_3459_ = lean_ctor_get(v___x_3338_, 2);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; lean_object* v_unused_3473_; lean_object* v_unused_3474_; 
v_unused_3472_ = lean_ctor_get(v___x_3338_, 4);
lean_dec(v_unused_3472_);
v_unused_3473_ = lean_ctor_get(v___x_3338_, 3);
lean_dec(v_unused_3473_);
v_unused_3474_ = lean_ctor_get(v___x_3338_, 0);
lean_dec(v_unused_3474_);
v___x_3461_ = v___x_3338_;
v_isShared_3462_ = v_isSharedCheck_3471_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_v_3459_);
lean_inc(v_k_3458_);
lean_dec(v___x_3338_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3471_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3463_ = lean_unsigned_to_nat(3u);
v___x_3464_ = lean_unsigned_to_nat(1u);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 3, v_r_3438_);
lean_ctor_set(v___x_3461_, 2, v_v_3331_);
lean_ctor_set(v___x_3461_, 1, v_k_3330_);
lean_ctor_set(v___x_3461_, 0, v___x_3464_);
v___x_3466_ = v___x_3461_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3470_, 3, v_r_3438_);
lean_ctor_set(v_reuseFailAlloc_3470_, 4, v_r_3438_);
v___x_3466_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3468_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v___x_3466_);
lean_ctor_set(v___x_3335_, 3, v_l_3437_);
lean_ctor_set(v___x_3335_, 2, v_v_3459_);
lean_ctor_set(v___x_3335_, 1, v_k_3458_);
lean_ctor_set(v___x_3335_, 0, v___x_3463_);
v___x_3468_ = v___x_3335_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_k_3458_);
lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_v_3459_);
lean_ctor_set(v_reuseFailAlloc_3469_, 3, v_l_3437_);
lean_ctor_set(v_reuseFailAlloc_3469_, 4, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
else
{
lean_object* v_r_3475_; 
v_r_3475_ = lean_ctor_get(v___x_3338_, 4);
lean_inc(v_r_3475_);
if (lean_obj_tag(v_r_3475_) == 0)
{
lean_object* v_k_3476_; lean_object* v_v_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3501_; 
lean_inc(v_l_3437_);
v_k_3476_ = lean_ctor_get(v___x_3338_, 1);
v_v_3477_ = lean_ctor_get(v___x_3338_, 2);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3501_ == 0)
{
lean_object* v_unused_3502_; lean_object* v_unused_3503_; lean_object* v_unused_3504_; 
v_unused_3502_ = lean_ctor_get(v___x_3338_, 4);
lean_dec(v_unused_3502_);
v_unused_3503_ = lean_ctor_get(v___x_3338_, 3);
lean_dec(v_unused_3503_);
v_unused_3504_ = lean_ctor_get(v___x_3338_, 0);
lean_dec(v_unused_3504_);
v___x_3479_ = v___x_3338_;
v_isShared_3480_ = v_isSharedCheck_3501_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_v_3477_);
lean_inc(v_k_3476_);
lean_dec(v___x_3338_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3501_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v_k_3481_; lean_object* v_v_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3497_; 
v_k_3481_ = lean_ctor_get(v_r_3475_, 1);
v_v_3482_ = lean_ctor_get(v_r_3475_, 2);
v_isSharedCheck_3497_ = !lean_is_exclusive(v_r_3475_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; lean_object* v_unused_3499_; lean_object* v_unused_3500_; 
v_unused_3498_ = lean_ctor_get(v_r_3475_, 4);
lean_dec(v_unused_3498_);
v_unused_3499_ = lean_ctor_get(v_r_3475_, 3);
lean_dec(v_unused_3499_);
v_unused_3500_ = lean_ctor_get(v_r_3475_, 0);
lean_dec(v_unused_3500_);
v___x_3484_ = v_r_3475_;
v_isShared_3485_ = v_isSharedCheck_3497_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_v_3482_);
lean_inc(v_k_3481_);
lean_dec(v_r_3475_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3497_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3489_; 
v___x_3486_ = lean_unsigned_to_nat(3u);
v___x_3487_ = lean_unsigned_to_nat(1u);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 4, v_l_3437_);
lean_ctor_set(v___x_3484_, 3, v_l_3437_);
lean_ctor_set(v___x_3484_, 2, v_v_3477_);
lean_ctor_set(v___x_3484_, 1, v_k_3476_);
lean_ctor_set(v___x_3484_, 0, v___x_3487_);
v___x_3489_ = v___x_3484_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3487_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3496_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3496_, 3, v_l_3437_);
lean_ctor_set(v_reuseFailAlloc_3496_, 4, v_l_3437_);
v___x_3489_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
lean_object* v___x_3491_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 4, v_l_3437_);
lean_ctor_set(v___x_3479_, 2, v_v_3331_);
lean_ctor_set(v___x_3479_, 1, v_k_3330_);
lean_ctor_set(v___x_3479_, 0, v___x_3487_);
v___x_3491_ = v___x_3479_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3487_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_l_3437_);
lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_l_3437_);
v___x_3491_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3493_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v___x_3491_);
lean_ctor_set(v___x_3335_, 3, v___x_3489_);
lean_ctor_set(v___x_3335_, 2, v_v_3482_);
lean_ctor_set(v___x_3335_, 1, v_k_3481_);
lean_ctor_set(v___x_3335_, 0, v___x_3486_);
v___x_3493_ = v___x_3335_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_k_3481_);
lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_v_3482_);
lean_ctor_set(v_reuseFailAlloc_3494_, 3, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3494_, 4, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
v___x_3505_ = lean_unsigned_to_nat(2u);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v_r_3475_);
lean_ctor_set(v___x_3335_, 3, v___x_3338_);
lean_ctor_set(v___x_3335_, 0, v___x_3505_);
v___x_3507_ = v___x_3335_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3508_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3508_, 3, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3508_, 4, v_r_3475_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3509_ = lean_unsigned_to_nat(1u);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v___x_3338_);
lean_ctor_set(v___x_3335_, 3, v___x_3338_);
lean_ctor_set(v___x_3335_, 0, v___x_3509_);
v___x_3511_ = v___x_3335_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3512_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3512_, 3, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3512_, 4, v___x_3338_);
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
case 1:
{
lean_object* v___x_3514_; 
lean_dec(v_v_3331_);
lean_dec(v_k_3330_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 2, v_v_3327_);
lean_ctor_set(v___x_3335_, 1, v_k_3326_);
v___x_3514_ = v___x_3335_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_size_3329_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3515_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3515_, 3, v_l_3332_);
lean_ctor_set(v_reuseFailAlloc_3515_, 4, v_r_3333_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
default: 
{
lean_object* v___x_3516_; 
lean_dec(v_size_3329_);
v___x_3516_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_k_3326_, v_v_3327_, v_r_3333_);
if (lean_obj_tag(v_l_3332_) == 0)
{
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_size_3517_; lean_object* v_size_3518_; lean_object* v_k_3519_; lean_object* v_v_3520_; lean_object* v_l_3521_; lean_object* v_r_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v_size_3517_ = lean_ctor_get(v_l_3332_, 0);
v_size_3518_ = lean_ctor_get(v___x_3516_, 0);
v_k_3519_ = lean_ctor_get(v___x_3516_, 1);
v_v_3520_ = lean_ctor_get(v___x_3516_, 2);
v_l_3521_ = lean_ctor_get(v___x_3516_, 3);
lean_inc(v_l_3521_);
v_r_3522_ = lean_ctor_get(v___x_3516_, 4);
v___x_3523_ = lean_unsigned_to_nat(3u);
v___x_3524_ = lean_nat_mul(v___x_3523_, v_size_3517_);
v___x_3525_ = lean_nat_dec_lt(v___x_3524_, v_size_3518_);
lean_dec(v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3530_; 
lean_dec(v_l_3521_);
v___x_3526_ = lean_unsigned_to_nat(1u);
v___x_3527_ = lean_nat_add(v___x_3526_, v_size_3517_);
v___x_3528_ = lean_nat_add(v___x_3527_, v_size_3518_);
lean_dec(v___x_3527_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v___x_3516_);
lean_ctor_set(v___x_3335_, 0, v___x_3528_);
v___x_3530_ = v___x_3335_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3531_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3531_, 3, v_l_3332_);
lean_ctor_set(v_reuseFailAlloc_3531_, 4, v___x_3516_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
else
{
lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3601_; 
lean_inc(v_r_3522_);
lean_inc(v_v_3520_);
lean_inc(v_k_3519_);
lean_inc(v_size_3518_);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3601_ == 0)
{
lean_object* v_unused_3602_; lean_object* v_unused_3603_; lean_object* v_unused_3604_; lean_object* v_unused_3605_; lean_object* v_unused_3606_; 
v_unused_3602_ = lean_ctor_get(v___x_3516_, 4);
lean_dec(v_unused_3602_);
v_unused_3603_ = lean_ctor_get(v___x_3516_, 3);
lean_dec(v_unused_3603_);
v_unused_3604_ = lean_ctor_get(v___x_3516_, 2);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v___x_3516_, 1);
lean_dec(v_unused_3605_);
v_unused_3606_ = lean_ctor_get(v___x_3516_, 0);
lean_dec(v_unused_3606_);
v___x_3533_ = v___x_3516_;
v_isShared_3534_ = v_isSharedCheck_3601_;
goto v_resetjp_3532_;
}
else
{
lean_dec(v___x_3516_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3601_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
if (lean_obj_tag(v_l_3521_) == 0)
{
if (lean_obj_tag(v_r_3522_) == 0)
{
lean_object* v_size_3535_; lean_object* v_k_3536_; lean_object* v_v_3537_; lean_object* v_l_3538_; lean_object* v_r_3539_; lean_object* v_size_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v_size_3535_ = lean_ctor_get(v_l_3521_, 0);
v_k_3536_ = lean_ctor_get(v_l_3521_, 1);
v_v_3537_ = lean_ctor_get(v_l_3521_, 2);
v_l_3538_ = lean_ctor_get(v_l_3521_, 3);
v_r_3539_ = lean_ctor_get(v_l_3521_, 4);
v_size_3540_ = lean_ctor_get(v_r_3522_, 0);
v___x_3541_ = lean_unsigned_to_nat(2u);
v___x_3542_ = lean_nat_mul(v___x_3541_, v_size_3540_);
v___x_3543_ = lean_nat_dec_lt(v_size_3535_, v___x_3542_);
lean_dec(v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3572_; 
lean_inc(v_r_3539_);
lean_inc(v_l_3538_);
lean_inc(v_v_3537_);
lean_inc(v_k_3536_);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_l_3521_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; lean_object* v_unused_3574_; lean_object* v_unused_3575_; lean_object* v_unused_3576_; lean_object* v_unused_3577_; 
v_unused_3573_ = lean_ctor_get(v_l_3521_, 4);
lean_dec(v_unused_3573_);
v_unused_3574_ = lean_ctor_get(v_l_3521_, 3);
lean_dec(v_unused_3574_);
v_unused_3575_ = lean_ctor_get(v_l_3521_, 2);
lean_dec(v_unused_3575_);
v_unused_3576_ = lean_ctor_get(v_l_3521_, 1);
lean_dec(v_unused_3576_);
v_unused_3577_ = lean_ctor_get(v_l_3521_, 0);
lean_dec(v_unused_3577_);
v___x_3545_ = v_l_3521_;
v_isShared_3546_ = v_isSharedCheck_3572_;
goto v_resetjp_3544_;
}
else
{
lean_dec(v_l_3521_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3572_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3562_; 
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_add(v___x_3547_, v_size_3517_);
v___x_3549_ = lean_nat_add(v___x_3548_, v_size_3518_);
lean_dec(v_size_3518_);
if (lean_obj_tag(v_l_3538_) == 0)
{
lean_object* v_size_3570_; 
v_size_3570_ = lean_ctor_get(v_l_3538_, 0);
lean_inc(v_size_3570_);
v___y_3562_ = v_size_3570_;
goto v___jp_3561_;
}
else
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_unsigned_to_nat(0u);
v___y_3562_ = v___x_3571_;
goto v___jp_3561_;
}
v___jp_3550_:
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3554_ = lean_nat_add(v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec(v___y_3552_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 4, v_r_3522_);
lean_ctor_set(v___x_3545_, 3, v_r_3539_);
lean_ctor_set(v___x_3545_, 2, v_v_3520_);
lean_ctor_set(v___x_3545_, 1, v_k_3519_);
lean_ctor_set(v___x_3545_, 0, v___x_3554_);
v___x_3556_ = v___x_3545_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_k_3519_);
lean_ctor_set(v_reuseFailAlloc_3560_, 2, v_v_3520_);
lean_ctor_set(v_reuseFailAlloc_3560_, 3, v_r_3539_);
lean_ctor_set(v_reuseFailAlloc_3560_, 4, v_r_3522_);
v___x_3556_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3558_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 4, v___x_3556_);
lean_ctor_set(v___x_3533_, 3, v___y_3551_);
lean_ctor_set(v___x_3533_, 2, v_v_3537_);
lean_ctor_set(v___x_3533_, 1, v_k_3536_);
lean_ctor_set(v___x_3533_, 0, v___x_3549_);
v___x_3558_ = v___x_3533_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3559_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3559_, 3, v___y_3551_);
lean_ctor_set(v_reuseFailAlloc_3559_, 4, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
v___jp_3561_:
{
lean_object* v___x_3563_; lean_object* v___x_3565_; 
v___x_3563_ = lean_nat_add(v___x_3548_, v___y_3562_);
lean_dec(v___y_3562_);
lean_dec(v___x_3548_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v_l_3538_);
lean_ctor_set(v___x_3335_, 0, v___x_3563_);
v___x_3565_ = v___x_3335_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3569_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3569_, 3, v_l_3332_);
lean_ctor_set(v_reuseFailAlloc_3569_, 4, v_l_3538_);
v___x_3565_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_nat_add(v___x_3547_, v_size_3540_);
if (lean_obj_tag(v_r_3539_) == 0)
{
lean_object* v_size_3567_; 
v_size_3567_ = lean_ctor_get(v_r_3539_, 0);
lean_inc(v_size_3567_);
v___y_3551_ = v___x_3565_;
v___y_3552_ = v___x_3566_;
v___y_3553_ = v_size_3567_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3568_; 
v___x_3568_ = lean_unsigned_to_nat(0u);
v___y_3551_ = v___x_3565_;
v___y_3552_ = v___x_3566_;
v___y_3553_ = v___x_3568_;
goto v___jp_3550_;
}
}
}
}
}
else
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3583_; 
lean_del_object(v___x_3335_);
v___x_3578_ = lean_unsigned_to_nat(1u);
v___x_3579_ = lean_nat_add(v___x_3578_, v_size_3517_);
v___x_3580_ = lean_nat_add(v___x_3579_, v_size_3518_);
lean_dec(v_size_3518_);
v___x_3581_ = lean_nat_add(v___x_3579_, v_size_3535_);
lean_dec(v___x_3579_);
lean_inc_ref(v_l_3332_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 4, v_l_3521_);
lean_ctor_set(v___x_3533_, 3, v_l_3332_);
lean_ctor_set(v___x_3533_, 2, v_v_3331_);
lean_ctor_set(v___x_3533_, 1, v_k_3330_);
lean_ctor_set(v___x_3533_, 0, v___x_3581_);
v___x_3583_ = v___x_3533_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_l_3332_);
lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_l_3521_);
v___x_3583_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
v_isSharedCheck_3590_ = !lean_is_exclusive(v_l_3332_);
if (v_isSharedCheck_3590_ == 0)
{
lean_object* v_unused_3591_; lean_object* v_unused_3592_; lean_object* v_unused_3593_; lean_object* v_unused_3594_; lean_object* v_unused_3595_; 
v_unused_3591_ = lean_ctor_get(v_l_3332_, 4);
lean_dec(v_unused_3591_);
v_unused_3592_ = lean_ctor_get(v_l_3332_, 3);
lean_dec(v_unused_3592_);
v_unused_3593_ = lean_ctor_get(v_l_3332_, 2);
lean_dec(v_unused_3593_);
v_unused_3594_ = lean_ctor_get(v_l_3332_, 1);
lean_dec(v_unused_3594_);
v_unused_3595_ = lean_ctor_get(v_l_3332_, 0);
lean_dec(v_unused_3595_);
v___x_3585_ = v_l_3332_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_dec(v_l_3332_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 4, v_r_3522_);
lean_ctor_set(v___x_3585_, 3, v___x_3583_);
lean_ctor_set(v___x_3585_, 2, v_v_3520_);
lean_ctor_set(v___x_3585_, 1, v_k_3519_);
lean_ctor_set(v___x_3585_, 0, v___x_3580_);
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3580_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_k_3519_);
lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_v_3520_);
lean_ctor_set(v_reuseFailAlloc_3589_, 3, v___x_3583_);
lean_ctor_set(v_reuseFailAlloc_3589_, 4, v_r_3522_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_dec_ref_known(v_l_3521_, 5);
lean_del_object(v___x_3533_);
lean_dec(v_v_3520_);
lean_dec(v_k_3519_);
lean_dec(v_size_3518_);
lean_dec_ref_known(v_l_3332_, 5);
lean_del_object(v___x_3335_);
lean_dec(v_v_3331_);
lean_dec(v_k_3330_);
v___x_3597_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__7);
v___x_3598_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4_spec__6___redArg(v___x_3597_);
return v___x_3598_;
}
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_del_object(v___x_3533_);
lean_dec(v_r_3522_);
lean_dec(v_v_3520_);
lean_dec(v_k_3519_);
lean_dec(v_size_3518_);
lean_dec_ref_known(v_l_3332_, 5);
lean_del_object(v___x_3335_);
lean_dec(v_v_3331_);
lean_dec(v_k_3330_);
v___x_3599_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___closed__8);
v___x_3600_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4_spec__6___redArg(v___x_3599_);
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_size_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3611_; 
v_size_3607_ = lean_ctor_get(v_l_3332_, 0);
v___x_3608_ = lean_unsigned_to_nat(1u);
v___x_3609_ = lean_nat_add(v___x_3608_, v_size_3607_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v___x_3516_);
lean_ctor_set(v___x_3335_, 0, v___x_3609_);
v___x_3611_ = v___x_3335_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_l_3332_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v___x_3516_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
else
{
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_l_3613_; 
v_l_3613_ = lean_ctor_get(v___x_3516_, 3);
lean_inc(v_l_3613_);
if (lean_obj_tag(v_l_3613_) == 0)
{
lean_object* v_r_3614_; 
v_r_3614_ = lean_ctor_get(v___x_3516_, 4);
lean_inc(v_r_3614_);
if (lean_obj_tag(v_r_3614_) == 0)
{
lean_object* v_size_3615_; lean_object* v_k_3616_; lean_object* v_v_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3631_; 
v_size_3615_ = lean_ctor_get(v___x_3516_, 0);
v_k_3616_ = lean_ctor_get(v___x_3516_, 1);
v_v_3617_ = lean_ctor_get(v___x_3516_, 2);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; lean_object* v_unused_3633_; 
v_unused_3632_ = lean_ctor_get(v___x_3516_, 4);
lean_dec(v_unused_3632_);
v_unused_3633_ = lean_ctor_get(v___x_3516_, 3);
lean_dec(v_unused_3633_);
v___x_3619_ = v___x_3516_;
v_isShared_3620_ = v_isSharedCheck_3631_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_v_3617_);
lean_inc(v_k_3616_);
lean_inc(v_size_3615_);
lean_dec(v___x_3516_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3631_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v_size_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
v_size_3621_ = lean_ctor_get(v_l_3613_, 0);
v___x_3622_ = lean_unsigned_to_nat(1u);
v___x_3623_ = lean_nat_add(v___x_3622_, v_size_3615_);
lean_dec(v_size_3615_);
v___x_3624_ = lean_nat_add(v___x_3622_, v_size_3621_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 4, v_l_3613_);
lean_ctor_set(v___x_3619_, 3, v_l_3332_);
lean_ctor_set(v___x_3619_, 2, v_v_3331_);
lean_ctor_set(v___x_3619_, 1, v_k_3330_);
lean_ctor_set(v___x_3619_, 0, v___x_3624_);
v___x_3626_ = v___x_3619_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3624_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_l_3332_);
lean_ctor_set(v_reuseFailAlloc_3630_, 4, v_l_3613_);
v___x_3626_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3628_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v_r_3614_);
lean_ctor_set(v___x_3335_, 3, v___x_3626_);
lean_ctor_set(v___x_3335_, 2, v_v_3617_);
lean_ctor_set(v___x_3335_, 1, v_k_3616_);
lean_ctor_set(v___x_3335_, 0, v___x_3623_);
v___x_3628_ = v___x_3335_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_k_3616_);
lean_ctor_set(v_reuseFailAlloc_3629_, 2, v_v_3617_);
lean_ctor_set(v_reuseFailAlloc_3629_, 3, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3629_, 4, v_r_3614_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_object* v_k_3634_; lean_object* v_v_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3659_; 
v_k_3634_ = lean_ctor_get(v___x_3516_, 1);
v_v_3635_ = lean_ctor_get(v___x_3516_, 2);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; lean_object* v_unused_3661_; lean_object* v_unused_3662_; 
v_unused_3660_ = lean_ctor_get(v___x_3516_, 4);
lean_dec(v_unused_3660_);
v_unused_3661_ = lean_ctor_get(v___x_3516_, 3);
lean_dec(v_unused_3661_);
v_unused_3662_ = lean_ctor_get(v___x_3516_, 0);
lean_dec(v_unused_3662_);
v___x_3637_ = v___x_3516_;
v_isShared_3638_ = v_isSharedCheck_3659_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_v_3635_);
lean_inc(v_k_3634_);
lean_dec(v___x_3516_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3659_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v_k_3639_; lean_object* v_v_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3655_; 
v_k_3639_ = lean_ctor_get(v_l_3613_, 1);
v_v_3640_ = lean_ctor_get(v_l_3613_, 2);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_l_3613_);
if (v_isSharedCheck_3655_ == 0)
{
lean_object* v_unused_3656_; lean_object* v_unused_3657_; lean_object* v_unused_3658_; 
v_unused_3656_ = lean_ctor_get(v_l_3613_, 4);
lean_dec(v_unused_3656_);
v_unused_3657_ = lean_ctor_get(v_l_3613_, 3);
lean_dec(v_unused_3657_);
v_unused_3658_ = lean_ctor_get(v_l_3613_, 0);
lean_dec(v_unused_3658_);
v___x_3642_ = v_l_3613_;
v_isShared_3643_ = v_isSharedCheck_3655_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_v_3640_);
lean_inc(v_k_3639_);
lean_dec(v_l_3613_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3655_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3644_ = lean_unsigned_to_nat(3u);
v___x_3645_ = lean_unsigned_to_nat(1u);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 4, v_r_3614_);
lean_ctor_set(v___x_3642_, 3, v_r_3614_);
lean_ctor_set(v___x_3642_, 2, v_v_3331_);
lean_ctor_set(v___x_3642_, 1, v_k_3330_);
lean_ctor_set(v___x_3642_, 0, v___x_3645_);
v___x_3647_ = v___x_3642_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3654_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3654_, 3, v_r_3614_);
lean_ctor_set(v_reuseFailAlloc_3654_, 4, v_r_3614_);
v___x_3647_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3649_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 3, v_r_3614_);
lean_ctor_set(v___x_3637_, 0, v___x_3645_);
v___x_3649_ = v___x_3637_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_k_3634_);
lean_ctor_set(v_reuseFailAlloc_3653_, 2, v_v_3635_);
lean_ctor_set(v_reuseFailAlloc_3653_, 3, v_r_3614_);
lean_ctor_set(v_reuseFailAlloc_3653_, 4, v_r_3614_);
v___x_3649_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3651_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v___x_3649_);
lean_ctor_set(v___x_3335_, 3, v___x_3647_);
lean_ctor_set(v___x_3335_, 2, v_v_3640_);
lean_ctor_set(v___x_3335_, 1, v_k_3639_);
lean_ctor_set(v___x_3335_, 0, v___x_3644_);
v___x_3651_ = v___x_3335_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3644_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_k_3639_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_v_3640_);
lean_ctor_set(v_reuseFailAlloc_3652_, 3, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3652_, 4, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3663_; 
v_r_3663_ = lean_ctor_get(v___x_3516_, 4);
lean_inc(v_r_3663_);
if (lean_obj_tag(v_r_3663_) == 0)
{
lean_object* v_k_3664_; lean_object* v_v_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3677_; 
v_k_3664_ = lean_ctor_get(v___x_3516_, 1);
v_v_3665_ = lean_ctor_get(v___x_3516_, 2);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; lean_object* v_unused_3679_; lean_object* v_unused_3680_; 
v_unused_3678_ = lean_ctor_get(v___x_3516_, 4);
lean_dec(v_unused_3678_);
v_unused_3679_ = lean_ctor_get(v___x_3516_, 3);
lean_dec(v_unused_3679_);
v_unused_3680_ = lean_ctor_get(v___x_3516_, 0);
lean_dec(v_unused_3680_);
v___x_3667_ = v___x_3516_;
v_isShared_3668_ = v_isSharedCheck_3677_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_v_3665_);
lean_inc(v_k_3664_);
lean_dec(v___x_3516_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3677_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3669_ = lean_unsigned_to_nat(3u);
v___x_3670_ = lean_unsigned_to_nat(1u);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 4, v_l_3613_);
lean_ctor_set(v___x_3667_, 2, v_v_3331_);
lean_ctor_set(v___x_3667_, 1, v_k_3330_);
lean_ctor_set(v___x_3667_, 0, v___x_3670_);
v___x_3672_ = v___x_3667_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_l_3613_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_l_3613_);
v___x_3672_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3674_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v_r_3663_);
lean_ctor_set(v___x_3335_, 3, v___x_3672_);
lean_ctor_set(v___x_3335_, 2, v_v_3665_);
lean_ctor_set(v___x_3335_, 1, v_k_3664_);
lean_ctor_set(v___x_3335_, 0, v___x_3669_);
v___x_3674_ = v___x_3335_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3675_, 3, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3675_, 4, v_r_3663_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
else
{
lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3681_ = lean_unsigned_to_nat(2u);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v___x_3516_);
lean_ctor_set(v___x_3335_, 3, v_r_3663_);
lean_ctor_set(v___x_3335_, 0, v___x_3681_);
v___x_3683_ = v___x_3335_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3684_, 3, v_r_3663_);
lean_ctor_set(v_reuseFailAlloc_3684_, 4, v___x_3516_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v___x_3685_; lean_object* v___x_3687_; 
v___x_3685_ = lean_unsigned_to_nat(1u);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v___x_3516_);
lean_ctor_set(v___x_3335_, 3, v___x_3516_);
lean_ctor_set(v___x_3335_, 0, v___x_3685_);
v___x_3687_ = v___x_3335_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3688_, 3, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3688_, 4, v___x_3516_);
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
}
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3690_ = lean_unsigned_to_nat(1u);
v___x_3691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
lean_ctor_set(v___x_3691_, 1, v_k_3326_);
lean_ctor_set(v___x_3691_, 2, v_v_3327_);
lean_ctor_set(v___x_3691_, 3, v_t_3328_);
lean_ctor_set(v___x_3691_, 4, v_t_3328_);
return v___x_3691_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5_spec__8(lean_object* v_init_3692_, lean_object* v_x_3693_){
_start:
{
if (lean_obj_tag(v_x_3693_) == 0)
{
lean_object* v_k_3694_; lean_object* v_v_3695_; lean_object* v_l_3696_; lean_object* v_r_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v_k_3694_ = lean_ctor_get(v_x_3693_, 1);
lean_inc(v_k_3694_);
v_v_3695_ = lean_ctor_get(v_x_3693_, 2);
lean_inc(v_v_3695_);
v_l_3696_ = lean_ctor_get(v_x_3693_, 3);
lean_inc(v_l_3696_);
v_r_3697_ = lean_ctor_get(v_x_3693_, 4);
lean_inc(v_r_3697_);
lean_dec_ref_known(v_x_3693_, 5);
v___x_3698_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5_spec__8(v_init_3692_, v_l_3696_);
v___x_3699_ = 1;
v___x_3700_ = l_Lean_Name_toString(v_k_3694_, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3701_, 0, v_v_3695_);
v___x_3702_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v___x_3700_, v___x_3701_, v___x_3698_);
v_init_3692_ = v___x_3702_;
v_x_3693_ = v_r_3697_;
goto _start;
}
else
{
return v_init_3692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_m_3704_){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = lean_box(1);
v___x_3706_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5_spec__8(v___x_3705_, v_m_3704_);
v___x_3707_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v_baseName_3710_, lean_object* v_ws_3711_, lean_object* v___x_3712_, lean_object* v_dep_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v_name_3717_; lean_object* v_opts_3718_; uint8_t v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v_name_3717_ = lean_ctor_get(v_dep_3713_, 0);
v_opts_3718_ = lean_ctor_get(v_dep_3713_, 4);
v___x_3719_ = 0;
v___x_3720_ = l_Lean_Name_toString(v_baseName_3710_, v___x_3719_);
v___x_3721_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3722_ = lean_string_append(v___x_3720_, v___x_3721_);
v___x_3723_ = 1;
lean_inc(v_name_3717_);
v___x_3724_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3717_, v___x_3723_);
v___x_3725_ = lean_string_append(v___x_3722_, v___x_3724_);
lean_dec_ref(v___x_3724_);
v___x_3726_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3727_ = lean_string_append(v___x_3725_, v___x_3726_);
lean_inc(v_opts_3718_);
v___x_3728_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_opts_3718_);
v___x_3729_ = lean_unsigned_to_nat(80u);
v___x_3730_ = l_Lean_Json_pretty(v___x_3728_, v___x_3729_);
v___x_3731_ = lean_string_append(v___x_3727_, v___x_3730_);
lean_dec_ref(v___x_3730_);
v___x_3732_ = 0;
v___x_3733_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set_uint8(v___x_3733_, sizeof(void*)*1, v___x_3732_);
lean_inc_ref(v___y_3715_);
v___x_3734_ = lean_apply_2(v___y_3715_, v___x_3733_, lean_box(0));
v___x_3735_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3711_, v___x_3712_, v_dep_3713_, v___y_3714_, v___y_3715_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v_baseName_3736_, lean_object* v_ws_3737_, lean_object* v___x_3738_, lean_object* v_dep_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v_baseName_3736_, v_ws_3737_, v___x_3738_, v_dep_3739_, v___y_3740_, v___y_3741_);
lean_dec_ref(v___y_3741_);
return v_res_3743_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg___lam__0(lean_object* v___x_3744_, lean_object* v_x_3745_){
_start:
{
lean_object* v_baseName_3746_; lean_object* v_name_3747_; uint8_t v___x_3748_; 
v_baseName_3746_ = lean_ctor_get(v_x_3745_, 1);
v_name_3747_ = lean_ctor_get(v___x_3744_, 0);
v___x_3748_ = lean_name_eq(v_baseName_3746_, v_name_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___x_3749_, lean_object* v_x_3750_){
_start:
{
uint8_t v_res_3751_; lean_object* v_r_3752_; 
v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg___lam__0(v___x_3749_, v_x_3750_);
lean_dec_ref(v_x_3750_);
lean_dec_ref(v___x_3749_);
v_r_3752_ = lean_box(v_res_3751_);
return v_r_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg(lean_object* v_pkg_3753_, lean_object* v_leanOpts_3754_, uint8_t v_reconfigure_3755_, lean_object* v_as_3756_, size_t v_i_3757_, size_t v_stop_3758_, lean_object* v_b_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
uint8_t v___x_3763_; 
v___x_3763_ = lean_usize_dec_eq(v_i_3757_, v_stop_3758_);
if (v___x_3763_ == 0)
{
lean_object* v_ws_3764_; lean_object* v_depIdxs_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3862_; 
v_ws_3764_ = lean_ctor_get(v_b_3759_, 0);
v_depIdxs_3765_ = lean_ctor_get(v_b_3759_, 1);
v_isSharedCheck_3862_ = !lean_is_exclusive(v_b_3759_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3767_ = v_b_3759_;
v_isShared_3768_ = v_isSharedCheck_3862_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_depIdxs_3765_);
lean_inc(v_ws_3764_);
lean_dec(v_b_3759_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3862_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v_packages_3769_; size_t v___x_3770_; size_t v___x_3771_; lean_object* v___x_3772_; lean_object* v___f_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v_packages_3769_ = lean_ctor_get(v_ws_3764_, 4);
v___x_3770_ = ((size_t)1ULL);
v___x_3771_ = lean_usize_sub(v_i_3757_, v___x_3770_);
v___x_3772_ = lean_array_uget_borrowed(v_as_3756_, v___x_3771_);
lean_inc(v___x_3772_);
v___f_3773_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3773_, 0, v___x_3772_);
v___x_3774_ = lean_unsigned_to_nat(0u);
v___x_3775_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3773_, v_packages_3769_, v___x_3774_);
if (lean_obj_tag(v___x_3775_) == 1)
{
lean_object* v_val_3776_; lean_object* v___x_3777_; lean_object* v___x_3779_; 
v_val_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_val_3776_);
lean_dec_ref_known(v___x_3775_, 1);
v___x_3777_ = lean_array_push(v_depIdxs_3765_, v_val_3776_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v___x_3777_);
v___x_3779_ = v___x_3767_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_ws_3764_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
v_i_3757_ = v___x_3771_;
v_b_3759_ = v___x_3779_;
goto _start;
}
}
else
{
lean_object* v_baseName_3782_; lean_object* v_name_3783_; lean_object* v_opts_3784_; uint8_t v___x_3785_; 
lean_dec(v___x_3775_);
v_baseName_3782_ = lean_ctor_get(v_pkg_3753_, 1);
v_name_3783_ = lean_ctor_get(v___x_3772_, 0);
v_opts_3784_ = lean_ctor_get(v___x_3772_, 4);
v___x_3785_ = lean_name_eq(v_baseName_3782_, v_name_3783_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; 
lean_inc_ref(v___y_3761_);
lean_inc_ref(v_ws_3764_);
lean_inc(v___x_3772_);
lean_inc_ref(v_pkg_3753_);
v___x_3786_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_3753_, v___x_3772_, v_ws_3764_, v___y_3760_, v___y_3761_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3845_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3845_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3845_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v_fst_3791_; lean_object* v_snd_3792_; lean_object* v___x_3793_; lean_object* v_wsIdx_3794_; lean_object* v___x_3795_; 
v_fst_3791_ = lean_ctor_get(v_a_3787_, 0);
lean_inc(v_fst_3791_);
v_snd_3792_ = lean_ctor_get(v_a_3787_, 1);
lean_inc(v_snd_3792_);
lean_dec(v_a_3787_);
v___x_3793_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_3794_ = lean_array_get_size(v_packages_3769_);
lean_inc_ref(v_leanOpts_3754_);
lean_inc(v_opts_3784_);
v___x_3795_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_3764_, v_fst_3791_, v_opts_3784_, v_leanOpts_3754_, v_reconfigure_3755_, v___x_3793_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v_a_3797_; lean_object* v___x_3798_; lean_object* v___x_3800_; 
lean_del_object(v___x_3789_);
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
v_a_3797_ = lean_ctor_get(v___x_3795_, 1);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3795_, 2);
v___x_3798_ = lean_array_push(v_depIdxs_3765_, v_wsIdx_3794_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v___x_3798_);
lean_ctor_set(v___x_3767_, 0, v_a_3796_);
v___x_3800_ = v___x_3767_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3796_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3801_ = lean_array_get_size(v_a_3797_);
v___x_3802_ = lean_nat_dec_lt(v___x_3774_, v___x_3801_);
if (v___x_3802_ == 0)
{
lean_dec(v_a_3797_);
v_i_3757_ = v___x_3771_;
v_b_3759_ = v___x_3800_;
v___y_3760_ = v_snd_3792_;
goto _start;
}
else
{
lean_object* v___x_3804_; size_t v___x_3805_; size_t v___x_3806_; lean_object* v___x_3807_; 
v___x_3804_ = lean_box(0);
v___x_3805_ = ((size_t)0ULL);
v___x_3806_ = lean_usize_of_nat(v___x_3801_);
v___x_3807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3797_, v___x_3805_, v___x_3806_, v___x_3804_, v___y_3761_);
lean_dec(v_a_3797_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_dec_ref_known(v___x_3807_, 1);
v_i_3757_ = v___x_3771_;
v_b_3759_ = v___x_3800_;
v___y_3760_ = v_snd_3792_;
goto _start;
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec_ref(v___x_3800_);
lean_dec(v_snd_3792_);
lean_dec_ref(v_leanOpts_3754_);
lean_dec_ref(v_pkg_3753_);
v_a_3809_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3807_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3807_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3819_; uint8_t v___x_3820_; 
lean_dec(v_snd_3792_);
lean_del_object(v___x_3767_);
lean_dec_ref(v_depIdxs_3765_);
lean_dec_ref(v_leanOpts_3754_);
lean_dec_ref(v_pkg_3753_);
v_a_3818_ = lean_ctor_get(v___x_3795_, 1);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3795_, 2);
v___x_3819_ = lean_array_get_size(v_a_3818_);
v___x_3820_ = lean_nat_dec_lt(v___x_3774_, v___x_3819_);
if (v___x_3820_ == 0)
{
lean_object* v___x_3821_; lean_object* v___x_3823_; 
lean_dec(v_a_3818_);
v___x_3821_ = lean_box(0);
if (v_isShared_3790_ == 0)
{
lean_ctor_set_tag(v___x_3789_, 1);
lean_ctor_set(v___x_3789_, 0, v___x_3821_);
v___x_3823_ = v___x_3789_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
else
{
lean_object* v___x_3825_; size_t v___x_3826_; size_t v___x_3827_; lean_object* v___x_3828_; 
lean_del_object(v___x_3789_);
v___x_3825_ = lean_box(0);
v___x_3826_ = ((size_t)0ULL);
v___x_3827_ = lean_usize_of_nat(v___x_3819_);
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3818_, v___x_3826_, v___x_3827_, v___x_3825_, v___y_3761_);
lean_dec(v_a_3818_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3835_ == 0)
{
lean_object* v_unused_3836_; 
v_unused_3836_ = lean_ctor_get(v___x_3828_, 0);
lean_dec(v_unused_3836_);
v___x_3830_ = v___x_3828_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_dec(v___x_3828_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
lean_ctor_set_tag(v___x_3830_, 1);
lean_ctor_set(v___x_3830_, 0, v___x_3825_);
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3825_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
v_a_3837_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3828_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3828_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_del_object(v___x_3767_);
lean_dec_ref(v_depIdxs_3765_);
lean_dec_ref(v_ws_3764_);
lean_dec_ref(v_leanOpts_3754_);
lean_dec_ref(v_pkg_3753_);
v_a_3846_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3786_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3786_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
else
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
lean_inc(v_baseName_3782_);
lean_del_object(v___x_3767_);
lean_dec_ref(v_depIdxs_3765_);
lean_dec_ref(v_ws_3764_);
lean_dec(v___y_3760_);
lean_dec_ref(v_leanOpts_3754_);
lean_dec_ref(v_pkg_3753_);
v___x_3854_ = l_Lean_Name_toString(v_baseName_3782_, v___x_3763_);
v___x_3855_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_3856_ = lean_string_append(v___x_3854_, v___x_3855_);
v___x_3857_ = 3;
v___x_3858_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set_uint8(v___x_3858_, sizeof(void*)*1, v___x_3857_);
lean_inc_ref(v___y_3761_);
v___x_3859_ = lean_apply_2(v___y_3761_, v___x_3858_, lean_box(0));
v___x_3860_ = lean_box(0);
v___x_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
return v___x_3861_;
}
}
}
}
else
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
lean_dec_ref(v_leanOpts_3754_);
lean_dec_ref(v_pkg_3753_);
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v_b_3759_);
lean_ctor_set(v___x_3863_, 1, v___y_3760_);
v___x_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
return v___x_3864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg___boxed(lean_object* v_pkg_3865_, lean_object* v_leanOpts_3866_, lean_object* v_reconfigure_3867_, lean_object* v_as_3868_, lean_object* v_i_3869_, lean_object* v_stop_3870_, lean_object* v_b_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
uint8_t v_reconfigure_boxed_3875_; size_t v_i_boxed_3876_; size_t v_stop_boxed_3877_; lean_object* v_res_3878_; 
v_reconfigure_boxed_3875_ = lean_unbox(v_reconfigure_3867_);
v_i_boxed_3876_ = lean_unbox_usize(v_i_3869_);
lean_dec(v_i_3869_);
v_stop_boxed_3877_ = lean_unbox_usize(v_stop_3870_);
lean_dec(v_stop_3870_);
v_res_3878_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg(v_pkg_3865_, v_leanOpts_3866_, v_reconfigure_boxed_3875_, v_as_3868_, v_i_boxed_3876_, v_stop_boxed_3877_, v_b_3871_, v___y_3872_, v___y_3873_);
lean_dec_ref(v___y_3873_);
lean_dec_ref(v_as_3868_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___redArg(lean_object* v_leanOpts_3879_, uint8_t v_reconfigure_3880_, lean_object* v_ws_3881_, lean_object* v_i_3882_, lean_object* v_next_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v_packages_3887_; lean_object* v_pkg_3888_; lean_object* v_ws_3890_; lean_object* v_depIdxs_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v_____x_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v_depConfigs_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v_s_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v_packages_3887_ = lean_ctor_get(v_ws_3881_, 4);
v_pkg_3888_ = lean_array_fget(v_packages_3887_, v_i_3882_);
lean_dec(v_i_3882_);
v_depConfigs_3909_ = lean_ctor_get(v_pkg_3888_, 12);
v___x_3910_ = lean_array_get_size(v_depConfigs_3909_);
v___x_3911_ = lean_mk_empty_array_with_capacity(v___x_3910_);
lean_inc_ref(v___x_3911_);
lean_inc_ref(v_ws_3881_);
v_s_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_3912_, 0, v_ws_3881_);
lean_ctor_set(v_s_3912_, 1, v___x_3911_);
v___x_3913_ = lean_unsigned_to_nat(0u);
v___x_3914_ = lean_nat_dec_le(v___x_3910_, v___x_3910_);
if (v___x_3914_ == 0)
{
uint8_t v___x_3915_; 
v___x_3915_ = lean_nat_dec_lt(v___x_3913_, v___x_3910_);
if (v___x_3915_ == 0)
{
lean_object* v_ws_3916_; lean_object* v_packages_3917_; lean_object* v___x_3918_; uint8_t v___x_3919_; 
lean_dec_ref_known(v_s_3912_, 2);
v_ws_3916_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_3881_, v_pkg_3888_, v___x_3911_);
v_packages_3917_ = lean_ctor_get(v_ws_3916_, 4);
v___x_3918_ = lean_array_get_size(v_packages_3917_);
v___x_3919_ = lean_nat_dec_lt(v_next_3883_, v___x_3918_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
lean_dec(v_next_3883_);
lean_dec_ref(v_leanOpts_3879_);
v___x_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3920_, 0, v_ws_3916_);
lean_ctor_set(v___x_3920_, 1, v___y_3884_);
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
return v___x_3921_;
}
else
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = lean_unsigned_to_nat(1u);
v___x_3923_ = lean_nat_add(v_next_3883_, v___x_3922_);
v_ws_3881_ = v_ws_3916_;
v_i_3882_ = v_next_3883_;
v_next_3883_ = v___x_3923_;
goto _start;
}
}
else
{
size_t v___x_3925_; size_t v___x_3926_; lean_object* v___x_3927_; 
lean_dec_ref(v___x_3911_);
lean_dec_ref(v_ws_3881_);
v___x_3925_ = lean_usize_of_nat(v___x_3910_);
v___x_3926_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_3879_);
lean_inc(v_pkg_3888_);
v___x_3927_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg(v_pkg_3888_, v_leanOpts_3879_, v_reconfigure_3880_, v_depConfigs_3909_, v___x_3925_, v___x_3926_, v_s_3912_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v_fst_3929_; lean_object* v_snd_3930_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3928_);
lean_dec_ref_known(v___x_3927_, 1);
v_fst_3929_ = lean_ctor_get(v_a_3928_, 0);
lean_inc(v_fst_3929_);
v_snd_3930_ = lean_ctor_get(v_a_3928_, 1);
lean_inc(v_snd_3930_);
lean_dec(v_a_3928_);
v_____x_3904_ = v_fst_3929_;
v___y_3905_ = v_snd_3930_;
v___y_3906_ = v___y_3885_;
goto v___jp_3903_;
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec(v_pkg_3888_);
lean_dec(v_next_3883_);
lean_dec_ref(v_leanOpts_3879_);
v_a_3931_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3927_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3927_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
else
{
uint8_t v___x_3939_; 
v___x_3939_ = lean_nat_dec_lt(v___x_3913_, v___x_3910_);
if (v___x_3939_ == 0)
{
lean_dec_ref_known(v_s_3912_, 2);
v_ws_3890_ = v_ws_3881_;
v_depIdxs_3891_ = v___x_3911_;
v___y_3892_ = v___y_3884_;
v___y_3893_ = v___y_3885_;
goto v___jp_3889_;
}
else
{
size_t v___x_3940_; size_t v___x_3941_; lean_object* v___x_3942_; 
lean_dec_ref(v___x_3911_);
lean_dec_ref(v_ws_3881_);
v___x_3940_ = lean_usize_of_nat(v___x_3910_);
v___x_3941_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_3879_);
lean_inc(v_pkg_3888_);
v___x_3942_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg(v_pkg_3888_, v_leanOpts_3879_, v_reconfigure_3880_, v_depConfigs_3909_, v___x_3940_, v___x_3941_, v_s_3912_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v_fst_3944_; lean_object* v_snd_3945_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
v_fst_3944_ = lean_ctor_get(v_a_3943_, 0);
lean_inc(v_fst_3944_);
v_snd_3945_ = lean_ctor_get(v_a_3943_, 1);
lean_inc(v_snd_3945_);
lean_dec(v_a_3943_);
v_____x_3904_ = v_fst_3944_;
v___y_3905_ = v_snd_3945_;
v___y_3906_ = v___y_3885_;
goto v___jp_3903_;
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec(v_pkg_3888_);
lean_dec(v_next_3883_);
lean_dec_ref(v_leanOpts_3879_);
v_a_3946_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3942_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3942_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
v___jp_3889_:
{
lean_object* v_ws_3894_; lean_object* v_packages_3895_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
v_ws_3894_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_3890_, v_pkg_3888_, v_depIdxs_3891_);
v_packages_3895_ = lean_ctor_get(v_ws_3894_, 4);
v___x_3896_ = lean_array_get_size(v_packages_3895_);
v___x_3897_ = lean_nat_dec_lt(v_next_3883_, v___x_3896_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
lean_dec(v_next_3883_);
lean_dec_ref(v_leanOpts_3879_);
v___x_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3898_, 0, v_ws_3894_);
lean_ctor_set(v___x_3898_, 1, v___y_3892_);
v___x_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
return v___x_3899_;
}
else
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = lean_unsigned_to_nat(1u);
v___x_3901_ = lean_nat_add(v_next_3883_, v___x_3900_);
v_ws_3881_ = v_ws_3894_;
v_i_3882_ = v_next_3883_;
v_next_3883_ = v___x_3901_;
v___y_3884_ = v___y_3892_;
v___y_3885_ = v___y_3893_;
goto _start;
}
}
v___jp_3903_:
{
lean_object* v_ws_3907_; lean_object* v_depIdxs_3908_; 
v_ws_3907_ = lean_ctor_get(v_____x_3904_, 0);
lean_inc_ref(v_ws_3907_);
v_depIdxs_3908_ = lean_ctor_get(v_____x_3904_, 1);
lean_inc_ref(v_depIdxs_3908_);
lean_dec_ref(v_____x_3904_);
v_ws_3890_ = v_ws_3907_;
v_depIdxs_3891_ = v_depIdxs_3908_;
v___y_3892_ = v___y_3905_;
v___y_3893_ = v___y_3906_;
goto v___jp_3889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___redArg___boxed(lean_object* v_leanOpts_3954_, lean_object* v_reconfigure_3955_, lean_object* v_ws_3956_, lean_object* v_i_3957_, lean_object* v_next_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
uint8_t v_reconfigure_boxed_3962_; lean_object* v_res_3963_; 
v_reconfigure_boxed_3962_ = lean_unbox(v_reconfigure_3955_);
v_res_3963_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___redArg(v_leanOpts_3954_, v_reconfigure_boxed_3962_, v_ws_3956_, v_i_3957_, v_next_3958_, v___y_3959_, v___y_3960_);
lean_dec_ref(v___y_3960_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___redArg(lean_object* v_n_3964_, lean_object* v_f_3965_, lean_object* v_xs_3966_, lean_object* v_k_3967_, lean_object* v_acc_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
uint8_t v___x_3972_; 
v___x_3972_ = lean_nat_dec_lt(v_k_3967_, v_n_3964_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec(v_k_3967_);
lean_dec_ref(v_f_3965_);
v___x_3973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3973_, 0, v_acc_3968_);
lean_ctor_set(v___x_3973_, 1, v___y_3969_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = lean_array_fget_borrowed(v_xs_3966_, v_k_3967_);
lean_inc_ref(v_f_3965_);
lean_inc_ref(v___y_3970_);
lean_inc(v___x_3975_);
v___x_3976_ = lean_apply_4(v_f_3965_, v___x_3975_, v___y_3969_, v___y_3970_, lean_box(0));
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v_fst_3978_; lean_object* v_snd_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v_fst_3978_ = lean_ctor_get(v_a_3977_, 0);
lean_inc(v_fst_3978_);
v_snd_3979_ = lean_ctor_get(v_a_3977_, 1);
lean_inc(v_snd_3979_);
lean_dec(v_a_3977_);
v___x_3980_ = lean_unsigned_to_nat(1u);
v___x_3981_ = lean_nat_add(v_k_3967_, v___x_3980_);
lean_dec(v_k_3967_);
v___x_3982_ = lean_array_push(v_acc_3968_, v_fst_3978_);
v_k_3967_ = v___x_3981_;
v_acc_3968_ = v___x_3982_;
v___y_3969_ = v_snd_3979_;
goto _start;
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec_ref(v_acc_3968_);
lean_dec(v_k_3967_);
lean_dec_ref(v_f_3965_);
v_a_3984_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3976_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3976_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___redArg___boxed(lean_object* v_n_3992_, lean_object* v_f_3993_, lean_object* v_xs_3994_, lean_object* v_k_3995_, lean_object* v_acc_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___redArg(v_n_3992_, v_f_3993_, v_xs_3994_, v_k_3995_, v_acc_3996_, v___y_3997_, v___y_3998_);
lean_dec_ref(v___y_3998_);
lean_dec_ref(v_xs_3994_);
lean_dec(v_n_3992_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_upperBound_4001_, lean_object* v_fst_4002_, lean_object* v___x_4003_, lean_object* v_leanOpts_4004_, lean_object* v_a_4005_, lean_object* v_b_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v_fst_4011_; lean_object* v_snd_4012_; uint8_t v___x_4016_; 
v___x_4016_ = lean_nat_dec_lt(v_a_4005_, v_upperBound_4001_);
if (v___x_4016_ == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_dec(v_a_4005_);
lean_dec_ref(v_leanOpts_4004_);
v___x_4017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4017_, 0, v_b_4006_);
lean_ctor_set(v___x_4017_, 1, v___y_4007_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
else
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = lean_array_fget_borrowed(v_fst_4002_, v_a_4005_);
lean_inc(v___x_4019_);
v___x_4020_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_4019_, v___y_4007_, v___y_4008_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4074_; 
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4023_ = v___x_4020_;
v_isShared_4024_ = v_isSharedCheck_4074_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4020_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4074_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v_snd_4025_; lean_object* v___x_4026_; lean_object* v_opts_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_snd_4025_ = lean_ctor_get(v_a_4021_, 1);
lean_inc(v_snd_4025_);
lean_dec(v_a_4021_);
v___x_4026_ = lean_array_fget_borrowed(v___x_4003_, v_a_4005_);
v_opts_4027_ = lean_ctor_get(v___x_4026_, 4);
v___x_4028_ = lean_unsigned_to_nat(0u);
v___x_4029_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_4004_);
lean_inc(v_opts_4027_);
lean_inc(v___x_4019_);
v___x_4030_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_4006_, v___x_4019_, v_opts_4027_, v_leanOpts_4004_, v___x_4016_, v___x_4029_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v_a_4032_; lean_object* v___x_4033_; uint8_t v___x_4034_; 
lean_del_object(v___x_4023_);
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
v_a_4032_ = lean_ctor_get(v___x_4030_, 1);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4030_, 2);
v___x_4033_ = lean_array_get_size(v_a_4032_);
v___x_4034_ = lean_nat_dec_lt(v___x_4028_, v___x_4033_);
if (v___x_4034_ == 0)
{
lean_dec(v_a_4032_);
v_fst_4011_ = v_a_4031_;
v_snd_4012_ = v_snd_4025_;
goto v___jp_4010_;
}
else
{
lean_object* v___x_4035_; size_t v___x_4036_; size_t v___x_4037_; lean_object* v___x_4038_; 
v___x_4035_ = lean_box(0);
v___x_4036_ = ((size_t)0ULL);
v___x_4037_ = lean_usize_of_nat(v___x_4033_);
v___x_4038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4032_, v___x_4036_, v___x_4037_, v___x_4035_, v___y_4008_);
lean_dec(v_a_4032_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_dec_ref_known(v___x_4038_, 1);
v_fst_4011_ = v_a_4031_;
v_snd_4012_ = v_snd_4025_;
goto v___jp_4010_;
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec(v_a_4031_);
lean_dec(v_snd_4025_);
lean_dec(v_a_4005_);
lean_dec_ref(v_leanOpts_4004_);
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4038_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4038_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4048_; uint8_t v___x_4049_; 
lean_dec(v_snd_4025_);
lean_dec(v_a_4005_);
lean_dec_ref(v_leanOpts_4004_);
v_a_4047_ = lean_ctor_get(v___x_4030_, 1);
lean_inc(v_a_4047_);
lean_dec_ref_known(v___x_4030_, 2);
v___x_4048_ = lean_array_get_size(v_a_4047_);
v___x_4049_ = lean_nat_dec_lt(v___x_4028_, v___x_4048_);
if (v___x_4049_ == 0)
{
lean_object* v___x_4050_; lean_object* v___x_4052_; 
lean_dec(v_a_4047_);
v___x_4050_ = lean_box(0);
if (v_isShared_4024_ == 0)
{
lean_ctor_set_tag(v___x_4023_, 1);
lean_ctor_set(v___x_4023_, 0, v___x_4050_);
v___x_4052_ = v___x_4023_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
else
{
lean_object* v___x_4054_; size_t v___x_4055_; size_t v___x_4056_; lean_object* v___x_4057_; 
lean_del_object(v___x_4023_);
v___x_4054_ = lean_box(0);
v___x_4055_ = ((size_t)0ULL);
v___x_4056_ = lean_usize_of_nat(v___x_4048_);
v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4047_, v___x_4055_, v___x_4056_, v___x_4054_, v___y_4008_);
lean_dec(v_a_4047_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; 
v_unused_4065_ = lean_ctor_get(v___x_4057_, 0);
lean_dec(v_unused_4065_);
v___x_4059_ = v___x_4057_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_dec(v___x_4057_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
lean_ctor_set_tag(v___x_4059_, 1);
lean_ctor_set(v___x_4059_, 0, v___x_4054_);
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4054_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
else
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
v_a_4066_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___x_4057_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4057_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_dec_ref(v_b_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_leanOpts_4004_);
v_a_4075_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4020_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4020_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
v___jp_4010_:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4013_ = lean_unsigned_to_nat(1u);
v___x_4014_ = lean_nat_add(v_a_4005_, v___x_4013_);
lean_dec(v_a_4005_);
v_a_4005_ = v___x_4014_;
v_b_4006_ = v_fst_4011_;
v___y_4007_ = v_snd_4012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg___boxed(lean_object* v_upperBound_4083_, lean_object* v_fst_4084_, lean_object* v___x_4085_, lean_object* v_leanOpts_4086_, lean_object* v_a_4087_, lean_object* v_b_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_upperBound_4083_, v_fst_4084_, v___x_4085_, v_leanOpts_4086_, v_a_4087_, v_b_4088_, v___y_4089_, v___y_4090_);
lean_dec_ref(v___y_4090_);
lean_dec_ref(v___x_4085_);
lean_dec_ref(v_fst_4084_);
lean_dec(v_upperBound_4083_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_a_4093_, lean_object* v_b_4094_){
_start:
{
lean_object* v_next_4095_; 
v_next_4095_ = lean_ctor_get(v_a_4093_, 0);
lean_inc(v_next_4095_);
if (lean_obj_tag(v_next_4095_) == 0)
{
lean_dec_ref(v_a_4093_);
return v_b_4094_;
}
else
{
lean_object* v_upperBound_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4116_; 
v_upperBound_4096_ = lean_ctor_get(v_a_4093_, 1);
v_isSharedCheck_4116_ = !lean_is_exclusive(v_a_4093_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; 
v_unused_4117_ = lean_ctor_get(v_a_4093_, 0);
lean_dec(v_unused_4117_);
v___x_4098_ = v_a_4093_;
v_isShared_4099_ = v_isSharedCheck_4116_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_upperBound_4096_);
lean_dec(v_a_4093_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4116_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v_val_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4115_; 
v_val_4100_ = lean_ctor_get(v_next_4095_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v_next_4095_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4102_ = v_next_4095_;
v_isShared_4103_ = v_isSharedCheck_4115_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_val_4100_);
lean_dec(v_next_4095_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4115_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
uint8_t v___x_4104_; 
v___x_4104_ = lean_nat_dec_lt(v_val_4100_, v_upperBound_4096_);
if (v___x_4104_ == 0)
{
lean_del_object(v___x_4102_);
lean_dec(v_val_4100_);
lean_del_object(v___x_4098_);
lean_dec(v_upperBound_4096_);
return v_b_4094_;
}
else
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4108_; 
v___x_4105_ = lean_unsigned_to_nat(1u);
v___x_4106_ = lean_nat_add(v_val_4100_, v___x_4105_);
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4106_);
v___x_4108_ = v___x_4102_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
lean_object* v___x_4110_; 
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 0, v___x_4108_);
v___x_4110_ = v___x_4098_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4108_);
lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_upperBound_4096_);
v___x_4110_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_array_push(v_b_4094_, v_val_4100_);
v_a_4093_ = v___x_4110_;
v_b_4094_ = v___x_4111_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4120_, lean_object* v_toUpdate_4121_, lean_object* v_leanOpts_4122_, uint8_t v_updateToolchain_4123_, lean_object* v_a_4124_){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_box(1);
v___x_4127_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4124_, v_ws_4120_, v_toUpdate_4121_, v___x_4126_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v_snd_4129_; lean_object* v_packages_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v_baseName_4133_; lean_object* v_depConfigs_4134_; lean_object* v___f_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
v_snd_4129_ = lean_ctor_get(v_a_4128_, 1);
lean_inc(v_snd_4129_);
lean_dec(v_a_4128_);
v_packages_4130_ = lean_ctor_get(v_ws_4120_, 4);
v___x_4131_ = lean_unsigned_to_nat(0u);
v___x_4132_ = lean_array_fget_borrowed(v_packages_4130_, v___x_4131_);
v_baseName_4133_ = lean_ctor_get(v___x_4132_, 1);
v_depConfigs_4134_ = lean_ctor_get(v___x_4132_, 12);
lean_inc(v___x_4132_);
lean_inc_ref(v_ws_4120_);
lean_inc(v_baseName_4133_);
v___f_4135_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4135_, 0, v_baseName_4133_);
lean_closure_set(v___f_4135_, 1, v_ws_4120_);
lean_closure_set(v___f_4135_, 2, v___x_4132_);
v___x_4136_ = lean_array_get_size(v_depConfigs_4134_);
lean_inc_ref(v_depConfigs_4134_);
v___x_4137_ = l_Array_reverse___redArg(v_depConfigs_4134_);
v___x_4138_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4139_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___redArg(v___x_4136_, v___f_4135_, v___x_4137_, v___x_4131_, v___x_4138_, v_snd_4129_, v_a_4124_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v_fst_4141_; lean_object* v_snd_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4217_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v_fst_4141_ = lean_ctor_get(v_a_4140_, 0);
v_snd_4142_ = lean_ctor_get(v_a_4140_, 1);
v_isSharedCheck_4217_ = !lean_is_exclusive(v_a_4140_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4144_ = v_a_4140_;
v_isShared_4145_ = v_isSharedCheck_4217_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_snd_4142_);
lean_inc(v_fst_4141_);
lean_dec(v_a_4140_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4217_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___y_4147_; 
if (v_updateToolchain_4123_ == 0)
{
v___y_4147_ = v_a_4124_;
goto v___jp_4146_;
}
else
{
lean_object* v___x_4208_; 
lean_inc_ref(v_ws_4120_);
v___x_4208_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_a_4124_, v_ws_4120_, v_fst_4141_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_dec_ref_known(v___x_4208_, 1);
v___y_4147_ = v_a_4124_;
goto v___jp_4146_;
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
lean_del_object(v___x_4144_);
lean_dec(v_snd_4142_);
lean_dec(v_fst_4141_);
lean_dec_ref(v___x_4137_);
lean_dec_ref(v_leanOpts_4122_);
lean_dec_ref(v_ws_4120_);
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4208_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4208_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
v___jp_4146_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_array_get_size(v_packages_4130_);
lean_inc_ref(v_leanOpts_4122_);
v___x_4149_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4136_, v_fst_4141_, v___x_4137_, v_leanOpts_4122_, v___x_4131_, v_ws_4120_, v_snd_4142_, v___y_4147_);
lean_dec_ref(v___x_4137_);
lean_dec(v_fst_4141_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4199_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4152_ = v___x_4149_;
v_isShared_4153_ = v_isSharedCheck_4199_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4149_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4199_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v_fst_4154_; lean_object* v_snd_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4198_; 
v_fst_4154_ = lean_ctor_get(v_a_4150_, 0);
v_snd_4155_ = lean_ctor_get(v_a_4150_, 1);
v_isSharedCheck_4198_ = !lean_is_exclusive(v_a_4150_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4157_ = v_a_4150_;
v_isShared_4158_ = v_isSharedCheck_4198_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_snd_4155_);
lean_inc(v_fst_4154_);
lean_dec(v_a_4150_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4198_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v_packages_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4164_; 
v_packages_4159_ = lean_ctor_get(v_fst_4154_, 4);
v___x_4160_ = lean_array_get_size(v_packages_4159_);
v___x_4161_ = lean_array_fget(v_packages_4159_, v___x_4131_);
v___x_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4148_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 1, v___x_4160_);
lean_ctor_set(v___x_4144_, 0, v___x_4162_);
v___x_4164_ = v___x_4144_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4162_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v___x_4160_);
v___x_4164_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; uint8_t v___x_4167_; 
v___x_4165_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4164_, v___x_4138_);
v___x_4166_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4154_, v___x_4161_, v___x_4165_);
v___x_4167_ = lean_nat_dec_eq(v___x_4148_, v___x_4160_);
if (v___x_4167_ == 0)
{
uint8_t v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
lean_del_object(v___x_4157_);
lean_del_object(v___x_4152_);
v___x_4168_ = 1;
v___x_4169_ = lean_unsigned_to_nat(1u);
v___x_4170_ = lean_nat_add(v___x_4148_, v___x_4169_);
v___x_4171_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___redArg(v_leanOpts_4122_, v___x_4168_, v___x_4166_, v___x_4148_, v___x_4170_, v_snd_4155_, v___y_4147_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4189_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4174_ = v___x_4171_;
v_isShared_4175_ = v_isSharedCheck_4189_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4171_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4189_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v_fst_4176_; lean_object* v_snd_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4188_; 
v_fst_4176_ = lean_ctor_get(v_a_4172_, 0);
v_snd_4177_ = lean_ctor_get(v_a_4172_, 1);
v_isSharedCheck_4188_ = !lean_is_exclusive(v_a_4172_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4179_ = v_a_4172_;
v_isShared_4180_ = v_isSharedCheck_4188_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_snd_4177_);
lean_inc(v_fst_4176_);
lean_dec(v_a_4172_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4188_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4181_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4176_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 0, v___x_4181_);
v___x_4183_ = v___x_4179_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4187_, 1, v_snd_4177_);
v___x_4183_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4185_; 
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4183_);
v___x_4185_ = v___x_4174_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4183_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
}
else
{
return v___x_4171_;
}
}
else
{
lean_object* v___x_4190_; lean_object* v___x_4192_; 
lean_dec_ref(v_leanOpts_4122_);
v___x_4190_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4166_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 0, v___x_4190_);
v___x_4192_ = v___x_4157_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4190_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v_snd_4155_);
v___x_4192_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
lean_object* v___x_4194_; 
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 0, v___x_4192_);
v___x_4194_ = v___x_4152_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4192_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_del_object(v___x_4144_);
lean_dec_ref(v_leanOpts_4122_);
v_a_4200_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4149_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4149_);
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
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
lean_dec_ref(v___x_4137_);
lean_dec_ref(v_leanOpts_4122_);
lean_dec_ref(v_ws_4120_);
v_a_4218_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4139_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4139_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec_ref(v_leanOpts_4122_);
lean_dec_ref(v_ws_4120_);
v_a_4226_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4127_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4127_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4234_, lean_object* v_toUpdate_4235_, lean_object* v_leanOpts_4236_, lean_object* v_updateToolchain_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
uint8_t v_updateToolchain_boxed_4240_; lean_object* v_res_4241_; 
v_updateToolchain_boxed_4240_ = lean_unbox(v_updateToolchain_4237_);
v_res_4241_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4234_, v_toUpdate_4235_, v_leanOpts_4236_, v_updateToolchain_boxed_4240_, v_a_4238_);
lean_dec_ref(v_a_4238_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_00_u03b1_4242_, lean_object* v_00_u03b2_4243_, lean_object* v_n_4244_, lean_object* v_f_4245_, lean_object* v_xs_4246_, lean_object* v_k_4247_, lean_object* v_h_4248_, lean_object* v_acc_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___redArg(v_n_4244_, v_f_4245_, v_xs_4246_, v_k_4247_, v_acc_4249_, v___y_4250_, v___y_4251_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___boxed(lean_object* v_00_u03b1_4254_, lean_object* v_00_u03b2_4255_, lean_object* v_n_4256_, lean_object* v_f_4257_, lean_object* v_xs_4258_, lean_object* v_k_4259_, lean_object* v_h_4260_, lean_object* v_acc_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_00_u03b1_4254_, v_00_u03b2_4255_, v_n_4256_, v_f_4257_, v_xs_4258_, v_k_4259_, v_h_4260_, v_acc_4261_, v___y_4262_, v___y_4263_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v_xs_4258_);
lean_dec(v_n_4256_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_inst_4266_, lean_object* v_R_4267_, lean_object* v_a_4268_, lean_object* v_b_4269_){
_start:
{
lean_object* v___x_4270_; 
v___x_4270_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_a_4268_, v_b_4269_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_leanOpts_4271_, uint8_t v_reconfigure_4272_, lean_object* v_ws_4273_, lean_object* v_i_4274_, lean_object* v_i__lt_4275_, lean_object* v_next_4276_, lean_object* v_lt__next_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___redArg(v_leanOpts_4271_, v_reconfigure_4272_, v_ws_4273_, v_i_4274_, v_next_4276_, v___y_4278_, v___y_4279_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_leanOpts_4282_, lean_object* v_reconfigure_4283_, lean_object* v_ws_4284_, lean_object* v_i_4285_, lean_object* v_i__lt_4286_, lean_object* v_next_4287_, lean_object* v_lt__next_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
uint8_t v_reconfigure_boxed_4292_; lean_object* v_res_4293_; 
v_reconfigure_boxed_4292_ = lean_unbox(v_reconfigure_4283_);
v_res_4293_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_leanOpts_4282_, v_reconfigure_boxed_4292_, v_ws_4284_, v_i_4285_, v_i__lt_4286_, v_next_4287_, v_lt__next_4288_, v___y_4289_, v___y_4290_);
lean_dec_ref(v___y_4290_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_upperBound_4294_, lean_object* v_fst_4295_, lean_object* v___x_4296_, lean_object* v_leanOpts_4297_, lean_object* v_inst_4298_, lean_object* v_R_4299_, lean_object* v_a_4300_, lean_object* v_b_4301_, lean_object* v_c_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_upperBound_4294_, v_fst_4295_, v___x_4296_, v_leanOpts_4297_, v_a_4300_, v_b_4301_, v___y_4303_, v___y_4304_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___boxed(lean_object* v_upperBound_4307_, lean_object* v_fst_4308_, lean_object* v___x_4309_, lean_object* v_leanOpts_4310_, lean_object* v_inst_4311_, lean_object* v_R_4312_, lean_object* v_a_4313_, lean_object* v_b_4314_, lean_object* v_c_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(v_upperBound_4307_, v_fst_4308_, v___x_4309_, v_leanOpts_4310_, v_inst_4311_, v_R_4312_, v_a_4313_, v_b_4314_, v_c_4315_, v___y_4316_, v___y_4317_);
lean_dec_ref(v___y_4317_);
lean_dec_ref(v___x_4309_);
lean_dec_ref(v_fst_4308_);
lean_dec(v_upperBound_4307_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4_spec__6(lean_object* v_00_u03b2_4320_, lean_object* v_msg_4321_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4_spec__6___redArg(v_msg_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_00_u03b2_4323_, lean_object* v_k_4324_, lean_object* v_v_4325_, lean_object* v_t_4326_){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_k_4324_, v_v_4325_, v_t_4326_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(lean_object* v_init_4328_, lean_object* v_t_4329_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5_spec__8(v_init_4328_, v_t_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9(lean_object* v_start_4331_, lean_object* v_pkg_4332_, lean_object* v_leanOpts_4333_, uint8_t v_reconfigure_4334_, lean_object* v_as_4335_, size_t v_i_4336_, size_t v_stop_4337_, lean_object* v_b_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg(v_pkg_4332_, v_leanOpts_4333_, v_reconfigure_4334_, v_as_4335_, v_i_4336_, v_stop_4337_, v_b_4338_, v___y_4339_, v___y_4340_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___boxed(lean_object* v_start_4343_, lean_object* v_pkg_4344_, lean_object* v_leanOpts_4345_, lean_object* v_reconfigure_4346_, lean_object* v_as_4347_, lean_object* v_i_4348_, lean_object* v_stop_4349_, lean_object* v_b_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
uint8_t v_reconfigure_boxed_4354_; size_t v_i_boxed_4355_; size_t v_stop_boxed_4356_; lean_object* v_res_4357_; 
v_reconfigure_boxed_4354_ = lean_unbox(v_reconfigure_4346_);
v_i_boxed_4355_ = lean_unbox_usize(v_i_4348_);
lean_dec(v_i_4348_);
v_stop_boxed_4356_ = lean_unbox_usize(v_stop_4349_);
lean_dec(v_stop_4349_);
v_res_4357_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9(v_start_4343_, v_pkg_4344_, v_leanOpts_4345_, v_reconfigure_boxed_4354_, v_as_4347_, v_i_boxed_4355_, v_stop_boxed_4356_, v_b_4350_, v___y_4351_, v___y_4352_);
lean_dec_ref(v___y_4352_);
lean_dec_ref(v_as_4347_);
lean_dec(v_start_4343_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4358_, lean_object* v_as_4359_, size_t v_i_4360_, size_t v_stop_4361_, lean_object* v_b_4362_){
_start:
{
lean_object* v___y_4364_; uint8_t v___x_4368_; 
v___x_4368_ = lean_usize_dec_eq(v_i_4360_, v_stop_4361_);
if (v___x_4368_ == 0)
{
lean_object* v___x_4369_; lean_object* v_baseName_4370_; lean_object* v_relConfigFile_4371_; lean_object* v_relManifestFile_4372_; lean_object* v___x_4373_; 
v___x_4369_ = lean_array_uget_borrowed(v_as_4359_, v_i_4360_);
v_baseName_4370_ = lean_ctor_get(v___x_4369_, 1);
v_relConfigFile_4371_ = lean_ctor_get(v___x_4369_, 8);
v_relManifestFile_4372_ = lean_ctor_get(v___x_4369_, 9);
v___x_4373_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4358_, v_baseName_4370_);
if (lean_obj_tag(v___x_4373_) == 0)
{
v___y_4364_ = v_b_4362_;
goto v___jp_4363_;
}
else
{
lean_object* v_val_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4395_; 
v_val_4374_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4376_ = v___x_4373_;
v_isShared_4377_ = v_isSharedCheck_4395_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_val_4374_);
lean_dec(v___x_4373_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4395_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v_name_4378_; lean_object* v_scope_4379_; uint8_t v_inherited_4380_; lean_object* v_src_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4392_; 
v_name_4378_ = lean_ctor_get(v_val_4374_, 0);
v_scope_4379_ = lean_ctor_get(v_val_4374_, 1);
v_inherited_4380_ = lean_ctor_get_uint8(v_val_4374_, sizeof(void*)*5);
v_src_4381_ = lean_ctor_get(v_val_4374_, 4);
v_isSharedCheck_4392_ = !lean_is_exclusive(v_val_4374_);
if (v_isSharedCheck_4392_ == 0)
{
lean_object* v_unused_4393_; lean_object* v_unused_4394_; 
v_unused_4393_ = lean_ctor_get(v_val_4374_, 3);
lean_dec(v_unused_4393_);
v_unused_4394_ = lean_ctor_get(v_val_4374_, 2);
lean_dec(v_unused_4394_);
v___x_4383_ = v_val_4374_;
v_isShared_4384_ = v_isSharedCheck_4392_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_src_4381_);
lean_inc(v_scope_4379_);
lean_inc(v_name_4378_);
lean_dec(v_val_4374_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4392_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
lean_inc_ref(v_relManifestFile_4372_);
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 0, v_relManifestFile_4372_);
v___x_4386_ = v___x_4376_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_relManifestFile_4372_);
v___x_4386_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
lean_object* v___x_4388_; 
lean_inc_ref(v_relConfigFile_4371_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 3, v___x_4386_);
lean_ctor_set(v___x_4383_, 2, v_relConfigFile_4371_);
v___x_4388_ = v___x_4383_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_name_4378_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_scope_4379_);
lean_ctor_set(v_reuseFailAlloc_4390_, 2, v_relConfigFile_4371_);
lean_ctor_set(v_reuseFailAlloc_4390_, 3, v___x_4386_);
lean_ctor_set(v_reuseFailAlloc_4390_, 4, v_src_4381_);
lean_ctor_set_uint8(v_reuseFailAlloc_4390_, sizeof(void*)*5, v_inherited_4380_);
v___x_4388_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4389_; 
v___x_4389_ = lean_array_push(v_b_4362_, v___x_4388_);
v___y_4364_ = v___x_4389_;
goto v___jp_4363_;
}
}
}
}
}
}
else
{
return v_b_4362_;
}
v___jp_4363_:
{
size_t v___x_4365_; size_t v___x_4366_; 
v___x_4365_ = ((size_t)1ULL);
v___x_4366_ = lean_usize_add(v_i_4360_, v___x_4365_);
v_i_4360_ = v___x_4366_;
v_b_4362_ = v___y_4364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4396_, lean_object* v_as_4397_, lean_object* v_i_4398_, lean_object* v_stop_4399_, lean_object* v_b_4400_){
_start:
{
size_t v_i_boxed_4401_; size_t v_stop_boxed_4402_; lean_object* v_res_4403_; 
v_i_boxed_4401_ = lean_unbox_usize(v_i_4398_);
lean_dec(v_i_4398_);
v_stop_boxed_4402_ = lean_unbox_usize(v_stop_4399_);
lean_dec(v_stop_4399_);
v_res_4403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4396_, v_as_4397_, v_i_boxed_4401_, v_stop_boxed_4402_, v_b_4400_);
lean_dec_ref(v_as_4397_);
lean_dec(v_entries_4396_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4404_, lean_object* v_entries_4405_){
_start:
{
lean_object* v_packages_4407_; lean_object* v___y_4409_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; uint8_t v___x_4427_; 
v_packages_4407_ = lean_ctor_get(v_ws_4404_, 4);
v___x_4424_ = lean_unsigned_to_nat(0u);
v___x_4425_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4426_ = lean_array_get_size(v_packages_4407_);
v___x_4427_ = lean_nat_dec_lt(v___x_4424_, v___x_4426_);
if (v___x_4427_ == 0)
{
v___y_4409_ = v___x_4425_;
goto v___jp_4408_;
}
else
{
size_t v___x_4428_; size_t v___x_4429_; lean_object* v___x_4430_; 
v___x_4428_ = ((size_t)0ULL);
v___x_4429_ = lean_usize_of_nat(v___x_4426_);
v___x_4430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4405_, v_packages_4407_, v___x_4428_, v___x_4429_, v___x_4425_);
v___y_4409_ = v___x_4430_;
goto v___jp_4408_;
}
v___jp_4408_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v_config_4412_; lean_object* v_baseName_4413_; lean_object* v_dir_4414_; lean_object* v_relManifestFile_4415_; lean_object* v_toWorkspaceConfig_4416_; uint8_t v_fixedToolchain_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v_manifest_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4410_ = lean_unsigned_to_nat(0u);
v___x_4411_ = lean_array_fget_borrowed(v_packages_4407_, v___x_4410_);
v_config_4412_ = lean_ctor_get(v___x_4411_, 6);
v_baseName_4413_ = lean_ctor_get(v___x_4411_, 1);
v_dir_4414_ = lean_ctor_get(v___x_4411_, 4);
v_relManifestFile_4415_ = lean_ctor_get(v___x_4411_, 9);
v_toWorkspaceConfig_4416_ = lean_ctor_get(v_config_4412_, 0);
v_fixedToolchain_4417_ = lean_ctor_get_uint8(v_config_4412_, sizeof(void*)*28 + 6);
v___x_4418_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4416_);
v___x_4419_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4416_);
v___x_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
lean_inc(v_baseName_4413_);
v_manifest_4421_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4421_, 0, v_baseName_4413_);
lean_ctor_set(v_manifest_4421_, 1, v___x_4418_);
lean_ctor_set(v_manifest_4421_, 2, v___x_4420_);
lean_ctor_set(v_manifest_4421_, 3, v___y_4409_);
lean_ctor_set_uint8(v_manifest_4421_, sizeof(void*)*4, v_fixedToolchain_4417_);
lean_inc_ref(v_relManifestFile_4415_);
lean_inc_ref(v_dir_4414_);
v___x_4422_ = l_Lake_joinRelative(v_dir_4414_, v_relManifestFile_4415_);
v___x_4423_ = l_Lake_Manifest_save(v_manifest_4421_, v___x_4422_);
lean_dec_ref(v___x_4422_);
return v___x_4423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4431_, lean_object* v_entries_4432_, lean_object* v_a_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4431_, v_entries_4432_);
lean_dec(v_entries_4432_);
lean_dec_ref(v_ws_4431_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4435_, lean_object* v_as_4436_, size_t v_i_4437_, size_t v_stop_4438_, lean_object* v_b_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
lean_object* v_a_4444_; uint8_t v___x_4448_; 
v___x_4448_ = lean_usize_dec_eq(v_i_4437_, v_stop_4438_);
if (v___x_4448_ == 0)
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_6568__overap_4451_; lean_object* v___x_4452_; 
v___x_4449_ = lean_unsigned_to_nat(0u);
v___x_4450_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_6568__overap_4451_ = lean_array_uget_borrowed(v_as_4436_, v_i_4437_);
lean_inc(v___x_6568__overap_4451_);
lean_inc(v___y_4440_);
lean_inc_ref(v_pkg_4435_);
v___x_4452_ = lean_apply_4(v___x_6568__overap_4451_, v_pkg_4435_, v___y_4440_, v___x_4450_, lean_box(0));
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v_a_4454_; lean_object* v___x_4455_; uint8_t v___x_4456_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
v_a_4454_ = lean_ctor_get(v___x_4452_, 1);
lean_inc(v_a_4454_);
lean_dec_ref_known(v___x_4452_, 2);
v___x_4455_ = lean_array_get_size(v_a_4454_);
v___x_4456_ = lean_nat_dec_lt(v___x_4449_, v___x_4455_);
if (v___x_4456_ == 0)
{
lean_dec(v_a_4454_);
v_a_4444_ = v_a_4453_;
goto v___jp_4443_;
}
else
{
lean_object* v___x_4457_; size_t v___x_4458_; size_t v___x_4459_; lean_object* v___x_4460_; 
v___x_4457_ = lean_box(0);
v___x_4458_ = ((size_t)0ULL);
v___x_4459_ = lean_usize_of_nat(v___x_4455_);
v___x_4460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4454_, v___x_4458_, v___x_4459_, v___x_4457_, v___y_4441_);
lean_dec(v_a_4454_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_dec_ref_known(v___x_4460_, 1);
v_a_4444_ = v_a_4453_;
goto v___jp_4443_;
}
else
{
lean_dec(v_a_4453_);
lean_dec_ref(v_pkg_4435_);
return v___x_4460_;
}
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4462_; uint8_t v___x_4463_; 
lean_dec_ref(v_pkg_4435_);
v_a_4461_ = lean_ctor_get(v___x_4452_, 1);
lean_inc(v_a_4461_);
lean_dec_ref_known(v___x_4452_, 2);
v___x_4462_ = lean_array_get_size(v_a_4461_);
v___x_4463_ = lean_nat_dec_lt(v___x_4449_, v___x_4462_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; lean_object* v___x_4465_; 
lean_dec(v_a_4461_);
v___x_4464_ = lean_box(0);
v___x_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4464_);
return v___x_4465_;
}
else
{
lean_object* v___x_4466_; size_t v___x_4467_; size_t v___x_4468_; lean_object* v___x_4469_; 
v___x_4466_ = lean_box(0);
v___x_4467_ = ((size_t)0ULL);
v___x_4468_ = lean_usize_of_nat(v___x_4462_);
v___x_4469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4461_, v___x_4467_, v___x_4468_, v___x_4466_, v___y_4441_);
lean_dec(v_a_4461_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4476_ == 0)
{
lean_object* v_unused_4477_; 
v_unused_4477_ = lean_ctor_get(v___x_4469_, 0);
lean_dec(v_unused_4477_);
v___x_4471_ = v___x_4469_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_dec(v___x_4469_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
lean_ctor_set_tag(v___x_4471_, 1);
lean_ctor_set(v___x_4471_, 0, v___x_4466_);
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4466_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
else
{
return v___x_4469_;
}
}
}
}
else
{
lean_object* v___x_4478_; 
lean_dec_ref(v_pkg_4435_);
v___x_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4478_, 0, v_b_4439_);
return v___x_4478_;
}
v___jp_4443_:
{
size_t v___x_4445_; size_t v___x_4446_; 
v___x_4445_ = ((size_t)1ULL);
v___x_4446_ = lean_usize_add(v_i_4437_, v___x_4445_);
v_i_4437_ = v___x_4446_;
v_b_4439_ = v_a_4444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4479_, lean_object* v_as_4480_, lean_object* v_i_4481_, lean_object* v_stop_4482_, lean_object* v_b_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
size_t v_i_boxed_4487_; size_t v_stop_boxed_4488_; lean_object* v_res_4489_; 
v_i_boxed_4487_ = lean_unbox_usize(v_i_4481_);
lean_dec(v_i_4481_);
v_stop_boxed_4488_ = lean_unbox_usize(v_stop_4482_);
lean_dec(v_stop_4482_);
v_res_4489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4479_, v_as_4480_, v_i_boxed_4487_, v_stop_boxed_4488_, v_b_4483_, v___y_4484_, v___y_4485_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v_as_4480_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v_baseName_4495_; lean_object* v_postUpdateHooks_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; uint8_t v___x_4499_; 
v_baseName_4495_ = lean_ctor_get(v_pkg_4491_, 1);
v_postUpdateHooks_4496_ = lean_ctor_get(v_pkg_4491_, 21);
lean_inc_ref(v_postUpdateHooks_4496_);
v___x_4497_ = lean_array_get_size(v_postUpdateHooks_4496_);
v___x_4498_ = lean_unsigned_to_nat(0u);
v___x_4499_ = lean_nat_dec_eq(v___x_4497_, v___x_4498_);
if (v___x_4499_ == 0)
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; uint8_t v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; uint8_t v___x_4507_; 
lean_inc(v_baseName_4495_);
v___x_4500_ = l_Lean_Name_toString(v_baseName_4495_, v___x_4499_);
v___x_4501_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4502_ = lean_string_append(v___x_4500_, v___x_4501_);
v___x_4503_ = 1;
v___x_4504_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4504_, 0, v___x_4502_);
lean_ctor_set_uint8(v___x_4504_, sizeof(void*)*1, v___x_4503_);
lean_inc_ref(v_a_4493_);
v___x_4505_ = lean_apply_2(v_a_4493_, v___x_4504_, lean_box(0));
v___x_4506_ = lean_box(0);
v___x_4507_ = lean_nat_dec_lt(v___x_4498_, v___x_4497_);
if (v___x_4507_ == 0)
{
lean_object* v___x_4508_; 
lean_dec_ref(v_postUpdateHooks_4496_);
lean_dec_ref(v_pkg_4491_);
v___x_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4506_);
return v___x_4508_;
}
else
{
size_t v___x_4509_; size_t v___x_4510_; lean_object* v___x_4511_; 
v___x_4509_ = ((size_t)0ULL);
v___x_4510_ = lean_usize_of_nat(v___x_4497_);
v___x_4511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4491_, v_postUpdateHooks_4496_, v___x_4509_, v___x_4510_, v___x_4506_, v_a_4492_, v_a_4493_);
lean_dec_ref(v_postUpdateHooks_4496_);
return v___x_4511_;
}
}
else
{
lean_object* v___x_4512_; lean_object* v___x_4513_; 
lean_dec_ref(v_postUpdateHooks_4496_);
lean_dec_ref(v_pkg_4491_);
v___x_4512_ = lean_box(0);
v___x_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4512_);
return v___x_4513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4514_, v_a_4515_, v_a_4516_);
lean_dec_ref(v_a_4516_);
lean_dec(v_a_4515_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4519_, lean_object* v_ws_4520_, lean_object* v_toUpdate_4521_, lean_object* v_leanOpts_4522_, uint8_t v_updateToolchain_4523_){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4525_ = lean_box(1);
v___x_4526_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4519_, v_ws_4520_, v_toUpdate_4521_, v___x_4525_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_a_4527_; lean_object* v_snd_4528_; lean_object* v_packages_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v_baseName_4532_; lean_object* v_depConfigs_4533_; lean_object* v___f_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc(v_a_4527_);
lean_dec_ref_known(v___x_4526_, 1);
v_snd_4528_ = lean_ctor_get(v_a_4527_, 1);
lean_inc(v_snd_4528_);
lean_dec(v_a_4527_);
v_packages_4529_ = lean_ctor_get(v_ws_4520_, 4);
v___x_4530_ = lean_unsigned_to_nat(0u);
v___x_4531_ = lean_array_fget_borrowed(v_packages_4529_, v___x_4530_);
v_baseName_4532_ = lean_ctor_get(v___x_4531_, 1);
v_depConfigs_4533_ = lean_ctor_get(v___x_4531_, 12);
lean_inc(v___x_4531_);
lean_inc_ref(v_ws_4520_);
lean_inc(v_baseName_4532_);
v___f_4534_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4534_, 0, v_baseName_4532_);
lean_closure_set(v___f_4534_, 1, v_ws_4520_);
lean_closure_set(v___f_4534_, 2, v___x_4531_);
v___x_4535_ = lean_array_get_size(v_depConfigs_4533_);
lean_inc_ref(v_depConfigs_4533_);
v___x_4536_ = l_Array_reverse___redArg(v_depConfigs_4533_);
v___x_4537_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4538_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___redArg(v___x_4535_, v___f_4534_, v___x_4536_, v___x_4530_, v___x_4537_, v_snd_4528_, v_a_4519_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; lean_object* v_fst_4540_; lean_object* v_snd_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4616_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v___x_4538_, 1);
v_fst_4540_ = lean_ctor_get(v_a_4539_, 0);
v_snd_4541_ = lean_ctor_get(v_a_4539_, 1);
v_isSharedCheck_4616_ = !lean_is_exclusive(v_a_4539_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4543_ = v_a_4539_;
v_isShared_4544_ = v_isSharedCheck_4616_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_snd_4541_);
lean_inc(v_fst_4540_);
lean_dec(v_a_4539_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4616_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___y_4546_; 
if (v_updateToolchain_4523_ == 0)
{
v___y_4546_ = v_a_4519_;
goto v___jp_4545_;
}
else
{
lean_object* v___x_4607_; 
lean_inc_ref(v_ws_4520_);
v___x_4607_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_a_4519_, v_ws_4520_, v_fst_4540_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_dec_ref_known(v___x_4607_, 1);
v___y_4546_ = v_a_4519_;
goto v___jp_4545_;
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_del_object(v___x_4543_);
lean_dec(v_snd_4541_);
lean_dec(v_fst_4540_);
lean_dec_ref(v___x_4536_);
lean_dec_ref(v_leanOpts_4522_);
lean_dec_ref(v_ws_4520_);
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4607_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4607_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
v___jp_4545_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4547_ = lean_array_get_size(v_packages_4529_);
lean_inc_ref(v_leanOpts_4522_);
v___x_4548_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4535_, v_fst_4540_, v___x_4536_, v_leanOpts_4522_, v___x_4530_, v_ws_4520_, v_snd_4541_, v___y_4546_);
lean_dec_ref(v___x_4536_);
lean_dec(v_fst_4540_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4598_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4598_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4598_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v_fst_4553_; lean_object* v_snd_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4597_; 
v_fst_4553_ = lean_ctor_get(v_a_4549_, 0);
v_snd_4554_ = lean_ctor_get(v_a_4549_, 1);
v_isSharedCheck_4597_ = !lean_is_exclusive(v_a_4549_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4556_ = v_a_4549_;
v_isShared_4557_ = v_isSharedCheck_4597_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_snd_4554_);
lean_inc(v_fst_4553_);
lean_dec(v_a_4549_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4597_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v_packages_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4563_; 
v_packages_4558_ = lean_ctor_get(v_fst_4553_, 4);
v___x_4559_ = lean_array_get_size(v_packages_4558_);
v___x_4560_ = lean_array_fget(v_packages_4558_, v___x_4530_);
v___x_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4547_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 1, v___x_4559_);
lean_ctor_set(v___x_4543_, 0, v___x_4561_);
v___x_4563_ = v___x_4543_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4561_);
lean_ctor_set(v_reuseFailAlloc_4596_, 1, v___x_4559_);
v___x_4563_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; uint8_t v___x_4566_; 
v___x_4564_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4563_, v___x_4537_);
v___x_4565_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4553_, v___x_4560_, v___x_4564_);
v___x_4566_ = lean_nat_dec_eq(v___x_4547_, v___x_4559_);
if (v___x_4566_ == 0)
{
uint8_t v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
lean_del_object(v___x_4556_);
lean_del_object(v___x_4551_);
v___x_4567_ = 1;
v___x_4568_ = lean_unsigned_to_nat(1u);
v___x_4569_ = lean_nat_add(v___x_4547_, v___x_4568_);
v___x_4570_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___redArg(v_leanOpts_4522_, v___x_4567_, v___x_4565_, v___x_4547_, v___x_4569_, v_snd_4554_, v___y_4546_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4588_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4573_ = v___x_4570_;
v_isShared_4574_ = v_isSharedCheck_4588_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4570_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4588_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v_fst_4575_; lean_object* v_snd_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4587_; 
v_fst_4575_ = lean_ctor_get(v_a_4571_, 0);
v_snd_4576_ = lean_ctor_get(v_a_4571_, 1);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_a_4571_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4578_ = v_a_4571_;
v_isShared_4579_ = v_isSharedCheck_4587_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_snd_4576_);
lean_inc(v_fst_4575_);
lean_dec(v_a_4571_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4587_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4580_; lean_object* v___x_4582_; 
v___x_4580_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4575_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 0, v___x_4580_);
v___x_4582_ = v___x_4578_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4586_, 1, v_snd_4576_);
v___x_4582_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4584_; 
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 0, v___x_4582_);
v___x_4584_ = v___x_4573_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v___x_4582_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
else
{
return v___x_4570_;
}
}
else
{
lean_object* v___x_4589_; lean_object* v___x_4591_; 
lean_dec_ref(v_leanOpts_4522_);
v___x_4589_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4565_);
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 0, v___x_4589_);
v___x_4591_ = v___x_4556_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4589_);
lean_ctor_set(v_reuseFailAlloc_4595_, 1, v_snd_4554_);
v___x_4591_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
lean_object* v___x_4593_; 
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4591_);
v___x_4593_ = v___x_4551_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4591_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4606_; 
lean_del_object(v___x_4543_);
lean_dec_ref(v_leanOpts_4522_);
v_a_4599_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4601_ = v___x_4548_;
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4548_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4604_; 
if (v_isShared_4602_ == 0)
{
v___x_4604_ = v___x_4601_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
}
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
lean_dec_ref(v___x_4536_);
lean_dec_ref(v_leanOpts_4522_);
lean_dec_ref(v_ws_4520_);
v_a_4617_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4538_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4538_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_dec_ref(v_leanOpts_4522_);
lean_dec_ref(v_ws_4520_);
v_a_4625_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4526_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4526_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4633_, lean_object* v_ws_4634_, lean_object* v_toUpdate_4635_, lean_object* v_leanOpts_4636_, lean_object* v_updateToolchain_4637_, lean_object* v_a_4638_){
_start:
{
uint8_t v_updateToolchain_boxed_4639_; lean_object* v_res_4640_; 
v_updateToolchain_boxed_4639_ = lean_unbox(v_updateToolchain_4637_);
v_res_4640_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4633_, v_ws_4634_, v_toUpdate_4635_, v_leanOpts_4636_, v_updateToolchain_boxed_4639_);
lean_dec_ref(v_a_4633_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4641_, size_t v_i_4642_, size_t v_stop_4643_, lean_object* v_b_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
uint8_t v___x_4648_; 
v___x_4648_ = lean_usize_dec_eq(v_i_4642_, v_stop_4643_);
if (v___x_4648_ == 0)
{
lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4649_ = lean_array_uget_borrowed(v_as_4641_, v_i_4642_);
lean_inc(v___x_4649_);
v___x_4650_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4649_, v___y_4645_, v___y_4646_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; size_t v___x_4652_; size_t v___x_4653_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref_known(v___x_4650_, 1);
v___x_4652_ = ((size_t)1ULL);
v___x_4653_ = lean_usize_add(v_i_4642_, v___x_4652_);
v_i_4642_ = v___x_4653_;
v_b_4644_ = v_a_4651_;
goto _start;
}
else
{
return v___x_4650_;
}
}
else
{
lean_object* v___x_4655_; 
v___x_4655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4655_, 0, v_b_4644_);
return v___x_4655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4656_, lean_object* v_i_4657_, lean_object* v_stop_4658_, lean_object* v_b_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
size_t v_i_boxed_4663_; size_t v_stop_boxed_4664_; lean_object* v_res_4665_; 
v_i_boxed_4663_ = lean_unbox_usize(v_i_4657_);
lean_dec(v_i_4657_);
v_stop_boxed_4664_ = lean_unbox_usize(v_stop_4658_);
lean_dec(v_stop_4658_);
v_res_4665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4656_, v_i_boxed_4663_, v_stop_boxed_4664_, v_b_4659_, v___y_4660_, v___y_4661_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v_as_4656_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4666_, lean_object* v_toUpdate_4667_, lean_object* v_leanOpts_4668_, uint8_t v_updateToolchain_4669_, lean_object* v_a_4670_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4670_, v_ws_4666_, v_toUpdate_4667_, v_leanOpts_4668_, v_updateToolchain_4669_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v_fst_4674_; lean_object* v_snd_4675_; lean_object* v___x_4676_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4673_);
lean_dec_ref_known(v___x_4672_, 1);
v_fst_4674_ = lean_ctor_get(v_a_4673_, 0);
lean_inc(v_fst_4674_);
v_snd_4675_ = lean_ctor_get(v_a_4673_, 1);
lean_inc(v_snd_4675_);
lean_dec(v_a_4673_);
v___x_4676_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4674_, v_snd_4675_);
lean_dec(v_snd_4675_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4707_; 
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4707_ == 0)
{
lean_object* v_unused_4708_; 
v_unused_4708_ = lean_ctor_get(v___x_4676_, 0);
lean_dec(v_unused_4708_);
v___x_4678_ = v___x_4676_;
v_isShared_4679_ = v_isSharedCheck_4707_;
goto v_resetjp_4677_;
}
else
{
lean_dec(v___x_4676_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4707_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v_packages_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; uint8_t v___x_4683_; 
v_packages_4680_ = lean_ctor_get(v_fst_4674_, 4);
v___x_4681_ = lean_unsigned_to_nat(0u);
v___x_4682_ = lean_array_get_size(v_packages_4680_);
v___x_4683_ = lean_nat_dec_lt(v___x_4681_, v___x_4682_);
if (v___x_4683_ == 0)
{
lean_object* v___x_4685_; 
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 0, v_fst_4674_);
v___x_4685_ = v___x_4678_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_fst_4674_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
else
{
lean_object* v___x_4687_; size_t v___x_4688_; size_t v___x_4689_; lean_object* v___x_4690_; 
lean_del_object(v___x_4678_);
v___x_4687_ = lean_box(0);
v___x_4688_ = ((size_t)0ULL);
v___x_4689_ = lean_usize_of_nat(v___x_4682_);
v___x_4690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4680_, v___x_4688_, v___x_4689_, v___x_4687_, v_fst_4674_, v_a_4670_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4697_ == 0)
{
lean_object* v_unused_4698_; 
v_unused_4698_ = lean_ctor_get(v___x_4690_, 0);
lean_dec(v_unused_4698_);
v___x_4692_ = v___x_4690_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_dec(v___x_4690_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 0, v_fst_4674_);
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_fst_4674_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
else
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4706_; 
lean_dec(v_fst_4674_);
v_a_4699_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4701_ = v___x_4690_;
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4690_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
if (v_isShared_4702_ == 0)
{
v___x_4704_ = v___x_4701_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
}
}
}
else
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4721_; 
lean_dec(v_fst_4674_);
v_a_4709_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4711_ = v___x_4676_;
v_isShared_4712_ = v_isSharedCheck_4721_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4676_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4721_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4713_; uint8_t v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4719_; 
v___x_4713_ = lean_io_error_to_string(v_a_4709_);
v___x_4714_ = 3;
v___x_4715_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4715_, 0, v___x_4713_);
lean_ctor_set_uint8(v___x_4715_, sizeof(void*)*1, v___x_4714_);
lean_inc_ref(v_a_4670_);
v___x_4716_ = lean_apply_2(v_a_4670_, v___x_4715_, lean_box(0));
v___x_4717_ = lean_box(0);
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 0, v___x_4717_);
v___x_4719_ = v___x_4711_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4717_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
else
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
v_a_4722_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4672_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4672_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4730_, lean_object* v_toUpdate_4731_, lean_object* v_leanOpts_4732_, lean_object* v_updateToolchain_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
uint8_t v_updateToolchain_boxed_4736_; lean_object* v_res_4737_; 
v_updateToolchain_boxed_4736_ = lean_unbox(v_updateToolchain_4733_);
v_res_4737_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4730_, v_toUpdate_4731_, v_leanOpts_4732_, v_updateToolchain_boxed_4736_, v_a_4734_);
lean_dec_ref(v_a_4734_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v_name_4742_, lean_object* v_what_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; uint8_t v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_4747_ = lean_string_append(v___x_4746_, v_what_4743_);
v___x_4748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_4749_ = lean_string_append(v___x_4747_, v___x_4748_);
v___x_4750_ = 1;
v___x_4751_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4742_, v___x_4750_);
v___x_4752_ = lean_string_append(v___x_4749_, v___x_4751_);
v___x_4753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_4754_ = lean_string_append(v___x_4752_, v___x_4753_);
v___x_4755_ = lean_string_append(v___x_4754_, v___x_4751_);
lean_dec_ref(v___x_4751_);
v___x_4756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_4757_ = lean_string_append(v___x_4755_, v___x_4756_);
v___x_4758_ = 2;
v___x_4759_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4759_, 0, v___x_4757_);
lean_ctor_set_uint8(v___x_4759_, sizeof(void*)*1, v___x_4758_);
lean_inc_ref(v___y_4744_);
v___x_4760_ = lean_apply_2(v___y_4744_, v___x_4759_, lean_box(0));
v___x_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4761_, 0, v___x_4760_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v_name_4762_, lean_object* v_what_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v_name_4762_, v_what_4763_, v___y_4764_);
lean_dec_ref(v___y_4764_);
lean_dec_ref(v_what_4763_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_4770_, lean_object* v_as_4771_, size_t v_i_4772_, size_t v_stop_4773_, lean_object* v_b_4774_, lean_object* v___y_4775_){
_start:
{
lean_object* v_a_4778_; lean_object* v___y_4783_; uint8_t v___x_4785_; 
v___x_4785_ = lean_usize_dec_eq(v_i_4772_, v_stop_4773_);
if (v___x_4785_ == 0)
{
lean_object* v___x_4786_; lean_object* v_src_x3f_4787_; 
v___x_4786_ = lean_array_uget_borrowed(v_as_4771_, v_i_4772_);
v_src_x3f_4787_ = lean_ctor_get(v___x_4786_, 3);
if (lean_obj_tag(v_src_x3f_4787_) == 1)
{
lean_object* v_name_4788_; lean_object* v_val_4789_; lean_object* v___x_4790_; 
v_name_4788_ = lean_ctor_get(v___x_4786_, 0);
v_val_4789_ = lean_ctor_get(v_src_x3f_4787_, 0);
v___x_4790_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_4770_, v_name_4788_);
if (lean_obj_tag(v___x_4790_) == 1)
{
lean_object* v_val_4791_; lean_object* v___y_4793_; 
v_val_4791_ = lean_ctor_get(v___x_4790_, 0);
lean_inc(v_val_4791_);
lean_dec_ref_known(v___x_4790_, 1);
if (lean_obj_tag(v_val_4789_) == 0)
{
lean_object* v_src_4796_; 
v_src_4796_ = lean_ctor_get(v_val_4791_, 4);
lean_inc_ref(v_src_4796_);
lean_dec(v_val_4791_);
if (lean_obj_tag(v_src_4796_) == 0)
{
lean_object* v___x_4797_; 
lean_dec_ref_known(v_src_4796_, 1);
v___x_4797_ = lean_box(0);
v_a_4778_ = v___x_4797_;
goto v___jp_4777_;
}
else
{
lean_dec_ref(v_src_4796_);
v___y_4793_ = v___y_4775_;
goto v___jp_4792_;
}
}
else
{
lean_object* v_src_4798_; 
v_src_4798_ = lean_ctor_get(v_val_4791_, 4);
lean_inc_ref(v_src_4798_);
lean_dec(v_val_4791_);
if (lean_obj_tag(v_src_4798_) == 1)
{
lean_object* v_url_4799_; lean_object* v_rev_4800_; lean_object* v_url_4801_; lean_object* v_inputRev_x3f_4802_; lean_object* v___y_4804_; uint8_t v___x_4810_; 
v_url_4799_ = lean_ctor_get(v_val_4789_, 0);
v_rev_4800_ = lean_ctor_get(v_val_4789_, 1);
v_url_4801_ = lean_ctor_get(v_src_4798_, 0);
lean_inc_ref(v_url_4801_);
v_inputRev_x3f_4802_ = lean_ctor_get(v_src_4798_, 2);
lean_inc(v_inputRev_x3f_4802_);
lean_dec_ref_known(v_src_4798_, 4);
v___x_4810_ = lean_string_dec_eq(v_url_4799_, v_url_4801_);
lean_dec_ref(v_url_4801_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v_name_4788_);
v___x_4812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v_name_4788_, v___x_4811_, v___y_4775_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_dec_ref_known(v___x_4812_, 1);
v___y_4804_ = v___y_4775_;
goto v___jp_4803_;
}
else
{
lean_dec(v_inputRev_x3f_4802_);
return v___x_4812_;
}
}
else
{
v___y_4804_ = v___y_4775_;
goto v___jp_4803_;
}
v___jp_4803_:
{
lean_object* v___x_4805_; uint8_t v___x_4806_; 
v___x_4805_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_4800_);
v___x_4806_ = l_Option_instDecidableEq___redArg(v___x_4805_, v_rev_4800_, v_inputRev_x3f_4802_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v_name_4788_);
v___x_4808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v_name_4788_, v___x_4807_, v___y_4804_);
v___y_4783_ = v___x_4808_;
goto v___jp_4782_;
}
else
{
lean_object* v___x_4809_; 
v___x_4809_ = lean_box(0);
v_a_4778_ = v___x_4809_;
goto v___jp_4777_;
}
}
}
else
{
lean_dec_ref(v_src_4798_);
v___y_4793_ = v___y_4775_;
goto v___jp_4792_;
}
}
v___jp_4792_:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v_name_4788_);
v___x_4795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v_name_4788_, v___x_4794_, v___y_4793_);
v___y_4783_ = v___x_4795_;
goto v___jp_4782_;
}
}
else
{
lean_object* v___x_4813_; 
lean_dec(v___x_4790_);
v___x_4813_ = lean_box(0);
v_a_4778_ = v___x_4813_;
goto v___jp_4777_;
}
}
else
{
lean_object* v___x_4814_; 
v___x_4814_ = lean_box(0);
v_a_4778_ = v___x_4814_;
goto v___jp_4777_;
}
}
else
{
lean_object* v___x_4815_; 
v___x_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4815_, 0, v_b_4774_);
return v___x_4815_;
}
v___jp_4777_:
{
size_t v___x_4779_; size_t v___x_4780_; 
v___x_4779_ = ((size_t)1ULL);
v___x_4780_ = lean_usize_add(v_i_4772_, v___x_4779_);
v_i_4772_ = v___x_4780_;
v_b_4774_ = v_a_4778_;
goto _start;
}
v___jp_4782_:
{
if (lean_obj_tag(v___y_4783_) == 0)
{
lean_object* v_a_4784_; 
v_a_4784_ = lean_ctor_get(v___y_4783_, 0);
lean_inc(v_a_4784_);
lean_dec_ref_known(v___y_4783_, 1);
v_a_4778_ = v_a_4784_;
goto v___jp_4777_;
}
else
{
return v___y_4783_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_4816_, lean_object* v_as_4817_, lean_object* v_i_4818_, lean_object* v_stop_4819_, lean_object* v_b_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
size_t v_i_boxed_4823_; size_t v_stop_boxed_4824_; lean_object* v_res_4825_; 
v_i_boxed_4823_ = lean_unbox_usize(v_i_4818_);
lean_dec(v_i_4818_);
v_stop_boxed_4824_ = lean_unbox_usize(v_stop_4819_);
lean_dec(v_stop_4819_);
v_res_4825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4816_, v_as_4817_, v_i_boxed_4823_, v_stop_boxed_4824_, v_b_4820_, v___y_4821_);
lean_dec_ref(v___y_4821_);
lean_dec_ref(v_as_4817_);
lean_dec(v_pkgEntries_4816_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_4826_, lean_object* v_deps_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; uint8_t v___x_4833_; 
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4831_ = lean_array_get_size(v_deps_4827_);
v___x_4832_ = lean_box(0);
v___x_4833_ = lean_nat_dec_lt(v___x_4830_, v___x_4831_);
if (v___x_4833_ == 0)
{
lean_object* v___x_4834_; 
v___x_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4832_);
return v___x_4834_;
}
else
{
size_t v___x_4835_; size_t v___x_4836_; lean_object* v___x_4837_; 
v___x_4835_ = ((size_t)0ULL);
v___x_4836_ = lean_usize_of_nat(v___x_4831_);
v___x_4837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4826_, v_deps_4827_, v___x_4835_, v___x_4836_, v___x_4832_, v_a_4828_);
return v___x_4837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_4838_, lean_object* v_deps_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_4838_, v_deps_4839_, v_a_4840_);
lean_dec_ref(v_a_4840_);
lean_dec_ref(v_deps_4839_);
lean_dec(v_pkgEntries_4838_);
return v_res_4842_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_4843_, lean_object* v_x_4844_){
_start:
{
if (lean_obj_tag(v_x_4843_) == 0)
{
if (lean_obj_tag(v_x_4844_) == 0)
{
uint8_t v___x_4845_; 
v___x_4845_ = 1;
return v___x_4845_;
}
else
{
uint8_t v___x_4846_; 
v___x_4846_ = 0;
return v___x_4846_;
}
}
else
{
if (lean_obj_tag(v_x_4844_) == 0)
{
uint8_t v___x_4847_; 
v___x_4847_ = 0;
return v___x_4847_;
}
else
{
lean_object* v_val_4848_; lean_object* v_val_4849_; uint8_t v___x_4850_; 
v_val_4848_ = lean_ctor_get(v_x_4843_, 0);
v_val_4849_ = lean_ctor_get(v_x_4844_, 0);
v___x_4850_ = lean_string_dec_eq(v_val_4848_, v_val_4849_);
return v___x_4850_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_4851_, lean_object* v_x_4852_){
_start:
{
uint8_t v_res_4853_; lean_object* v_r_4854_; 
v_res_4853_ = l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_4851_, v_x_4852_);
lean_dec(v_x_4852_);
lean_dec(v_x_4851_);
v_r_4854_ = lean_box(v_res_4853_);
return v_r_4854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_pkg_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v_leanOpts_4863_, uint8_t v_reconfigure_4864_, lean_object* v_as_4865_, size_t v_i_4866_, size_t v_stop_4867_, lean_object* v_b_4868_, lean_object* v___y_4869_){
_start:
{
uint8_t v___x_4871_; 
v___x_4871_ = lean_usize_dec_eq(v_i_4866_, v_stop_4867_);
if (v___x_4871_ == 0)
{
lean_object* v_ws_4872_; lean_object* v_depIdxs_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_5003_; 
v_ws_4872_ = lean_ctor_get(v_b_4868_, 0);
v_depIdxs_4873_ = lean_ctor_get(v_b_4868_, 1);
v_isSharedCheck_5003_ = !lean_is_exclusive(v_b_4868_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4875_ = v_b_4868_;
v_isShared_4876_ = v_isSharedCheck_5003_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_depIdxs_4873_);
lean_inc(v_ws_4872_);
lean_dec(v_b_4868_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_5003_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v_lakeEnv_4877_; lean_object* v_packages_4878_; size_t v___x_4879_; size_t v___x_4880_; lean_object* v___x_4881_; lean_object* v___f_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
v_lakeEnv_4877_ = lean_ctor_get(v_ws_4872_, 0);
v_packages_4878_ = lean_ctor_get(v_ws_4872_, 4);
v___x_4879_ = ((size_t)1ULL);
v___x_4880_ = lean_usize_sub(v_i_4866_, v___x_4879_);
v___x_4881_ = lean_array_uget_borrowed(v_as_4865_, v___x_4880_);
lean_inc(v___x_4881_);
v___f_4882_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4882_, 0, v___x_4881_);
v___x_4883_ = lean_unsigned_to_nat(0u);
v___x_4884_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_4882_, v_packages_4878_, v___x_4883_);
if (lean_obj_tag(v___x_4884_) == 1)
{
lean_object* v_val_4885_; lean_object* v___x_4886_; lean_object* v___x_4888_; 
v_val_4885_ = lean_ctor_get(v___x_4884_, 0);
lean_inc(v_val_4885_);
lean_dec_ref_known(v___x_4884_, 1);
v___x_4886_ = lean_array_push(v_depIdxs_4873_, v_val_4885_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 1, v___x_4886_);
v___x_4888_ = v___x_4875_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_ws_4872_);
lean_ctor_set(v_reuseFailAlloc_4890_, 1, v___x_4886_);
v___x_4888_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
v_i_4866_ = v___x_4880_;
v_b_4868_ = v___x_4888_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_4891_; lean_object* v_baseName_4892_; lean_object* v_name_4893_; lean_object* v_opts_4894_; uint8_t v___x_4895_; 
lean_dec(v___x_4884_);
v_wsIdx_4891_ = lean_ctor_get(v_pkg_4860_, 0);
v_baseName_4892_ = lean_ctor_get(v_pkg_4860_, 1);
v_name_4893_ = lean_ctor_get(v___x_4881_, 0);
v_opts_4894_ = lean_ctor_get(v___x_4881_, 4);
v___x_4895_ = lean_name_eq(v_baseName_4892_, v_name_4893_);
if (v___x_4895_ == 0)
{
lean_object* v___x_4896_; 
v___x_4896_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_4861_, v_name_4893_);
if (lean_obj_tag(v___x_4896_) == 1)
{
lean_object* v_val_4897_; lean_object* v___x_4898_; lean_object* v_dir_4899_; lean_object* v___x_4900_; 
v_val_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc(v_val_4897_);
lean_dec_ref_known(v___x_4896_, 1);
v___x_4898_ = lean_array_fget_borrowed(v_packages_4878_, v___x_4883_);
v_dir_4899_ = lean_ctor_get(v___x_4898_, 4);
lean_inc_ref(v___y_4862_);
lean_inc_ref(v_dir_4899_);
v___x_4900_ = l_Lake_PackageEntry_materialize(v_val_4897_, v_lakeEnv_4877_, v_dir_4899_, v___y_4862_, v___y_4869_);
if (lean_obj_tag(v___x_4900_) == 0)
{
lean_object* v_a_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4957_; 
v_a_4901_ = lean_ctor_get(v___x_4900_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4903_ = v___x_4900_;
v_isShared_4904_ = v_isSharedCheck_4957_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_a_4901_);
lean_dec(v___x_4900_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4957_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4905_; lean_object* v_wsIdx_4906_; lean_object* v___x_4907_; 
v___x_4905_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_4906_ = lean_array_get_size(v_packages_4878_);
lean_inc_ref(v_leanOpts_4863_);
lean_inc(v_opts_4894_);
v___x_4907_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_4872_, v_a_4901_, v_opts_4894_, v_leanOpts_4863_, v_reconfigure_4864_, v___x_4905_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v_a_4908_; lean_object* v_a_4909_; lean_object* v___x_4910_; lean_object* v___x_4912_; 
lean_del_object(v___x_4903_);
v_a_4908_ = lean_ctor_get(v___x_4907_, 0);
lean_inc(v_a_4908_);
v_a_4909_ = lean_ctor_get(v___x_4907_, 1);
lean_inc(v_a_4909_);
lean_dec_ref_known(v___x_4907_, 2);
v___x_4910_ = lean_array_push(v_depIdxs_4873_, v_wsIdx_4906_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 1, v___x_4910_);
lean_ctor_set(v___x_4875_, 0, v_a_4908_);
v___x_4912_ = v___x_4875_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4908_);
lean_ctor_set(v_reuseFailAlloc_4929_, 1, v___x_4910_);
v___x_4912_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
lean_object* v___x_4913_; uint8_t v___x_4914_; 
v___x_4913_ = lean_array_get_size(v_a_4909_);
v___x_4914_ = lean_nat_dec_lt(v___x_4883_, v___x_4913_);
if (v___x_4914_ == 0)
{
lean_dec(v_a_4909_);
v_i_4866_ = v___x_4880_;
v_b_4868_ = v___x_4912_;
goto _start;
}
else
{
lean_object* v___x_4916_; size_t v___x_4917_; size_t v___x_4918_; lean_object* v___x_4919_; 
v___x_4916_ = lean_box(0);
v___x_4917_ = ((size_t)0ULL);
v___x_4918_ = lean_usize_of_nat(v___x_4913_);
v___x_4919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4909_, v___x_4917_, v___x_4918_, v___x_4916_, v___y_4869_);
lean_dec(v_a_4909_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_dec_ref_known(v___x_4919_, 1);
v_i_4866_ = v___x_4880_;
v_b_4868_ = v___x_4912_;
goto _start;
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_dec_ref(v___x_4912_);
lean_dec_ref(v_leanOpts_4863_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v_pkg_4860_);
v_a_4921_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4919_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4919_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
}
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4931_; uint8_t v___x_4932_; 
lean_del_object(v___x_4875_);
lean_dec_ref(v_depIdxs_4873_);
lean_dec_ref(v_leanOpts_4863_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v_pkg_4860_);
v_a_4930_ = lean_ctor_get(v___x_4907_, 1);
lean_inc(v_a_4930_);
lean_dec_ref_known(v___x_4907_, 2);
v___x_4931_ = lean_array_get_size(v_a_4930_);
v___x_4932_ = lean_nat_dec_lt(v___x_4883_, v___x_4931_);
if (v___x_4932_ == 0)
{
lean_object* v___x_4933_; lean_object* v___x_4935_; 
lean_dec(v_a_4930_);
v___x_4933_ = lean_box(0);
if (v_isShared_4904_ == 0)
{
lean_ctor_set_tag(v___x_4903_, 1);
lean_ctor_set(v___x_4903_, 0, v___x_4933_);
v___x_4935_ = v___x_4903_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4933_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
else
{
lean_object* v___x_4937_; size_t v___x_4938_; size_t v___x_4939_; lean_object* v___x_4940_; 
lean_del_object(v___x_4903_);
v___x_4937_ = lean_box(0);
v___x_4938_ = ((size_t)0ULL);
v___x_4939_ = lean_usize_of_nat(v___x_4931_);
v___x_4940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4930_, v___x_4938_, v___x_4939_, v___x_4937_, v___y_4869_);
lean_dec(v_a_4930_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4947_ == 0)
{
lean_object* v_unused_4948_; 
v_unused_4948_ = lean_ctor_get(v___x_4940_, 0);
lean_dec(v_unused_4948_);
v___x_4942_ = v___x_4940_;
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
else
{
lean_dec(v___x_4940_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set_tag(v___x_4942_, 1);
lean_ctor_set(v___x_4942_, 0, v___x_4937_);
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v___x_4937_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
v_a_4949_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4940_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4940_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4965_; 
lean_del_object(v___x_4875_);
lean_dec_ref(v_depIdxs_4873_);
lean_dec_ref(v_ws_4872_);
lean_dec_ref(v_leanOpts_4863_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v_pkg_4860_);
v_a_4958_ = lean_ctor_get(v___x_4900_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4960_ = v___x_4900_;
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4900_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4963_; 
if (v_isShared_4961_ == 0)
{
v___x_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4958_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
}
else
{
uint8_t v___x_4966_; 
lean_inc(v_baseName_4892_);
lean_inc(v_wsIdx_4891_);
lean_dec(v___x_4896_);
lean_del_object(v___x_4875_);
lean_dec_ref(v_depIdxs_4873_);
lean_dec_ref(v_ws_4872_);
lean_dec_ref(v_leanOpts_4863_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v_pkg_4860_);
v___x_4966_ = lean_nat_dec_eq(v_wsIdx_4891_, v___x_4883_);
lean_dec(v_wsIdx_4891_);
if (v___x_4966_ == 0)
{
lean_object* v___x_4967_; uint8_t v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; uint8_t v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_4968_ = 1;
lean_inc(v_name_4893_);
v___x_4969_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4893_, v___x_4968_);
v___x_4970_ = lean_string_append(v___x_4967_, v___x_4969_);
lean_dec_ref(v___x_4969_);
v___x_4971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_4972_ = lean_string_append(v___x_4970_, v___x_4971_);
v___x_4973_ = l_Lean_Name_toString(v_baseName_4892_, v___x_4966_);
v___x_4974_ = lean_string_append(v___x_4972_, v___x_4973_);
lean_dec_ref(v___x_4973_);
v___x_4975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_4976_ = lean_string_append(v___x_4974_, v___x_4975_);
v___x_4977_ = 3;
v___x_4978_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4978_, 0, v___x_4976_);
lean_ctor_set_uint8(v___x_4978_, sizeof(void*)*1, v___x_4977_);
lean_inc_ref(v___y_4869_);
v___x_4979_ = lean_apply_2(v___y_4869_, v___x_4978_, lean_box(0));
v___x_4980_ = lean_box(0);
v___x_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4980_);
return v___x_4981_;
}
else
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; uint8_t v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
lean_dec(v_baseName_4892_);
v___x_4982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_4893_);
v___x_4983_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4893_, v___x_4966_);
v___x_4984_ = lean_string_append(v___x_4982_, v___x_4983_);
v___x_4985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_4986_ = lean_string_append(v___x_4984_, v___x_4985_);
v___x_4987_ = lean_string_append(v___x_4986_, v___x_4983_);
lean_dec_ref(v___x_4983_);
v___x_4988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_4989_ = lean_string_append(v___x_4987_, v___x_4988_);
v___x_4990_ = 3;
v___x_4991_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4991_, 0, v___x_4989_);
lean_ctor_set_uint8(v___x_4991_, sizeof(void*)*1, v___x_4990_);
lean_inc_ref(v___y_4869_);
v___x_4992_ = lean_apply_2(v___y_4869_, v___x_4991_, lean_box(0));
v___x_4993_ = lean_box(0);
v___x_4994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
return v___x_4994_;
}
}
}
else
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; uint8_t v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
lean_inc(v_baseName_4892_);
lean_del_object(v___x_4875_);
lean_dec_ref(v_depIdxs_4873_);
lean_dec_ref(v_ws_4872_);
lean_dec_ref(v_leanOpts_4863_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v_pkg_4860_);
v___x_4995_ = l_Lean_Name_toString(v_baseName_4892_, v___x_4871_);
v___x_4996_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_4997_ = lean_string_append(v___x_4995_, v___x_4996_);
v___x_4998_ = 3;
v___x_4999_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4999_, 0, v___x_4997_);
lean_ctor_set_uint8(v___x_4999_, sizeof(void*)*1, v___x_4998_);
lean_inc_ref(v___y_4869_);
v___x_5000_ = lean_apply_2(v___y_4869_, v___x_4999_, lean_box(0));
v___x_5001_ = lean_box(0);
v___x_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5002_, 0, v___x_5001_);
return v___x_5002_;
}
}
}
}
else
{
lean_object* v___x_5004_; 
lean_dec_ref(v_leanOpts_4863_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v_pkg_4860_);
v___x_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5004_, 0, v_b_4868_);
return v___x_5004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_pkg_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v_leanOpts_5008_, lean_object* v_reconfigure_5009_, lean_object* v_as_5010_, lean_object* v_i_5011_, lean_object* v_stop_5012_, lean_object* v_b_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
uint8_t v_reconfigure_boxed_5016_; size_t v_i_boxed_5017_; size_t v_stop_boxed_5018_; lean_object* v_res_5019_; 
v_reconfigure_boxed_5016_ = lean_unbox(v_reconfigure_5009_);
v_i_boxed_5017_ = lean_unbox_usize(v_i_5011_);
lean_dec(v_i_5011_);
v_stop_boxed_5018_ = lean_unbox_usize(v_stop_5012_);
lean_dec(v_stop_5012_);
v_res_5019_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5005_, v___y_5006_, v___y_5007_, v_leanOpts_5008_, v_reconfigure_boxed_5016_, v_as_5010_, v_i_boxed_5017_, v_stop_boxed_5018_, v_b_5013_, v___y_5014_);
lean_dec_ref(v___y_5014_);
lean_dec_ref(v_as_5010_);
lean_dec(v___y_5006_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_start_5020_, lean_object* v_pkg_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v_leanOpts_5024_, uint8_t v_reconfigure_5025_, lean_object* v_as_5026_, size_t v_i_5027_, size_t v_stop_5028_, lean_object* v_b_5029_, lean_object* v___y_5030_){
_start:
{
uint8_t v___x_5032_; 
v___x_5032_ = lean_usize_dec_eq(v_i_5027_, v_stop_5028_);
if (v___x_5032_ == 0)
{
lean_object* v_ws_5033_; lean_object* v_depIdxs_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5164_; 
v_ws_5033_ = lean_ctor_get(v_b_5029_, 0);
v_depIdxs_5034_ = lean_ctor_get(v_b_5029_, 1);
v_isSharedCheck_5164_ = !lean_is_exclusive(v_b_5029_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5036_ = v_b_5029_;
v_isShared_5037_ = v_isSharedCheck_5164_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_depIdxs_5034_);
lean_inc(v_ws_5033_);
lean_dec(v_b_5029_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5164_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v_lakeEnv_5038_; lean_object* v_packages_5039_; size_t v___x_5040_; size_t v___x_5041_; lean_object* v___x_5042_; lean_object* v___f_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v_lakeEnv_5038_ = lean_ctor_get(v_ws_5033_, 0);
v_packages_5039_ = lean_ctor_get(v_ws_5033_, 4);
v___x_5040_ = ((size_t)1ULL);
v___x_5041_ = lean_usize_sub(v_i_5027_, v___x_5040_);
v___x_5042_ = lean_array_uget_borrowed(v_as_5026_, v___x_5041_);
lean_inc(v___x_5042_);
v___f_5043_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__9___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5043_, 0, v___x_5042_);
v___x_5044_ = lean_unsigned_to_nat(0u);
v___x_5045_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5043_, v_packages_5039_, v___x_5044_);
if (lean_obj_tag(v___x_5045_) == 1)
{
lean_object* v_val_5046_; lean_object* v___x_5047_; lean_object* v___x_5049_; 
v_val_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_val_5046_);
lean_dec_ref_known(v___x_5045_, 1);
v___x_5047_ = lean_array_push(v_depIdxs_5034_, v_val_5046_);
if (v_isShared_5037_ == 0)
{
lean_ctor_set(v___x_5036_, 1, v___x_5047_);
v___x_5049_ = v___x_5036_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_ws_5033_);
lean_ctor_set(v_reuseFailAlloc_5051_, 1, v___x_5047_);
v___x_5049_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
lean_object* v___x_5050_; 
v___x_5050_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5021_, v___y_5022_, v___y_5023_, v_leanOpts_5024_, v_reconfigure_5025_, v_as_5026_, v___x_5041_, v_stop_5028_, v___x_5049_, v___y_5030_);
return v___x_5050_;
}
}
else
{
lean_object* v_wsIdx_5052_; lean_object* v_baseName_5053_; lean_object* v_name_5054_; lean_object* v_opts_5055_; uint8_t v___x_5056_; 
lean_dec(v___x_5045_);
v_wsIdx_5052_ = lean_ctor_get(v_pkg_5021_, 0);
v_baseName_5053_ = lean_ctor_get(v_pkg_5021_, 1);
v_name_5054_ = lean_ctor_get(v___x_5042_, 0);
v_opts_5055_ = lean_ctor_get(v___x_5042_, 4);
v___x_5056_ = lean_name_eq(v_baseName_5053_, v_name_5054_);
if (v___x_5056_ == 0)
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5022_, v_name_5054_);
if (lean_obj_tag(v___x_5057_) == 1)
{
lean_object* v_val_5058_; lean_object* v___x_5059_; lean_object* v_dir_5060_; lean_object* v___x_5061_; 
v_val_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_val_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v___x_5059_ = lean_array_fget_borrowed(v_packages_5039_, v___x_5044_);
v_dir_5060_ = lean_ctor_get(v___x_5059_, 4);
lean_inc_ref(v___y_5023_);
lean_inc_ref(v_dir_5060_);
v___x_5061_ = l_Lake_PackageEntry_materialize(v_val_5058_, v_lakeEnv_5038_, v_dir_5060_, v___y_5023_, v___y_5030_);
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5118_; 
v_a_5062_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5064_ = v___x_5061_;
v_isShared_5065_ = v_isSharedCheck_5118_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v___x_5061_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5118_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5066_; lean_object* v_wsIdx_5067_; lean_object* v___x_5068_; 
v___x_5066_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_5067_ = lean_array_get_size(v_packages_5039_);
lean_inc_ref(v_leanOpts_5024_);
lean_inc(v_opts_5055_);
v___x_5068_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5033_, v_a_5062_, v_opts_5055_, v_leanOpts_5024_, v_reconfigure_5025_, v___x_5066_);
if (lean_obj_tag(v___x_5068_) == 0)
{
lean_object* v_a_5069_; lean_object* v_a_5070_; lean_object* v___x_5071_; lean_object* v___x_5073_; 
lean_del_object(v___x_5064_);
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
lean_inc(v_a_5069_);
v_a_5070_ = lean_ctor_get(v___x_5068_, 1);
lean_inc(v_a_5070_);
lean_dec_ref_known(v___x_5068_, 2);
v___x_5071_ = lean_array_push(v_depIdxs_5034_, v_wsIdx_5067_);
if (v_isShared_5037_ == 0)
{
lean_ctor_set(v___x_5036_, 1, v___x_5071_);
lean_ctor_set(v___x_5036_, 0, v_a_5069_);
v___x_5073_ = v___x_5036_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_a_5069_);
lean_ctor_set(v_reuseFailAlloc_5090_, 1, v___x_5071_);
v___x_5073_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
lean_object* v___x_5074_; uint8_t v___x_5075_; 
v___x_5074_ = lean_array_get_size(v_a_5070_);
v___x_5075_ = lean_nat_dec_lt(v___x_5044_, v___x_5074_);
if (v___x_5075_ == 0)
{
lean_object* v___x_5076_; 
lean_dec(v_a_5070_);
v___x_5076_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5021_, v___y_5022_, v___y_5023_, v_leanOpts_5024_, v_reconfigure_5025_, v_as_5026_, v___x_5041_, v_stop_5028_, v___x_5073_, v___y_5030_);
return v___x_5076_;
}
else
{
lean_object* v___x_5077_; size_t v___x_5078_; size_t v___x_5079_; lean_object* v___x_5080_; 
v___x_5077_ = lean_box(0);
v___x_5078_ = ((size_t)0ULL);
v___x_5079_ = lean_usize_of_nat(v___x_5074_);
v___x_5080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5070_, v___x_5078_, v___x_5079_, v___x_5077_, v___y_5030_);
lean_dec(v_a_5070_);
if (lean_obj_tag(v___x_5080_) == 0)
{
lean_object* v___x_5081_; 
lean_dec_ref_known(v___x_5080_, 1);
v___x_5081_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5021_, v___y_5022_, v___y_5023_, v_leanOpts_5024_, v_reconfigure_5025_, v_as_5026_, v___x_5041_, v_stop_5028_, v___x_5073_, v___y_5030_);
return v___x_5081_;
}
else
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5089_; 
lean_dec_ref(v___x_5073_);
lean_dec_ref(v_leanOpts_5024_);
lean_dec_ref(v___y_5023_);
lean_dec_ref(v_pkg_5021_);
v_a_5082_ = lean_ctor_get(v___x_5080_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5080_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5084_ = v___x_5080_;
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5080_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5087_; 
if (v_isShared_5085_ == 0)
{
v___x_5087_ = v___x_5084_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
}
}
else
{
lean_object* v_a_5091_; lean_object* v___x_5092_; uint8_t v___x_5093_; 
lean_del_object(v___x_5036_);
lean_dec_ref(v_depIdxs_5034_);
lean_dec_ref(v_leanOpts_5024_);
lean_dec_ref(v___y_5023_);
lean_dec_ref(v_pkg_5021_);
v_a_5091_ = lean_ctor_get(v___x_5068_, 1);
lean_inc(v_a_5091_);
lean_dec_ref_known(v___x_5068_, 2);
v___x_5092_ = lean_array_get_size(v_a_5091_);
v___x_5093_ = lean_nat_dec_lt(v___x_5044_, v___x_5092_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; lean_object* v___x_5096_; 
lean_dec(v_a_5091_);
v___x_5094_ = lean_box(0);
if (v_isShared_5065_ == 0)
{
lean_ctor_set_tag(v___x_5064_, 1);
lean_ctor_set(v___x_5064_, 0, v___x_5094_);
v___x_5096_ = v___x_5064_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5094_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
else
{
lean_object* v___x_5098_; size_t v___x_5099_; size_t v___x_5100_; lean_object* v___x_5101_; 
lean_del_object(v___x_5064_);
v___x_5098_ = lean_box(0);
v___x_5099_ = ((size_t)0ULL);
v___x_5100_ = lean_usize_of_nat(v___x_5092_);
v___x_5101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5091_, v___x_5099_, v___x_5100_, v___x_5098_, v___y_5030_);
lean_dec(v_a_5091_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5108_; 
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5108_ == 0)
{
lean_object* v_unused_5109_; 
v_unused_5109_ = lean_ctor_get(v___x_5101_, 0);
lean_dec(v_unused_5109_);
v___x_5103_ = v___x_5101_;
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
else
{
lean_dec(v___x_5101_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5106_; 
if (v_isShared_5104_ == 0)
{
lean_ctor_set_tag(v___x_5103_, 1);
lean_ctor_set(v___x_5103_, 0, v___x_5098_);
v___x_5106_ = v___x_5103_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v___x_5098_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
v_a_5110_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v___x_5101_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5101_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5113_ == 0)
{
v___x_5115_ = v___x_5112_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5110_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_del_object(v___x_5036_);
lean_dec_ref(v_depIdxs_5034_);
lean_dec_ref(v_ws_5033_);
lean_dec_ref(v_leanOpts_5024_);
lean_dec_ref(v___y_5023_);
lean_dec_ref(v_pkg_5021_);
v_a_5119_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_5061_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_5061_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
else
{
uint8_t v___x_5127_; 
lean_inc(v_baseName_5053_);
lean_inc(v_wsIdx_5052_);
lean_dec(v___x_5057_);
lean_del_object(v___x_5036_);
lean_dec_ref(v_depIdxs_5034_);
lean_dec_ref(v_ws_5033_);
lean_dec_ref(v_leanOpts_5024_);
lean_dec_ref(v___y_5023_);
lean_dec_ref(v_pkg_5021_);
v___x_5127_ = lean_nat_dec_eq(v_wsIdx_5052_, v___x_5044_);
lean_dec(v_wsIdx_5052_);
if (v___x_5127_ == 0)
{
lean_object* v___x_5128_; uint8_t v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; uint8_t v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; 
v___x_5128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5129_ = 1;
lean_inc(v_name_5054_);
v___x_5130_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5054_, v___x_5129_);
v___x_5131_ = lean_string_append(v___x_5128_, v___x_5130_);
lean_dec_ref(v___x_5130_);
v___x_5132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5133_ = lean_string_append(v___x_5131_, v___x_5132_);
v___x_5134_ = l_Lean_Name_toString(v_baseName_5053_, v___x_5127_);
v___x_5135_ = lean_string_append(v___x_5133_, v___x_5134_);
lean_dec_ref(v___x_5134_);
v___x_5136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5137_ = lean_string_append(v___x_5135_, v___x_5136_);
v___x_5138_ = 3;
v___x_5139_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5139_, 0, v___x_5137_);
lean_ctor_set_uint8(v___x_5139_, sizeof(void*)*1, v___x_5138_);
lean_inc_ref(v___y_5030_);
v___x_5140_ = lean_apply_2(v___y_5030_, v___x_5139_, lean_box(0));
v___x_5141_ = lean_box(0);
v___x_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5142_, 0, v___x_5141_);
return v___x_5142_;
}
else
{
lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; uint8_t v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; 
lean_dec(v_baseName_5053_);
v___x_5143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5054_);
v___x_5144_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5054_, v___x_5127_);
v___x_5145_ = lean_string_append(v___x_5143_, v___x_5144_);
v___x_5146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5147_ = lean_string_append(v___x_5145_, v___x_5146_);
v___x_5148_ = lean_string_append(v___x_5147_, v___x_5144_);
lean_dec_ref(v___x_5144_);
v___x_5149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5150_ = lean_string_append(v___x_5148_, v___x_5149_);
v___x_5151_ = 3;
v___x_5152_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5152_, 0, v___x_5150_);
lean_ctor_set_uint8(v___x_5152_, sizeof(void*)*1, v___x_5151_);
lean_inc_ref(v___y_5030_);
v___x_5153_ = lean_apply_2(v___y_5030_, v___x_5152_, lean_box(0));
v___x_5154_ = lean_box(0);
v___x_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5155_, 0, v___x_5154_);
return v___x_5155_;
}
}
}
else
{
lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; 
lean_inc(v_baseName_5053_);
lean_del_object(v___x_5036_);
lean_dec_ref(v_depIdxs_5034_);
lean_dec_ref(v_ws_5033_);
lean_dec_ref(v_leanOpts_5024_);
lean_dec_ref(v___y_5023_);
lean_dec_ref(v_pkg_5021_);
v___x_5156_ = l_Lean_Name_toString(v_baseName_5053_, v___x_5032_);
v___x_5157_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5158_ = lean_string_append(v___x_5156_, v___x_5157_);
v___x_5159_ = 3;
v___x_5160_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5160_, 0, v___x_5158_);
lean_ctor_set_uint8(v___x_5160_, sizeof(void*)*1, v___x_5159_);
lean_inc_ref(v___y_5030_);
v___x_5161_ = lean_apply_2(v___y_5030_, v___x_5160_, lean_box(0));
v___x_5162_ = lean_box(0);
v___x_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5163_, 0, v___x_5162_);
return v___x_5163_;
}
}
}
}
else
{
lean_object* v___x_5165_; 
lean_dec_ref(v_leanOpts_5024_);
lean_dec_ref(v___y_5023_);
lean_dec_ref(v_pkg_5021_);
v___x_5165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5165_, 0, v_b_5029_);
return v___x_5165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_start_5166_, lean_object* v_pkg_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v_leanOpts_5170_, lean_object* v_reconfigure_5171_, lean_object* v_as_5172_, lean_object* v_i_5173_, lean_object* v_stop_5174_, lean_object* v_b_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_){
_start:
{
uint8_t v_reconfigure_boxed_5178_; size_t v_i_boxed_5179_; size_t v_stop_boxed_5180_; lean_object* v_res_5181_; 
v_reconfigure_boxed_5178_ = lean_unbox(v_reconfigure_5171_);
v_i_boxed_5179_ = lean_unbox_usize(v_i_5173_);
lean_dec(v_i_5173_);
v_stop_boxed_5180_ = lean_unbox_usize(v_stop_5174_);
lean_dec(v_stop_5174_);
v_res_5181_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5166_, v_pkg_5167_, v___y_5168_, v___y_5169_, v_leanOpts_5170_, v_reconfigure_boxed_5178_, v_as_5172_, v_i_boxed_5179_, v_stop_boxed_5180_, v_b_5175_, v___y_5176_);
lean_dec_ref(v___y_5176_);
lean_dec_ref(v_as_5172_);
lean_dec(v___y_5168_);
lean_dec(v_start_5166_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v_leanOpts_5184_, uint8_t v_reconfigure_5185_, lean_object* v_ws_5186_, lean_object* v_i_5187_, lean_object* v_next_5188_, lean_object* v___y_5189_){
_start:
{
lean_object* v_packages_5191_; lean_object* v_pkg_5192_; lean_object* v_ws_5194_; lean_object* v_depIdxs_5195_; lean_object* v___y_5196_; lean_object* v_____x_5206_; lean_object* v___y_5207_; lean_object* v_depConfigs_5210_; lean_object* v_start_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v_s_5214_; lean_object* v___x_5215_; uint8_t v___x_5216_; 
v_packages_5191_ = lean_ctor_get(v_ws_5186_, 4);
v_pkg_5192_ = lean_array_fget(v_packages_5191_, v_i_5187_);
lean_dec(v_i_5187_);
v_depConfigs_5210_ = lean_ctor_get(v_pkg_5192_, 12);
v_start_5211_ = lean_array_get_size(v_packages_5191_);
v___x_5212_ = lean_array_get_size(v_depConfigs_5210_);
v___x_5213_ = lean_mk_empty_array_with_capacity(v___x_5212_);
lean_inc_ref(v___x_5213_);
lean_inc_ref(v_ws_5186_);
v_s_5214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5214_, 0, v_ws_5186_);
lean_ctor_set(v_s_5214_, 1, v___x_5213_);
v___x_5215_ = lean_unsigned_to_nat(0u);
v___x_5216_ = lean_nat_dec_le(v___x_5212_, v___x_5212_);
if (v___x_5216_ == 0)
{
uint8_t v___x_5217_; 
v___x_5217_ = lean_nat_dec_lt(v___x_5215_, v___x_5212_);
if (v___x_5217_ == 0)
{
lean_object* v_ws_5218_; lean_object* v_packages_5219_; lean_object* v___x_5220_; uint8_t v___x_5221_; 
lean_dec_ref_known(v_s_5214_, 2);
v_ws_5218_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5186_, v_pkg_5192_, v___x_5213_);
v_packages_5219_ = lean_ctor_get(v_ws_5218_, 4);
v___x_5220_ = lean_array_get_size(v_packages_5219_);
v___x_5221_ = lean_nat_dec_lt(v_next_5188_, v___x_5220_);
if (v___x_5221_ == 0)
{
lean_object* v___x_5222_; 
lean_dec(v_next_5188_);
lean_dec_ref(v_leanOpts_5184_);
lean_dec_ref(v___y_5183_);
v___x_5222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5222_, 0, v_ws_5218_);
return v___x_5222_;
}
else
{
lean_object* v___x_5223_; lean_object* v___x_5224_; 
v___x_5223_ = lean_unsigned_to_nat(1u);
v___x_5224_ = lean_nat_add(v_next_5188_, v___x_5223_);
v_ws_5186_ = v_ws_5218_;
v_i_5187_ = v_next_5188_;
v_next_5188_ = v___x_5224_;
goto _start;
}
}
else
{
size_t v___x_5226_; size_t v___x_5227_; lean_object* v___x_5228_; 
lean_dec_ref(v___x_5213_);
lean_dec_ref(v_ws_5186_);
v___x_5226_ = lean_usize_of_nat(v___x_5212_);
v___x_5227_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5184_);
lean_inc_ref(v___y_5183_);
lean_inc(v_pkg_5192_);
v___x_5228_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5211_, v_pkg_5192_, v___y_5182_, v___y_5183_, v_leanOpts_5184_, v_reconfigure_5185_, v_depConfigs_5210_, v___x_5226_, v___x_5227_, v_s_5214_, v___y_5189_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v_a_5229_; 
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc(v_a_5229_);
lean_dec_ref_known(v___x_5228_, 1);
v_____x_5206_ = v_a_5229_;
v___y_5207_ = v___y_5189_;
goto v___jp_5205_;
}
else
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5237_; 
lean_dec(v_pkg_5192_);
lean_dec(v_next_5188_);
lean_dec_ref(v_leanOpts_5184_);
lean_dec_ref(v___y_5183_);
v_a_5230_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5232_ = v___x_5228_;
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5228_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5235_; 
if (v_isShared_5233_ == 0)
{
v___x_5235_ = v___x_5232_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_a_5230_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
}
}
}
else
{
uint8_t v___x_5238_; 
v___x_5238_ = lean_nat_dec_lt(v___x_5215_, v___x_5212_);
if (v___x_5238_ == 0)
{
lean_dec_ref_known(v_s_5214_, 2);
v_ws_5194_ = v_ws_5186_;
v_depIdxs_5195_ = v___x_5213_;
v___y_5196_ = v___y_5189_;
goto v___jp_5193_;
}
else
{
size_t v___x_5239_; size_t v___x_5240_; lean_object* v___x_5241_; 
lean_dec_ref(v___x_5213_);
lean_dec_ref(v_ws_5186_);
v___x_5239_ = lean_usize_of_nat(v___x_5212_);
v___x_5240_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5184_);
lean_inc_ref(v___y_5183_);
lean_inc(v_pkg_5192_);
v___x_5241_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5211_, v_pkg_5192_, v___y_5182_, v___y_5183_, v_leanOpts_5184_, v_reconfigure_5185_, v_depConfigs_5210_, v___x_5239_, v___x_5240_, v_s_5214_, v___y_5189_);
if (lean_obj_tag(v___x_5241_) == 0)
{
lean_object* v_a_5242_; 
v_a_5242_ = lean_ctor_get(v___x_5241_, 0);
lean_inc(v_a_5242_);
lean_dec_ref_known(v___x_5241_, 1);
v_____x_5206_ = v_a_5242_;
v___y_5207_ = v___y_5189_;
goto v___jp_5205_;
}
else
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5250_; 
lean_dec(v_pkg_5192_);
lean_dec(v_next_5188_);
lean_dec_ref(v_leanOpts_5184_);
lean_dec_ref(v___y_5183_);
v_a_5243_ = lean_ctor_get(v___x_5241_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5241_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5241_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5241_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5248_; 
if (v_isShared_5246_ == 0)
{
v___x_5248_ = v___x_5245_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_a_5243_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
return v___x_5248_;
}
}
}
}
}
v___jp_5193_:
{
lean_object* v_ws_5197_; lean_object* v_packages_5198_; lean_object* v___x_5199_; uint8_t v___x_5200_; 
v_ws_5197_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5194_, v_pkg_5192_, v_depIdxs_5195_);
v_packages_5198_ = lean_ctor_get(v_ws_5197_, 4);
v___x_5199_ = lean_array_get_size(v_packages_5198_);
v___x_5200_ = lean_nat_dec_lt(v_next_5188_, v___x_5199_);
if (v___x_5200_ == 0)
{
lean_object* v___x_5201_; 
lean_dec(v_next_5188_);
lean_dec_ref(v_leanOpts_5184_);
lean_dec_ref(v___y_5183_);
v___x_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5201_, 0, v_ws_5197_);
return v___x_5201_;
}
else
{
lean_object* v___x_5202_; lean_object* v___x_5203_; 
v___x_5202_ = lean_unsigned_to_nat(1u);
v___x_5203_ = lean_nat_add(v_next_5188_, v___x_5202_);
v_ws_5186_ = v_ws_5197_;
v_i_5187_ = v_next_5188_;
v_next_5188_ = v___x_5203_;
v___y_5189_ = v___y_5196_;
goto _start;
}
}
v___jp_5205_:
{
lean_object* v_ws_5208_; lean_object* v_depIdxs_5209_; 
v_ws_5208_ = lean_ctor_get(v_____x_5206_, 0);
lean_inc_ref(v_ws_5208_);
v_depIdxs_5209_ = lean_ctor_get(v_____x_5206_, 1);
lean_inc_ref(v_depIdxs_5209_);
lean_dec_ref(v_____x_5206_);
v_ws_5194_ = v_ws_5208_;
v_depIdxs_5195_ = v_depIdxs_5209_;
v___y_5196_ = v___y_5207_;
goto v___jp_5193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v_leanOpts_5253_, lean_object* v_reconfigure_5254_, lean_object* v_ws_5255_, lean_object* v_i_5256_, lean_object* v_next_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_){
_start:
{
uint8_t v_reconfigure_boxed_5260_; lean_object* v_res_5261_; 
v_reconfigure_boxed_5260_ = lean_unbox(v_reconfigure_5254_);
v_res_5261_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5251_, v___y_5252_, v_leanOpts_5253_, v_reconfigure_boxed_5260_, v_ws_5255_, v_i_5256_, v_next_5257_, v___y_5258_);
lean_dec_ref(v___y_5258_);
lean_dec(v___y_5251_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(lean_object* v_as_5262_, size_t v_i_5263_, size_t v_stop_5264_, lean_object* v_b_5265_){
_start:
{
uint8_t v___x_5266_; 
v___x_5266_ = lean_usize_dec_eq(v_i_5263_, v_stop_5264_);
if (v___x_5266_ == 0)
{
lean_object* v___x_5267_; lean_object* v_name_5268_; lean_object* v___x_5269_; size_t v___x_5270_; size_t v___x_5271_; 
v___x_5267_ = lean_array_uget_borrowed(v_as_5262_, v_i_5263_);
v_name_5268_ = lean_ctor_get(v___x_5267_, 0);
lean_inc(v___x_5267_);
lean_inc(v_name_5268_);
v___x_5269_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5268_, v___x_5267_, v_b_5265_);
v___x_5270_ = ((size_t)1ULL);
v___x_5271_ = lean_usize_add(v_i_5263_, v___x_5270_);
v_i_5263_ = v___x_5271_;
v_b_5265_ = v___x_5269_;
goto _start;
}
else
{
return v_b_5265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2___boxed(lean_object* v_as_5273_, lean_object* v_i_5274_, lean_object* v_stop_5275_, lean_object* v_b_5276_){
_start:
{
size_t v_i_boxed_5277_; size_t v_stop_boxed_5278_; lean_object* v_res_5279_; 
v_i_boxed_5277_ = lean_unbox_usize(v_i_5274_);
lean_dec(v_i_5274_);
v_stop_boxed_5278_ = lean_unbox_usize(v_stop_5275_);
lean_dec(v_stop_5275_);
v_res_5279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5273_, v_i_boxed_5277_, v_stop_boxed_5278_, v_b_5276_);
lean_dec_ref(v_as_5273_);
return v_res_5279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5280_, size_t v_i_5281_, size_t v_stop_5282_, lean_object* v_b_5283_){
_start:
{
uint8_t v___x_5284_; 
v___x_5284_ = lean_usize_dec_eq(v_i_5281_, v_stop_5282_);
if (v___x_5284_ == 0)
{
lean_object* v___x_5285_; lean_object* v_name_5286_; lean_object* v___x_5287_; size_t v___x_5288_; size_t v___x_5289_; lean_object* v___x_5290_; 
v___x_5285_ = lean_array_uget_borrowed(v_as_5280_, v_i_5281_);
v_name_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc(v___x_5285_);
lean_inc(v_name_5286_);
v___x_5287_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5286_, v___x_5285_, v_b_5283_);
v___x_5288_ = ((size_t)1ULL);
v___x_5289_ = lean_usize_add(v_i_5281_, v___x_5288_);
v___x_5290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5280_, v___x_5289_, v_stop_5282_, v___x_5287_);
return v___x_5290_;
}
else
{
return v_b_5283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5291_, lean_object* v_i_5292_, lean_object* v_stop_5293_, lean_object* v_b_5294_){
_start:
{
size_t v_i_boxed_5295_; size_t v_stop_boxed_5296_; lean_object* v_res_5297_; 
v_i_boxed_5295_ = lean_unbox_usize(v_i_5292_);
lean_dec(v_i_5292_);
v_stop_boxed_5296_ = lean_unbox_usize(v_stop_5293_);
lean_dec(v_stop_5293_);
v_res_5297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5291_, v_i_boxed_5295_, v_stop_boxed_5296_, v_b_5294_);
lean_dec_ref(v_as_5291_);
return v_res_5297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5307_, lean_object* v_manifest_5308_, lean_object* v_leanOpts_5309_, uint8_t v_reconfigure_5310_, lean_object* v_overrides_5311_, lean_object* v_a_5312_){
_start:
{
lean_object* v___y_5315_; lean_object* v___y_5316_; lean_object* v___y_5317_; lean_object* v___y_5318_; lean_object* v___y_5319_; lean_object* v___y_5332_; lean_object* v___y_5333_; lean_object* v___y_5334_; lean_object* v___y_5335_; lean_object* v___y_5336_; lean_object* v___y_5337_; lean_object* v___y_5338_; lean_object* v___y_5346_; lean_object* v___y_5347_; lean_object* v___y_5348_; lean_object* v___y_5349_; lean_object* v___y_5350_; lean_object* v___y_5351_; lean_object* v___y_5352_; lean_object* v___y_5359_; lean_object* v___y_5360_; lean_object* v___y_5361_; lean_object* v___y_5362_; lean_object* v_packagesDir_x3f_5401_; lean_object* v_packages_5402_; lean_object* v___y_5404_; lean_object* v___y_5405_; lean_object* v___y_5414_; lean_object* v___x_5422_; lean_object* v___x_5423_; uint8_t v___x_5424_; 
v_packagesDir_x3f_5401_ = lean_ctor_get(v_manifest_5308_, 2);
lean_inc(v_packagesDir_x3f_5401_);
v_packages_5402_ = lean_ctor_get(v_manifest_5308_, 3);
lean_inc_ref(v_packages_5402_);
lean_dec_ref(v_manifest_5308_);
v___x_5422_ = lean_array_get_size(v_packages_5402_);
v___x_5423_ = lean_unsigned_to_nat(0u);
v___x_5424_ = lean_nat_dec_eq(v___x_5422_, v___x_5423_);
if (v___x_5424_ == 0)
{
lean_object* v_packages_5425_; lean_object* v___x_5426_; lean_object* v_config_5427_; lean_object* v_toWorkspaceConfig_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; uint8_t v___x_5432_; 
v_packages_5425_ = lean_ctor_get(v_ws_5307_, 4);
v___x_5426_ = lean_array_fget_borrowed(v_packages_5425_, v___x_5423_);
v_config_5427_ = lean_ctor_get(v___x_5426_, 6);
v_toWorkspaceConfig_5428_ = lean_ctor_get(v_config_5427_, 0);
lean_inc_ref(v_toWorkspaceConfig_5428_);
v___x_5429_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5428_);
v___x_5430_ = l_Lake_mkRelPathString(v___x_5429_);
v___x_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5431_, 0, v___x_5430_);
v___x_5432_ = l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5401_, v___x_5431_);
lean_dec_ref_known(v___x_5431_, 1);
if (v___x_5432_ == 0)
{
lean_object* v___x_5433_; lean_object* v___x_5434_; 
v___x_5433_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5312_);
v___x_5434_ = lean_apply_2(v_a_5312_, v___x_5433_, lean_box(0));
v___y_5414_ = v_a_5312_;
goto v___jp_5413_;
}
else
{
v___y_5414_ = v_a_5312_;
goto v___jp_5413_;
}
}
else
{
v___y_5414_ = v_a_5312_;
goto v___jp_5413_;
}
v___jp_5314_:
{
lean_object* v___x_5320_; lean_object* v___x_5321_; 
v___x_5320_ = lean_array_get_size(v___y_5315_);
lean_dec_ref(v___y_5315_);
v___x_5321_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5319_, v___y_5318_, v_leanOpts_5309_, v_reconfigure_5310_, v_ws_5307_, v___y_5317_, v___x_5320_, v___y_5316_);
lean_dec(v___y_5319_);
if (lean_obj_tag(v___x_5321_) == 0)
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5330_; 
v_a_5322_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5330_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5330_ == 0)
{
v___x_5324_ = v___x_5321_;
v_isShared_5325_ = v_isSharedCheck_5330_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5321_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5330_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5326_; lean_object* v___x_5328_; 
v___x_5326_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_a_5322_);
if (v_isShared_5325_ == 0)
{
lean_ctor_set(v___x_5324_, 0, v___x_5326_);
v___x_5328_ = v___x_5324_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v___x_5326_);
v___x_5328_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
return v___x_5328_;
}
}
}
else
{
return v___x_5321_;
}
}
v___jp_5331_:
{
if (lean_obj_tag(v___y_5338_) == 0)
{
lean_dec_ref(v___y_5337_);
v___y_5315_ = v___y_5332_;
v___y_5316_ = v___y_5334_;
v___y_5317_ = v___y_5335_;
v___y_5318_ = v___y_5336_;
v___y_5319_ = v___y_5338_;
goto v___jp_5314_;
}
else
{
lean_object* v___x_5339_; uint8_t v___x_5340_; 
v___x_5339_ = lean_array_get_size(v___y_5337_);
lean_dec_ref(v___y_5337_);
v___x_5340_ = lean_nat_dec_eq(v___x_5339_, v___y_5333_);
if (v___x_5340_ == 0)
{
lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; 
lean_dec_ref(v___y_5336_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5332_);
lean_dec_ref(v_leanOpts_5309_);
lean_dec_ref(v_ws_5307_);
v___x_5341_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5334_);
v___x_5342_ = lean_apply_2(v___y_5334_, v___x_5341_, lean_box(0));
v___x_5343_ = lean_box(0);
v___x_5344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5344_, 0, v___x_5343_);
return v___x_5344_;
}
else
{
v___y_5315_ = v___y_5332_;
v___y_5316_ = v___y_5334_;
v___y_5317_ = v___y_5335_;
v___y_5318_ = v___y_5336_;
v___y_5319_ = v___y_5338_;
goto v___jp_5314_;
}
}
}
v___jp_5345_:
{
lean_object* v___x_5353_; uint8_t v___x_5354_; 
v___x_5353_ = lean_array_get_size(v_overrides_5311_);
v___x_5354_ = lean_nat_dec_lt(v___y_5348_, v___x_5353_);
if (v___x_5354_ == 0)
{
v___y_5332_ = v___y_5346_;
v___y_5333_ = v___y_5348_;
v___y_5334_ = v___y_5347_;
v___y_5335_ = v___y_5349_;
v___y_5336_ = v___y_5350_;
v___y_5337_ = v___y_5351_;
v___y_5338_ = v___y_5352_;
goto v___jp_5331_;
}
else
{
size_t v___x_5355_; size_t v___x_5356_; lean_object* v___x_5357_; 
v___x_5355_ = ((size_t)0ULL);
v___x_5356_ = lean_usize_of_nat(v___x_5353_);
v___x_5357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5311_, v___x_5355_, v___x_5356_, v___y_5352_);
v___y_5332_ = v___y_5346_;
v___y_5333_ = v___y_5348_;
v___y_5334_ = v___y_5347_;
v___y_5335_ = v___y_5349_;
v___y_5336_ = v___y_5350_;
v___y_5337_ = v___y_5351_;
v___y_5338_ = v___x_5357_;
goto v___jp_5331_;
}
}
v___jp_5358_:
{
lean_object* v_packages_5363_; lean_object* v___x_5364_; lean_object* v_wsIdx_5365_; lean_object* v_dir_5366_; lean_object* v_depConfigs_5367_; lean_object* v___x_5368_; 
v_packages_5363_ = lean_ctor_get(v_ws_5307_, 4);
v___x_5364_ = lean_array_fget_borrowed(v_packages_5363_, v___y_5360_);
v_wsIdx_5365_ = lean_ctor_get(v___x_5364_, 0);
v_dir_5366_ = lean_ctor_get(v___x_5364_, 4);
v_depConfigs_5367_ = lean_ctor_get(v___x_5364_, 12);
v___x_5368_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5362_, v_depConfigs_5367_, v___y_5359_);
if (lean_obj_tag(v___x_5368_) == 0)
{
lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; 
lean_dec_ref_known(v___x_5368_, 1);
v___x_5369_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5366_);
v___x_5370_ = l_Lake_joinRelative(v_dir_5366_, v___x_5369_);
v___x_5371_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5372_ = l_Lake_joinRelative(v___x_5370_, v___x_5371_);
v___x_5373_ = l_Lake_Manifest_tryLoadEntries(v___x_5372_);
if (lean_obj_tag(v___x_5373_) == 0)
{
lean_object* v_a_5374_; lean_object* v___x_5375_; uint8_t v___x_5376_; 
v_a_5374_ = lean_ctor_get(v___x_5373_, 0);
lean_inc(v_a_5374_);
lean_dec_ref_known(v___x_5373_, 1);
v___x_5375_ = lean_array_get_size(v_a_5374_);
v___x_5376_ = lean_nat_dec_lt(v___y_5360_, v___x_5375_);
if (v___x_5376_ == 0)
{
lean_dec(v_a_5374_);
lean_inc_ref(v_depConfigs_5367_);
lean_inc(v_wsIdx_5365_);
lean_inc_ref(v_packages_5363_);
v___y_5346_ = v_packages_5363_;
v___y_5347_ = v___y_5359_;
v___y_5348_ = v___y_5360_;
v___y_5349_ = v_wsIdx_5365_;
v___y_5350_ = v___y_5361_;
v___y_5351_ = v_depConfigs_5367_;
v___y_5352_ = v___y_5362_;
goto v___jp_5345_;
}
else
{
size_t v___x_5377_; size_t v___x_5378_; lean_object* v___x_5379_; 
v___x_5377_ = ((size_t)0ULL);
v___x_5378_ = lean_usize_of_nat(v___x_5375_);
v___x_5379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5374_, v___x_5377_, v___x_5378_, v___y_5362_);
lean_dec(v_a_5374_);
lean_inc_ref(v_depConfigs_5367_);
lean_inc(v_wsIdx_5365_);
lean_inc_ref(v_packages_5363_);
v___y_5346_ = v_packages_5363_;
v___y_5347_ = v___y_5359_;
v___y_5348_ = v___y_5360_;
v___y_5349_ = v_wsIdx_5365_;
v___y_5350_ = v___y_5361_;
v___y_5351_ = v_depConfigs_5367_;
v___y_5352_ = v___x_5379_;
goto v___jp_5345_;
}
}
else
{
lean_object* v_a_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5392_; 
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
lean_dec_ref(v_leanOpts_5309_);
lean_dec_ref(v_ws_5307_);
v_a_5380_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5382_ = v___x_5373_;
v_isShared_5383_ = v_isSharedCheck_5392_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_a_5380_);
lean_dec(v___x_5373_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5392_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v___x_5384_; uint8_t v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5390_; 
v___x_5384_ = lean_io_error_to_string(v_a_5380_);
v___x_5385_ = 3;
v___x_5386_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5386_, 0, v___x_5384_);
lean_ctor_set_uint8(v___x_5386_, sizeof(void*)*1, v___x_5385_);
lean_inc_ref(v___y_5359_);
v___x_5387_ = lean_apply_2(v___y_5359_, v___x_5386_, lean_box(0));
v___x_5388_ = lean_box(0);
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 0, v___x_5388_);
v___x_5390_ = v___x_5382_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v___x_5388_);
v___x_5390_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
return v___x_5390_;
}
}
}
}
else
{
lean_object* v_a_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5400_; 
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
lean_dec_ref(v_leanOpts_5309_);
lean_dec_ref(v_ws_5307_);
v_a_5393_ = lean_ctor_get(v___x_5368_, 0);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___x_5368_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5395_ = v___x_5368_;
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_a_5393_);
lean_dec(v___x_5368_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v___x_5398_; 
if (v_isShared_5396_ == 0)
{
v___x_5398_ = v___x_5395_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
}
v___jp_5403_:
{
lean_object* v_pkgEntries_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; uint8_t v___x_5409_; 
v_pkgEntries_5406_ = lean_box(1);
v___x_5407_ = lean_unsigned_to_nat(0u);
v___x_5408_ = lean_array_get_size(v_packages_5402_);
v___x_5409_ = lean_nat_dec_lt(v___x_5407_, v___x_5408_);
if (v___x_5409_ == 0)
{
lean_dec_ref(v_packages_5402_);
v___y_5359_ = v___y_5404_;
v___y_5360_ = v___x_5407_;
v___y_5361_ = v___y_5405_;
v___y_5362_ = v_pkgEntries_5406_;
goto v___jp_5358_;
}
else
{
size_t v___x_5410_; size_t v___x_5411_; lean_object* v___x_5412_; 
v___x_5410_ = ((size_t)0ULL);
v___x_5411_ = lean_usize_of_nat(v___x_5408_);
v___x_5412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5402_, v___x_5410_, v___x_5411_, v_pkgEntries_5406_);
lean_dec_ref(v_packages_5402_);
v___y_5359_ = v___y_5404_;
v___y_5360_ = v___x_5407_;
v___y_5361_ = v___y_5405_;
v___y_5362_ = v___x_5412_;
goto v___jp_5358_;
}
}
v___jp_5413_:
{
if (lean_obj_tag(v_packagesDir_x3f_5401_) == 0)
{
lean_object* v_packages_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v_config_5418_; lean_object* v_toWorkspaceConfig_5419_; lean_object* v___x_5420_; 
v_packages_5415_ = lean_ctor_get(v_ws_5307_, 4);
v___x_5416_ = lean_unsigned_to_nat(0u);
v___x_5417_ = lean_array_fget_borrowed(v_packages_5415_, v___x_5416_);
v_config_5418_ = lean_ctor_get(v___x_5417_, 6);
v_toWorkspaceConfig_5419_ = lean_ctor_get(v_config_5418_, 0);
lean_inc_ref(v_toWorkspaceConfig_5419_);
v___x_5420_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5419_);
v___y_5404_ = v___y_5414_;
v___y_5405_ = v___x_5420_;
goto v___jp_5403_;
}
else
{
lean_object* v_val_5421_; 
v_val_5421_ = lean_ctor_get(v_packagesDir_x3f_5401_, 0);
lean_inc(v_val_5421_);
lean_dec_ref_known(v_packagesDir_x3f_5401_, 1);
v___y_5404_ = v___y_5414_;
v___y_5405_ = v_val_5421_;
goto v___jp_5403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5435_, lean_object* v_manifest_5436_, lean_object* v_leanOpts_5437_, lean_object* v_reconfigure_5438_, lean_object* v_overrides_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_){
_start:
{
uint8_t v_reconfigure_boxed_5442_; lean_object* v_res_5443_; 
v_reconfigure_boxed_5442_ = lean_unbox(v_reconfigure_5438_);
v_res_5443_ = l_Lake_Workspace_materializeDeps(v_ws_5435_, v_manifest_5436_, v_leanOpts_5437_, v_reconfigure_boxed_5442_, v_overrides_5439_, v_a_5440_);
lean_dec_ref(v_a_5440_);
lean_dec_ref(v_overrides_5439_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v_leanOpts_5446_, uint8_t v_reconfigure_5447_, lean_object* v_ws_5448_, lean_object* v_i_5449_, lean_object* v_i__lt_5450_, lean_object* v_next_5451_, lean_object* v_lt__next_5452_, lean_object* v___y_5453_){
_start:
{
lean_object* v___x_5455_; 
v___x_5455_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5444_, v___y_5445_, v_leanOpts_5446_, v_reconfigure_5447_, v_ws_5448_, v_i_5449_, v_next_5451_, v___y_5453_);
return v___x_5455_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v_leanOpts_5458_, lean_object* v_reconfigure_5459_, lean_object* v_ws_5460_, lean_object* v_i_5461_, lean_object* v_i__lt_5462_, lean_object* v_next_5463_, lean_object* v_lt__next_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
uint8_t v_reconfigure_boxed_5467_; lean_object* v_res_5468_; 
v_reconfigure_boxed_5467_ = lean_unbox(v_reconfigure_5459_);
v_res_5468_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5456_, v___y_5457_, v_leanOpts_5458_, v_reconfigure_boxed_5467_, v_ws_5460_, v_i_5461_, v_i__lt_5462_, v_next_5463_, v_lt__next_5464_, v___y_5465_);
lean_dec_ref(v___y_5465_);
lean_dec(v___y_5456_);
return v_res_5468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(lean_object* v_start_5469_, lean_object* v_pkg_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v_leanOpts_5473_, uint8_t v_reconfigure_5474_, lean_object* v_as_5475_, size_t v_i_5476_, size_t v_stop_5477_, lean_object* v_b_5478_, lean_object* v___y_5479_){
_start:
{
lean_object* v___x_5481_; 
v___x_5481_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5470_, v___y_5471_, v___y_5472_, v_leanOpts_5473_, v_reconfigure_5474_, v_as_5475_, v_i_5476_, v_stop_5477_, v_b_5478_, v___y_5479_);
return v___x_5481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_start_5482_, lean_object* v_pkg_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v_leanOpts_5486_, lean_object* v_reconfigure_5487_, lean_object* v_as_5488_, lean_object* v_i_5489_, lean_object* v_stop_5490_, lean_object* v_b_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_){
_start:
{
uint8_t v_reconfigure_boxed_5494_; size_t v_i_boxed_5495_; size_t v_stop_boxed_5496_; lean_object* v_res_5497_; 
v_reconfigure_boxed_5494_ = lean_unbox(v_reconfigure_5487_);
v_i_boxed_5495_ = lean_unbox_usize(v_i_5489_);
lean_dec(v_i_5489_);
v_stop_boxed_5496_ = lean_unbox_usize(v_stop_5490_);
lean_dec(v_stop_5490_);
v_res_5497_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(v_start_5482_, v_pkg_5483_, v___y_5484_, v___y_5485_, v_leanOpts_5486_, v_reconfigure_boxed_5494_, v_as_5488_, v_i_boxed_5495_, v_stop_boxed_5496_, v_b_5491_, v___y_5492_);
lean_dec_ref(v___y_5492_);
lean_dec_ref(v_as_5488_);
lean_dec(v___y_5484_);
lean_dec(v_start_5482_);
return v_res_5497_;
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

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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Env_noToolchainVars(lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_io_exit(uint8_t);
extern lean_object* l_Lake_toolchainFileName;
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
static uint8_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = ": no previous manifest, creating one from scratch"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = ": ignoring previous manifest because it failed to load: "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "restarting Lake via Elan"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "run"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--install"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5_value;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "no Elan detected; you will need to manually restart Lake"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9_value;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "cannot auto-restart; you will need to manually restart Lake"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "updating toolchain to '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "toolchain not updated; multiple toolchain candidates:\n  "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "toolchain not updated; already up-to-date"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "toolchain not updated; no toolchain information found"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "toolchain not updated; multiple toolchain candidates:"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19_value;
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20_value;
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object*, lean_object*);
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
lean_inc(v_size_102_);
v_k_103_ = lean_ctor_get(v_impl_99_, 1);
lean_inc(v_k_103_);
v_v_104_ = lean_ctor_get(v_impl_99_, 2);
lean_inc(v_v_104_);
v_l_105_ = lean_ctor_get(v_impl_99_, 3);
lean_inc(v_l_105_);
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
lean_dec(v_l_105_);
lean_dec(v_v_104_);
lean_dec(v_k_103_);
v___x_110_ = lean_nat_add(v___x_100_, v_size_102_);
lean_dec(v_size_102_);
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
lean_inc(v_l_186_);
if (lean_obj_tag(v_l_186_) == 0)
{
lean_object* v_r_187_; lean_object* v_k_188_; lean_object* v_v_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_200_; 
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
lean_inc(v_size_242_);
v_k_243_ = lean_ctor_get(v_impl_239_, 1);
lean_inc(v_k_243_);
v_v_244_ = lean_ctor_get(v_impl_239_, 2);
lean_inc(v_v_244_);
v_l_245_ = lean_ctor_get(v_impl_239_, 3);
lean_inc(v_l_245_);
v_r_246_ = lean_ctor_get(v_impl_239_, 4);
lean_inc(v_r_246_);
v___x_247_ = lean_unsigned_to_nat(3u);
v___x_248_ = lean_nat_mul(v___x_247_, v_size_241_);
v___x_249_ = lean_nat_dec_lt(v___x_248_, v_size_242_);
lean_dec(v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec(v_r_246_);
lean_dec(v_l_245_);
lean_dec(v_v_244_);
lean_dec(v_k_243_);
v___x_250_ = lean_nat_add(v___x_240_, v_size_241_);
v___x_251_ = lean_nat_add(v___x_250_, v_size_242_);
lean_dec(v_size_242_);
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
lean_object* v_lakeEnv_659_; lean_object* v_lakeConfig_660_; lean_object* v_lakeCache_661_; lean_object* v_lakeArgs_x3f_662_; lean_object* v_packages_663_; lean_object* v_facetConfigs_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_693_; 
v_lakeEnv_659_ = lean_ctor_get(v_self_658_, 0);
v_lakeConfig_660_ = lean_ctor_get(v_self_658_, 1);
v_lakeCache_661_ = lean_ctor_get(v_self_658_, 2);
v_lakeArgs_x3f_662_ = lean_ctor_get(v_self_658_, 3);
v_packages_663_ = lean_ctor_get(v_self_658_, 4);
v_facetConfigs_664_ = lean_ctor_get(v_self_658_, 6);
v_isSharedCheck_693_ = !lean_is_exclusive(v_self_658_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v_self_658_, 5);
lean_dec(v_unused_694_);
v___x_666_ = v_self_658_;
v_isShared_667_ = v_isSharedCheck_693_;
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
v_isShared_667_ = v_isSharedCheck_693_;
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
uint8_t v___x_677_; 
v___x_677_ = lean_nat_dec_le(v___x_672_, v___x_672_);
if (v___x_677_ == 0)
{
if (v___x_673_ == 0)
{
lean_object* v___x_679_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 5, v___x_670_);
lean_ctor_set(v___x_666_, 4, v_val_669_);
v___x_679_ = v___x_666_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_lakeEnv_659_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_lakeConfig_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_lakeCache_661_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_lakeArgs_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_val_669_);
lean_ctor_set(v_reuseFailAlloc_680_, 5, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_680_, 6, v_facetConfigs_664_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
else
{
size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_681_ = ((size_t)0ULL);
v___x_682_ = lean_usize_of_nat(v___x_672_);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_val_669_, v___x_681_, v___x_682_, v___x_670_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 5, v___x_683_);
lean_ctor_set(v___x_666_, 4, v_val_669_);
v___x_685_ = v___x_666_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_lakeEnv_659_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_lakeConfig_660_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_lakeCache_661_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_lakeArgs_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_val_669_);
lean_ctor_set(v_reuseFailAlloc_686_, 5, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_686_, 6, v_facetConfigs_664_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
else
{
size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_687_ = ((size_t)0ULL);
v___x_688_ = lean_usize_of_nat(v___x_672_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_val_669_, v___x_687_, v___x_688_, v___x_670_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 5, v___x_689_);
lean_ctor_set(v___x_666_, 4, v_val_669_);
v___x_691_ = v___x_666_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_lakeEnv_659_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_lakeConfig_660_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_lakeCache_661_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_lakeArgs_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_val_669_);
lean_ctor_set(v_reuseFailAlloc_692_, 5, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_692_, 6, v_facetConfigs_664_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(lean_object* v___x_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(v_x_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___boxed(lean_object* v___x_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(v___x_699_, v_x_700_, v_x_701_);
lean_dec(v___x_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(lean_object* v_ws_703_, lean_object* v_size_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_mk_empty_array_with_capacity(v_size_704_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_ws_703_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init___boxed(lean_object* v_ws_707_, lean_object* v_size_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(v_ws_707_, v_size_708_);
lean_dec(v_size_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___redArg(lean_object* v_s_710_, lean_object* v_wsIdx_711_){
_start:
{
lean_object* v_ws_712_; lean_object* v_depIdxs_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_721_; 
v_ws_712_ = lean_ctor_get(v_s_710_, 0);
v_depIdxs_713_ = lean_ctor_get(v_s_710_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_s_710_);
if (v_isSharedCheck_721_ == 0)
{
v___x_715_ = v_s_710_;
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_depIdxs_713_);
lean_inc(v_ws_712_);
lean_dec(v_s_710_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_array_push(v_depIdxs_713_, v_wsIdx_711_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_ws_712_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(lean_object* v_n_722_, lean_object* v_s_723_, lean_object* v_wsIdx_724_){
_start:
{
lean_object* v_ws_725_; lean_object* v_depIdxs_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
v_ws_725_ = lean_ctor_get(v_s_723_, 0);
v_depIdxs_726_ = lean_ctor_get(v_s_723_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_s_723_);
if (v_isSharedCheck_734_ == 0)
{
v___x_728_ = v_s_723_;
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_depIdxs_726_);
lean_inc(v_ws_725_);
lean_dec(v_s_723_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_array_push(v_depIdxs_726_, v_wsIdx_724_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_ws_725_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___boxed(lean_object* v_n_735_, lean_object* v_s_736_, lean_object* v_wsIdx_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(v_n_735_, v_s_736_, v_wsIdx_737_);
lean_dec(v_n_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(lean_object* v_s_739_, lean_object* v_dep_740_, lean_object* v_lakeOpts_741_, lean_object* v_leanOpts_742_, uint8_t v_reconfigure_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_ws_746_; lean_object* v_depIdxs_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_776_; 
v_ws_746_ = lean_ctor_get(v_s_739_, 0);
v_depIdxs_747_ = lean_ctor_get(v_s_739_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_s_739_);
if (v_isSharedCheck_776_ == 0)
{
v___x_749_ = v_s_739_;
v_isShared_750_ = v_isSharedCheck_776_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_depIdxs_747_);
lean_inc(v_ws_746_);
lean_dec(v_s_739_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_776_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; 
lean_inc_ref(v_ws_746_);
v___x_751_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_746_, v_dep_740_, v_lakeOpts_741_, v_leanOpts_742_, v_reconfigure_743_, v_a_744_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_766_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_a_753_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_766_ == 0)
{
v___x_755_ = v___x_751_;
v_isShared_756_ = v_isSharedCheck_766_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_766_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_packages_757_; lean_object* v_wsIdx_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v_packages_757_ = lean_ctor_get(v_ws_746_, 4);
lean_inc_ref(v_packages_757_);
lean_dec_ref(v_ws_746_);
v_wsIdx_758_ = lean_array_get_size(v_packages_757_);
lean_dec_ref(v_packages_757_);
v___x_759_ = lean_array_push(v_depIdxs_747_, v_wsIdx_758_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_759_);
lean_ctor_set(v___x_749_, 0, v_a_752_);
v___x_761_ = v___x_749_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_752_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_763_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_761_);
v___x_763_ = v___x_755_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_a_753_);
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
else
{
lean_object* v_a_767_; lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_del_object(v___x_749_);
lean_dec_ref(v_depIdxs_747_);
lean_dec_ref(v_ws_746_);
v_a_767_ = lean_ctor_get(v___x_751_, 0);
v_a_768_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_751_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_inc(v_a_767_);
lean_dec(v___x_751_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_767_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg___boxed(lean_object* v_s_777_, lean_object* v_dep_778_, lean_object* v_lakeOpts_779_, lean_object* v_leanOpts_780_, lean_object* v_reconfigure_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
uint8_t v_reconfigure_boxed_784_; lean_object* v_res_785_; 
v_reconfigure_boxed_784_ = lean_unbox(v_reconfigure_781_);
v_res_785_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(v_s_777_, v_dep_778_, v_lakeOpts_779_, v_leanOpts_780_, v_reconfigure_boxed_784_, v_a_782_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(lean_object* v_n_786_, lean_object* v_s_787_, lean_object* v_dep_788_, lean_object* v_lakeOpts_789_, lean_object* v_leanOpts_790_, uint8_t v_reconfigure_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_ws_794_; lean_object* v_depIdxs_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_824_; 
v_ws_794_ = lean_ctor_get(v_s_787_, 0);
v_depIdxs_795_ = lean_ctor_get(v_s_787_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_s_787_);
if (v_isSharedCheck_824_ == 0)
{
v___x_797_ = v_s_787_;
v_isShared_798_ = v_isSharedCheck_824_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_depIdxs_795_);
lean_inc(v_ws_794_);
lean_dec(v_s_787_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_824_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; 
lean_inc_ref(v_ws_794_);
v___x_799_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_794_, v_dep_788_, v_lakeOpts_789_, v_leanOpts_790_, v_reconfigure_791_, v_a_792_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_814_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_a_801_ = lean_ctor_get(v___x_799_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_814_ == 0)
{
v___x_803_ = v___x_799_;
v_isShared_804_ = v_isSharedCheck_814_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_814_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_packages_805_; lean_object* v_wsIdx_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v_packages_805_ = lean_ctor_get(v_ws_794_, 4);
lean_inc_ref(v_packages_805_);
lean_dec_ref(v_ws_794_);
v_wsIdx_806_ = lean_array_get_size(v_packages_805_);
lean_dec_ref(v_packages_805_);
v___x_807_ = lean_array_push(v_depIdxs_795_, v_wsIdx_806_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_807_);
lean_ctor_set(v___x_797_, 0, v_a_800_);
v___x_809_ = v___x_797_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_800_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_809_);
v___x_811_ = v___x_803_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_a_801_);
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
else
{
lean_object* v_a_815_; lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_del_object(v___x_797_);
lean_dec_ref(v_depIdxs_795_);
lean_dec_ref(v_ws_794_);
v_a_815_ = lean_ctor_get(v___x_799_, 0);
v_a_816_ = lean_ctor_get(v___x_799_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_799_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_inc(v_a_815_);
lean_dec(v___x_799_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_815_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed(lean_object* v_n_825_, lean_object* v_s_826_, lean_object* v_dep_827_, lean_object* v_lakeOpts_828_, lean_object* v_leanOpts_829_, lean_object* v_reconfigure_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
uint8_t v_reconfigure_boxed_833_; lean_object* v_res_834_; 
v_reconfigure_boxed_833_ = lean_unbox(v_reconfigure_830_);
v_res_834_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(v_n_825_, v_s_826_, v_dep_827_, v_lakeOpts_828_, v_leanOpts_829_, v_reconfigure_boxed_833_, v_a_831_);
lean_dec(v_n_825_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___redArg(lean_object* v_inst_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = lean_apply_2(v_inst_835_, lean_box(0), lean_box(0));
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(lean_object* v_m_837_, lean_object* v_00_u03b1_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_as_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_apply_2(v_inst_839_, lean_box(0), lean_box(0));
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___boxed(lean_object* v_m_843_, lean_object* v_00_u03b1_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_as_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(v_m_843_, v_00_u03b1_844_, v_inst_845_, v_inst_846_, v_as_847_);
lean_dec_ref(v_as_847_);
lean_dec(v_inst_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object* v_resolve_849_, lean_object* v_pkg_850_, lean_object* v_dep_851_, lean_object* v_ws_852_, lean_object* v_toBind_853_, lean_object* v___f_854_, lean_object* v_____r_855_){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_apply_3(v_resolve_849_, v_pkg_850_, v_dep_851_, v_ws_852_);
v___x_857_ = lean_apply_4(v_toBind_853_, lean_box(0), lean_box(0), v___x_856_, v___f_854_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object* v_start_858_, lean_object* v_s_859_, lean_object* v_opts_860_, lean_object* v_leanOpts_861_, uint8_t v_reconfigure_862_, lean_object* v_inst_863_, lean_object* v_matDep_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_865_ = lean_box(v_reconfigure_862_);
v___x_866_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed), 8, 6);
lean_closure_set(v___x_866_, 0, v_start_858_);
lean_closure_set(v___x_866_, 1, v_s_859_);
lean_closure_set(v___x_866_, 2, v_matDep_864_);
lean_closure_set(v___x_866_, 3, v_opts_860_);
lean_closure_set(v___x_866_, 4, v_leanOpts_861_);
lean_closure_set(v___x_866_, 5, v___x_865_);
v___x_867_ = lean_apply_2(v_inst_863_, lean_box(0), v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object* v_start_868_, lean_object* v_s_869_, lean_object* v_opts_870_, lean_object* v_leanOpts_871_, lean_object* v_reconfigure_872_, lean_object* v_inst_873_, lean_object* v_matDep_874_){
_start:
{
uint8_t v_reconfigure_boxed_875_; lean_object* v_res_876_; 
v_reconfigure_boxed_875_ = lean_unbox(v_reconfigure_872_);
v_res_876_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(v_start_868_, v_s_869_, v_opts_870_, v_leanOpts_871_, v_reconfigure_boxed_875_, v_inst_873_, v_matDep_874_);
return v_res_876_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object* v_dep_877_, lean_object* v_x_878_){
_start:
{
lean_object* v_baseName_879_; lean_object* v_name_880_; uint8_t v___x_881_; 
v_baseName_879_ = lean_ctor_get(v_x_878_, 1);
v_name_880_ = lean_ctor_get(v_dep_877_, 0);
v___x_881_ = lean_name_eq(v_baseName_879_, v_name_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed(lean_object* v_dep_882_, lean_object* v_x_883_){
_start:
{
uint8_t v_res_884_; lean_object* v_r_885_; 
v_res_884_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(v_dep_882_, v_x_883_);
lean_dec_ref(v_x_883_);
lean_dec_ref(v_dep_882_);
v_r_885_ = lean_box(v_res_884_);
return v_r_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object* v___f_886_, lean_object* v_____r_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_apply_1(v___f_886_, v_____r_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object* v_toPure_890_, lean_object* v_start_891_, lean_object* v_leanOpts_892_, uint8_t v_reconfigure_893_, lean_object* v_inst_894_, lean_object* v_resolve_895_, lean_object* v_pkg_896_, lean_object* v_toBind_897_, lean_object* v_baseName_898_, lean_object* v_inst_899_, lean_object* v_dep_900_, lean_object* v_s_901_){
_start:
{
lean_object* v_ws_902_; lean_object* v_depIdxs_903_; lean_object* v_packages_904_; lean_object* v___f_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_ws_902_ = lean_ctor_get(v_s_901_, 0);
lean_inc_ref(v_ws_902_);
v_depIdxs_903_ = lean_ctor_get(v_s_901_, 1);
v_packages_904_ = lean_ctor_get(v_ws_902_, 4);
lean_inc_ref(v_dep_900_);
v___f_905_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_905_, 0, v_dep_900_);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_905_, v_packages_904_, v___x_906_);
if (lean_obj_tag(v___x_907_) == 1)
{
lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_917_; 
lean_inc_ref(v_depIdxs_903_);
lean_dec_ref(v_dep_900_);
lean_dec(v_inst_899_);
lean_dec(v_baseName_898_);
lean_dec(v_toBind_897_);
lean_dec_ref(v_pkg_896_);
lean_dec(v_resolve_895_);
lean_dec(v_inst_894_);
lean_dec_ref(v_leanOpts_892_);
lean_dec(v_start_891_);
v_isSharedCheck_917_ = !lean_is_exclusive(v_s_901_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; lean_object* v_unused_919_; 
v_unused_918_ = lean_ctor_get(v_s_901_, 1);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_s_901_, 0);
lean_dec(v_unused_919_);
v___x_909_ = v_s_901_;
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
else
{
lean_dec(v_s_901_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_val_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v_val_911_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_val_911_);
lean_dec_ref_known(v___x_907_, 1);
v___x_912_ = lean_array_push(v_depIdxs_903_, v_val_911_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___x_912_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_ws_902_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_912_);
v___x_914_ = v_reuseFailAlloc_916_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; 
v___x_915_ = lean_apply_2(v_toPure_890_, lean_box(0), v___x_914_);
return v___x_915_;
}
}
}
else
{
lean_object* v_name_920_; lean_object* v_opts_921_; lean_object* v___x_922_; lean_object* v___f_923_; lean_object* v___f_924_; uint8_t v___x_925_; 
lean_dec(v___x_907_);
lean_dec(v_toPure_890_);
v_name_920_ = lean_ctor_get(v_dep_900_, 0);
v_opts_921_ = lean_ctor_get(v_dep_900_, 4);
v___x_922_ = lean_box(v_reconfigure_893_);
lean_inc(v_opts_921_);
v___f_923_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_923_, 0, v_start_891_);
lean_closure_set(v___f_923_, 1, v_s_901_);
lean_closure_set(v___f_923_, 2, v_opts_921_);
lean_closure_set(v___f_923_, 3, v_leanOpts_892_);
lean_closure_set(v___f_923_, 4, v___x_922_);
lean_closure_set(v___f_923_, 5, v_inst_894_);
lean_inc_ref(v___f_923_);
lean_inc(v_toBind_897_);
lean_inc_ref(v_ws_902_);
lean_inc_ref(v_dep_900_);
lean_inc_ref(v_pkg_896_);
lean_inc(v_resolve_895_);
v___f_924_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4), 7, 6);
lean_closure_set(v___f_924_, 0, v_resolve_895_);
lean_closure_set(v___f_924_, 1, v_pkg_896_);
lean_closure_set(v___f_924_, 2, v_dep_900_);
lean_closure_set(v___f_924_, 3, v_ws_902_);
lean_closure_set(v___f_924_, 4, v_toBind_897_);
lean_closure_set(v___f_924_, 5, v___f_923_);
v___x_925_ = lean_name_eq(v_baseName_898_, v_name_920_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec_ref(v___f_924_);
lean_dec(v_inst_899_);
lean_dec(v_baseName_898_);
v___x_926_ = lean_box(0);
v___x_927_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(v_resolve_895_, v_pkg_896_, v_dep_900_, v_ws_902_, v_toBind_897_, v___f_923_, v___x_926_);
return v___x_927_;
}
else
{
lean_object* v___f_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec_ref(v___f_923_);
lean_dec_ref(v_ws_902_);
lean_dec_ref(v_dep_900_);
lean_dec_ref(v_pkg_896_);
lean_dec(v_resolve_895_);
v___f_928_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5), 2, 1);
lean_closure_set(v___f_928_, 0, v___f_924_);
v___x_929_ = 0;
v___x_930_ = l_Lean_Name_toString(v_baseName_898_, v___x_929_);
v___x_931_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
v___x_933_ = lean_apply_2(v_inst_899_, lean_box(0), v___x_932_);
v___x_934_ = lean_apply_4(v_toBind_897_, lean_box(0), lean_box(0), v___x_933_, v___f_928_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object* v_toPure_935_, lean_object* v_start_936_, lean_object* v_leanOpts_937_, lean_object* v_reconfigure_938_, lean_object* v_inst_939_, lean_object* v_resolve_940_, lean_object* v_pkg_941_, lean_object* v_toBind_942_, lean_object* v_baseName_943_, lean_object* v_inst_944_, lean_object* v_dep_945_, lean_object* v_s_946_){
_start:
{
uint8_t v_reconfigure_boxed_947_; lean_object* v_res_948_; 
v_reconfigure_boxed_947_ = lean_unbox(v_reconfigure_938_);
v_res_948_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(v_toPure_935_, v_start_936_, v_leanOpts_937_, v_reconfigure_boxed_947_, v_inst_939_, v_resolve_940_, v_pkg_941_, v_toBind_942_, v_baseName_943_, v_inst_944_, v_dep_945_, v_s_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0___boxed(lean_object* v_next_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_resolve_953_, lean_object* v_leanOpts_954_, lean_object* v_reconfigure_955_, lean_object* v_ws_956_, lean_object* v_____x_957_){
_start:
{
uint8_t v_reconfigure_boxed_958_; lean_object* v_res_959_; 
v_reconfigure_boxed_958_ = lean_unbox(v_reconfigure_955_);
v_res_959_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(v_next_949_, v_inst_950_, v_inst_951_, v_inst_952_, v_resolve_953_, v_leanOpts_954_, v_reconfigure_boxed_958_, v_ws_956_, v_____x_957_);
lean_dec(v_next_949_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object* v_pkg_960_, lean_object* v_next_961_, lean_object* v_toPure_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_resolve_966_, lean_object* v_leanOpts_967_, uint8_t v_reconfigure_968_, lean_object* v_toBind_969_, lean_object* v_____x_970_){
_start:
{
lean_object* v_ws_971_; lean_object* v_depIdxs_972_; lean_object* v_ws_973_; lean_object* v_packages_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v_ws_971_ = lean_ctor_get(v_____x_970_, 0);
lean_inc_ref(v_ws_971_);
v_depIdxs_972_ = lean_ctor_get(v_____x_970_, 1);
lean_inc_ref(v_depIdxs_972_);
lean_dec_ref(v_____x_970_);
v_ws_973_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_971_, v_pkg_960_, v_depIdxs_972_);
v_packages_974_ = lean_ctor_get(v_ws_973_, 4);
lean_inc_ref(v_packages_974_);
v___x_975_ = lean_array_get_size(v_packages_974_);
lean_dec_ref(v_packages_974_);
v___x_976_ = lean_nat_dec_lt(v_next_961_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_dec(v_toBind_969_);
lean_dec_ref(v_leanOpts_967_);
lean_dec(v_resolve_966_);
lean_dec(v_inst_965_);
lean_dec(v_inst_964_);
lean_dec_ref(v_inst_963_);
lean_dec(v_next_961_);
v___x_977_ = lean_apply_2(v_toPure_962_, lean_box(0), v_ws_973_);
return v___x_977_;
}
else
{
lean_object* v___x_978_; lean_object* v___f_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_978_ = lean_box(v_reconfigure_968_);
v___f_979_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_979_, 0, v_next_961_);
lean_closure_set(v___f_979_, 1, v_inst_963_);
lean_closure_set(v___f_979_, 2, v_inst_964_);
lean_closure_set(v___f_979_, 3, v_inst_965_);
lean_closure_set(v___f_979_, 4, v_resolve_966_);
lean_closure_set(v___f_979_, 5, v_leanOpts_967_);
lean_closure_set(v___f_979_, 6, v___x_978_);
lean_closure_set(v___f_979_, 7, v_ws_973_);
v___x_980_ = lean_apply_2(v_toPure_962_, lean_box(0), lean_box(0));
v___x_981_ = lean_apply_4(v_toBind_969_, lean_box(0), lean_box(0), v___x_980_, v___f_979_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed(lean_object* v_pkg_982_, lean_object* v_next_983_, lean_object* v_toPure_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_resolve_988_, lean_object* v_leanOpts_989_, lean_object* v_reconfigure_990_, lean_object* v_toBind_991_, lean_object* v_____x_992_){
_start:
{
uint8_t v_reconfigure_boxed_993_; lean_object* v_res_994_; 
v_reconfigure_boxed_993_ = lean_unbox(v_reconfigure_990_);
v_res_994_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(v_pkg_982_, v_next_983_, v_toPure_984_, v_inst_985_, v_inst_986_, v_inst_987_, v_resolve_988_, v_leanOpts_989_, v_reconfigure_boxed_993_, v_toBind_991_, v_____x_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object* v_inst_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_resolve_998_, lean_object* v_leanOpts_999_, uint8_t v_reconfigure_1000_, lean_object* v_ws_1001_, lean_object* v_i_1002_, lean_object* v_next_1003_){
_start:
{
lean_object* v_packages_1004_; lean_object* v_pkg_1005_; lean_object* v_toApplicative_1006_; lean_object* v_baseName_1007_; lean_object* v_depConfigs_1008_; lean_object* v_toBind_1009_; lean_object* v_toPure_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_s_1013_; lean_object* v___x_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_packages_1004_ = lean_ctor_get(v_ws_1001_, 4);
lean_inc_ref(v_packages_1004_);
v_pkg_1005_ = lean_array_fget(v_packages_1004_, v_i_1002_);
v_toApplicative_1006_ = lean_ctor_get(v_inst_995_, 0);
v_baseName_1007_ = lean_ctor_get(v_pkg_1005_, 1);
lean_inc(v_baseName_1007_);
v_depConfigs_1008_ = lean_ctor_get(v_pkg_1005_, 12);
lean_inc_ref(v_depConfigs_1008_);
v_toBind_1009_ = lean_ctor_get(v_inst_995_, 1);
lean_inc_n(v_toBind_1009_, 2);
v_toPure_1010_ = lean_ctor_get(v_toApplicative_1006_, 1);
v___x_1011_ = lean_array_get_size(v_depConfigs_1008_);
v___x_1012_ = lean_mk_empty_array_with_capacity(v___x_1011_);
v_s_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_1013_, 0, v_ws_1001_);
lean_ctor_set(v_s_1013_, 1, v___x_1012_);
v___x_1014_ = lean_box(v_reconfigure_1000_);
lean_inc_ref(v_leanOpts_999_);
lean_inc(v_resolve_998_);
lean_inc(v_inst_997_);
lean_inc(v_inst_996_);
lean_inc_ref(v_inst_995_);
lean_inc(v_toPure_1010_);
lean_inc(v_pkg_1005_);
v___f_1015_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_1015_, 0, v_pkg_1005_);
lean_closure_set(v___f_1015_, 1, v_next_1003_);
lean_closure_set(v___f_1015_, 2, v_toPure_1010_);
lean_closure_set(v___f_1015_, 3, v_inst_995_);
lean_closure_set(v___f_1015_, 4, v_inst_996_);
lean_closure_set(v___f_1015_, 5, v_inst_997_);
lean_closure_set(v___f_1015_, 6, v_resolve_998_);
lean_closure_set(v___f_1015_, 7, v_leanOpts_999_);
lean_closure_set(v___f_1015_, 8, v___x_1014_);
lean_closure_set(v___f_1015_, 9, v_toBind_1009_);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_nat_dec_lt(v___x_1016_, v___x_1011_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_inc(v_toPure_1010_);
lean_dec_ref(v_depConfigs_1008_);
lean_dec(v_baseName_1007_);
lean_dec(v_pkg_1005_);
lean_dec_ref(v_packages_1004_);
lean_dec_ref(v_leanOpts_999_);
lean_dec(v_resolve_998_);
lean_dec(v_inst_997_);
lean_dec(v_inst_996_);
lean_dec_ref(v_inst_995_);
v___x_1018_ = lean_apply_2(v_toPure_1010_, lean_box(0), v_s_1013_);
v___x_1019_ = lean_apply_4(v_toBind_1009_, lean_box(0), lean_box(0), v___x_1018_, v___f_1015_);
return v___x_1019_;
}
else
{
lean_object* v_start_1020_; lean_object* v___x_1021_; lean_object* v___f_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_start_1020_ = lean_array_get_size(v_packages_1004_);
lean_dec_ref(v_packages_1004_);
v___x_1021_ = lean_box(v_reconfigure_1000_);
lean_inc(v_toBind_1009_);
lean_inc(v_toPure_1010_);
v___f_1022_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed), 12, 10);
lean_closure_set(v___f_1022_, 0, v_toPure_1010_);
lean_closure_set(v___f_1022_, 1, v_start_1020_);
lean_closure_set(v___f_1022_, 2, v_leanOpts_999_);
lean_closure_set(v___f_1022_, 3, v___x_1021_);
lean_closure_set(v___f_1022_, 4, v_inst_997_);
lean_closure_set(v___f_1022_, 5, v_resolve_998_);
lean_closure_set(v___f_1022_, 6, v_pkg_1005_);
lean_closure_set(v___f_1022_, 7, v_toBind_1009_);
lean_closure_set(v___f_1022_, 8, v_baseName_1007_);
lean_closure_set(v___f_1022_, 9, v_inst_996_);
v___x_1023_ = lean_usize_of_nat(v___x_1011_);
v___x_1024_ = ((size_t)0ULL);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_995_, v___f_1022_, v_depConfigs_1008_, v___x_1023_, v___x_1024_, v_s_1013_);
v___x_1026_ = lean_apply_4(v_toBind_1009_, lean_box(0), lean_box(0), v___x_1025_, v___f_1015_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object* v_next_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_resolve_1031_, lean_object* v_leanOpts_1032_, uint8_t v_reconfigure_1033_, lean_object* v_ws_1034_, lean_object* v_____x_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = lean_unsigned_to_nat(1u);
v___x_1037_ = lean_nat_add(v_next_1027_, v___x_1036_);
v___x_1038_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1028_, v_inst_1029_, v_inst_1030_, v_resolve_1031_, v_leanOpts_1032_, v_reconfigure_1033_, v_ws_1034_, v_next_1027_, v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_resolve_1042_, lean_object* v_leanOpts_1043_, lean_object* v_reconfigure_1044_, lean_object* v_ws_1045_, lean_object* v_i_1046_, lean_object* v_next_1047_){
_start:
{
uint8_t v_reconfigure_boxed_1048_; lean_object* v_res_1049_; 
v_reconfigure_boxed_1048_ = lean_unbox(v_reconfigure_1044_);
v_res_1049_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1039_, v_inst_1040_, v_inst_1041_, v_resolve_1042_, v_leanOpts_1043_, v_reconfigure_boxed_1048_, v_ws_1045_, v_i_1046_, v_next_1047_);
lean_dec(v_i_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* v_m_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_resolve_1054_, lean_object* v_leanOpts_1055_, uint8_t v_reconfigure_1056_, lean_object* v_ws_1057_, lean_object* v_i_1058_, lean_object* v_i__lt_1059_, lean_object* v_next_1060_, lean_object* v_lt__next_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1051_, v_inst_1052_, v_inst_1053_, v_resolve_1054_, v_leanOpts_1055_, v_reconfigure_1056_, v_ws_1057_, v_i_1058_, v_next_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object* v_m_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_resolve_1067_, lean_object* v_leanOpts_1068_, lean_object* v_reconfigure_1069_, lean_object* v_ws_1070_, lean_object* v_i_1071_, lean_object* v_i__lt_1072_, lean_object* v_next_1073_, lean_object* v_lt__next_1074_){
_start:
{
uint8_t v_reconfigure_boxed_1075_; lean_object* v_res_1076_; 
v_reconfigure_boxed_1075_ = lean_unbox(v_reconfigure_1069_);
v_res_1076_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(v_m_1063_, v_inst_1064_, v_inst_1065_, v_inst_1066_, v_resolve_1067_, v_leanOpts_1068_, v_reconfigure_boxed_1075_, v_ws_1070_, v_i_1071_, v_i__lt_1072_, v_next_1073_, v_lt__next_1074_);
lean_dec(v_i_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___redArg(lean_object* v_x_1077_, lean_object* v_h__1_1078_, lean_object* v_h__2_1079_){
_start:
{
if (lean_obj_tag(v_x_1077_) == 1)
{
lean_object* v_val_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__2_1079_);
v_val_1080_ = lean_ctor_get(v_x_1077_, 0);
lean_inc(v_val_1080_);
lean_dec_ref_known(v_x_1077_, 1);
v___x_1081_ = lean_apply_1(v_h__1_1078_, v_val_1080_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; 
lean_dec(v_h__1_1078_);
v___x_1082_ = lean_apply_2(v_h__2_1079_, v_x_1077_, lean_box(0));
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(lean_object* v_ws_1083_, lean_object* v_s_1084_, lean_object* v_motive_1085_, lean_object* v_x_1086_, lean_object* v_h__1_1087_, lean_object* v_h__2_1088_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 1)
{
lean_object* v_val_1089_; lean_object* v___x_1090_; 
lean_dec(v_h__2_1088_);
v_val_1089_ = lean_ctor_get(v_x_1086_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v_x_1086_, 1);
v___x_1090_ = lean_apply_1(v_h__1_1087_, v_val_1089_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; 
lean_dec(v_h__1_1087_);
v___x_1091_ = lean_apply_2(v_h__2_1088_, v_x_1086_, lean_box(0));
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___boxed(lean_object* v_ws_1092_, lean_object* v_s_1093_, lean_object* v_motive_1094_, lean_object* v_x_1095_, lean_object* v_h__1_1096_, lean_object* v_h__2_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(v_ws_1092_, v_s_1093_, v_motive_1094_, v_x_1095_, v_h__1_1096_, v_h__2_1097_);
lean_dec_ref(v_s_1093_);
lean_dec_ref(v_ws_1092_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___redArg(lean_object* v_x_1099_, lean_object* v_h__1_1100_){
_start:
{
lean_object* v_ws_1101_; lean_object* v_depIdxs_1102_; lean_object* v___x_1103_; 
v_ws_1101_ = lean_ctor_get(v_x_1099_, 0);
lean_inc_ref(v_ws_1101_);
v_depIdxs_1102_ = lean_ctor_get(v_x_1099_, 1);
lean_inc_ref(v_depIdxs_1102_);
lean_dec_ref(v_x_1099_);
v___x_1103_ = lean_apply_4(v_h__1_1100_, v_ws_1101_, v_depIdxs_1102_, lean_box(0), lean_box(0));
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(lean_object* v_ws_1104_, lean_object* v_motive_1105_, lean_object* v_x_1106_, lean_object* v_h__1_1107_){
_start:
{
lean_object* v_ws_1108_; lean_object* v_depIdxs_1109_; lean_object* v___x_1110_; 
v_ws_1108_ = lean_ctor_get(v_x_1106_, 0);
lean_inc_ref(v_ws_1108_);
v_depIdxs_1109_ = lean_ctor_get(v_x_1106_, 1);
lean_inc_ref(v_depIdxs_1109_);
lean_dec_ref(v_x_1106_);
v___x_1110_ = lean_apply_4(v_h__1_1107_, v_ws_1108_, v_depIdxs_1109_, lean_box(0), lean_box(0));
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___boxed(lean_object* v_ws_1111_, lean_object* v_motive_1112_, lean_object* v_x_1113_, lean_object* v_h__1_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(v_ws_1111_, v_motive_1112_, v_x_1113_, v_h__1_1114_);
lean_dec_ref(v_ws_1111_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___redArg(lean_object* v_h__1_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_apply_1(v_h__1_1116_, lean_box(0));
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(lean_object* v_ws_1118_, lean_object* v_motive_1119_, lean_object* v_x_1120_, lean_object* v_h__1_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_apply_1(v_h__1_1121_, lean_box(0));
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___boxed(lean_object* v_ws_1123_, lean_object* v_motive_1124_, lean_object* v_x_1125_, lean_object* v_h__1_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(v_ws_1123_, v_motive_1124_, v_x_1125_, v_h__1_1126_);
lean_dec_ref(v_ws_1123_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_ws_1132_, lean_object* v_resolve_1133_, lean_object* v_root_1134_, lean_object* v_next_1135_, lean_object* v_leanOpts_1136_, uint8_t v_reconfigure_1137_){
_start:
{
lean_object* v_toApplicative_1138_; lean_object* v_toFunctor_1139_; lean_object* v_map_1140_; lean_object* v___f_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_toApplicative_1138_ = lean_ctor_get(v_inst_1129_, 0);
v_toFunctor_1139_ = lean_ctor_get(v_toApplicative_1138_, 0);
v_map_1140_ = lean_ctor_get(v_toFunctor_1139_, 0);
lean_inc(v_map_1140_);
v___f_1141_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0));
v___x_1142_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1129_, v_inst_1130_, v_inst_1131_, v_resolve_1133_, v_leanOpts_1136_, v_reconfigure_1137_, v_ws_1132_, v_root_1134_, v_next_1135_);
v___x_1143_ = lean_apply_4(v_map_1140_, lean_box(0), lean_box(0), v___f_1141_, v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_ws_1147_, lean_object* v_resolve_1148_, lean_object* v_root_1149_, lean_object* v_next_1150_, lean_object* v_leanOpts_1151_, lean_object* v_reconfigure_1152_){
_start:
{
uint8_t v_reconfigure_boxed_1153_; lean_object* v_res_1154_; 
v_reconfigure_boxed_1153_ = lean_unbox(v_reconfigure_1152_);
v_res_1154_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(v_inst_1144_, v_inst_1145_, v_inst_1146_, v_ws_1147_, v_resolve_1148_, v_root_1149_, v_next_1150_, v_leanOpts_1151_, v_reconfigure_boxed_1153_);
lean_dec(v_root_1149_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* v_m_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_ws_1159_, lean_object* v_resolve_1160_, lean_object* v_root_1161_, lean_object* v_root__lt_1162_, lean_object* v_next_1163_, lean_object* v_next__lt_1164_, lean_object* v_leanOpts_1165_, uint8_t v_reconfigure_1166_){
_start:
{
lean_object* v_toApplicative_1167_; lean_object* v_toFunctor_1168_; lean_object* v_map_1169_; lean_object* v___f_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_toApplicative_1167_ = lean_ctor_get(v_inst_1156_, 0);
v_toFunctor_1168_ = lean_ctor_get(v_toApplicative_1167_, 0);
v_map_1169_ = lean_ctor_get(v_toFunctor_1168_, 0);
lean_inc(v_map_1169_);
v___f_1170_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0));
v___x_1171_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1156_, v_inst_1157_, v_inst_1158_, v_resolve_1160_, v_leanOpts_1165_, v_reconfigure_1166_, v_ws_1159_, v_root_1161_, v_next_1163_);
v___x_1172_ = lean_apply_4(v_map_1169_, lean_box(0), lean_box(0), v___f_1170_, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object* v_m_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_ws_1177_, lean_object* v_resolve_1178_, lean_object* v_root_1179_, lean_object* v_root__lt_1180_, lean_object* v_next_1181_, lean_object* v_next__lt_1182_, lean_object* v_leanOpts_1183_, lean_object* v_reconfigure_1184_){
_start:
{
uint8_t v_reconfigure_boxed_1185_; lean_object* v_res_1186_; 
v_reconfigure_boxed_1185_ = lean_unbox(v_reconfigure_1184_);
v_res_1186_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(v_m_1173_, v_inst_1174_, v_inst_1175_, v_inst_1176_, v_ws_1177_, v_resolve_1178_, v_root_1179_, v_root__lt_1180_, v_next_1181_, v_next__lt_1182_, v_leanOpts_1183_, v_reconfigure_boxed_1185_);
lean_dec(v_root_1179_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object* v_x_1187_, lean_object* v_init_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_apply_1(v_x_1187_, v_init_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object* v_m_1190_, lean_object* v_00_u03b1_1191_, lean_object* v_x_1192_, lean_object* v_init_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_apply_1(v_x_1192_, v_init_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(lean_object* v_as_1195_, size_t v_i_1196_, size_t v_stop_1197_, lean_object* v_b_1198_){
_start:
{
uint8_t v___x_1199_; 
v___x_1199_ = lean_usize_dec_eq(v_i_1196_, v_stop_1197_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v_name_1201_; lean_object* v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; 
v___x_1200_ = lean_array_uget_borrowed(v_as_1195_, v_i_1196_);
v_name_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_name_1201_);
v___x_1202_ = l_Lean_NameSet_insert(v_b_1198_, v_name_1201_);
v___x_1203_ = ((size_t)1ULL);
v___x_1204_ = lean_usize_add(v_i_1196_, v___x_1203_);
v_i_1196_ = v___x_1204_;
v_b_1198_ = v___x_1202_;
goto _start;
}
else
{
return v_b_1198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2___boxed(lean_object* v_as_1206_, lean_object* v_i_1207_, lean_object* v_stop_1208_, lean_object* v_b_1209_){
_start:
{
size_t v_i_boxed_1210_; size_t v_stop_boxed_1211_; lean_object* v_res_1212_; 
v_i_boxed_1210_ = lean_unbox_usize(v_i_1207_);
lean_dec(v_i_1207_);
v_stop_boxed_1211_ = lean_unbox_usize(v_stop_1208_);
lean_dec(v_stop_1208_);
v_res_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_as_1206_, v_i_boxed_1210_, v_stop_boxed_1211_, v_b_1209_);
lean_dec_ref(v_as_1206_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(lean_object* v_as_1213_, size_t v_sz_1214_, size_t v_i_1215_, lean_object* v_b_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v___x_1219_; 
v___x_1219_ = lean_usize_dec_lt(v_i_1215_, v_sz_1214_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_b_1216_);
lean_ctor_set(v___x_1220_, 1, v___y_1217_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
else
{
lean_object* v_a_1222_; lean_object* v_name_1223_; lean_object* v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; 
v_a_1222_ = lean_array_uget_borrowed(v_as_1213_, v_i_1215_);
v_name_1223_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_name_1223_);
v___x_1224_ = l_Lean_NameSet_insert(v_b_1216_, v_name_1223_);
v___x_1225_ = ((size_t)1ULL);
v___x_1226_ = lean_usize_add(v_i_1215_, v___x_1225_);
v_i_1215_ = v___x_1226_;
v_b_1216_ = v___x_1224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg___boxed(lean_object* v_as_1228_, lean_object* v_sz_1229_, lean_object* v_i_1230_, lean_object* v_b_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
size_t v_sz_boxed_1234_; size_t v_i_boxed_1235_; lean_object* v_res_1236_; 
v_sz_boxed_1234_ = lean_unbox_usize(v_sz_1229_);
lean_dec(v_sz_1229_);
v_i_boxed_1235_ = lean_unbox_usize(v_i_1230_);
lean_dec(v_i_1230_);
v_res_1236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1228_, v_sz_boxed_1234_, v_i_boxed_1235_, v_b_1231_, v___y_1232_);
lean_dec_ref(v_as_1228_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_fst_1239_, lean_object* v_init_1240_, lean_object* v_x_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
if (lean_obj_tag(v_x_1241_) == 0)
{
lean_object* v_k_1245_; lean_object* v_l_1246_; lean_object* v_r_1247_; lean_object* v___x_1248_; 
v_k_1245_ = lean_ctor_get(v_x_1241_, 1);
lean_inc(v_k_1245_);
v_l_1246_ = lean_ctor_get(v_x_1241_, 3);
lean_inc(v_l_1246_);
v_r_1247_ = lean_ctor_get(v_x_1241_, 4);
lean_inc(v_r_1247_);
lean_dec_ref_known(v_x_1241_, 5);
v___x_1248_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1239_, v_init_1240_, v_l_1246_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1268_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1268_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1268_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_snd_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_snd_1253_ = lean_ctor_get(v_a_1249_, 1);
lean_inc(v_snd_1253_);
lean_dec(v_a_1249_);
v___x_1254_ = lean_box(0);
v___x_1255_ = l_Lean_NameSet_contains(v_fst_1239_, v_k_1245_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
lean_dec(v_snd_1253_);
lean_dec(v_r_1247_);
v___x_1256_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__0));
v___x_1257_ = l_Lean_Name_toString(v_k_1245_, v___x_1255_);
v___x_1258_ = lean_string_append(v___x_1256_, v___x_1257_);
lean_dec_ref(v___x_1257_);
v___x_1259_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__1));
v___x_1260_ = lean_string_append(v___x_1258_, v___x_1259_);
v___x_1261_ = 3;
v___x_1262_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*1, v___x_1261_);
lean_inc_ref(v___y_1243_);
v___x_1263_ = lean_apply_2(v___y_1243_, v___x_1262_, lean_box(0));
if (v_isShared_1252_ == 0)
{
lean_ctor_set_tag(v___x_1251_, 1);
lean_ctor_set(v___x_1251_, 0, v___x_1254_);
v___x_1265_ = v___x_1251_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1254_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
else
{
lean_del_object(v___x_1251_);
lean_dec(v_k_1245_);
v_init_1240_ = v___x_1254_;
v_x_1241_ = v_r_1247_;
v___y_1242_ = v_snd_1253_;
goto _start;
}
}
}
else
{
lean_dec(v_r_1247_);
lean_dec(v_k_1245_);
return v___x_1248_;
}
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_init_1240_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___y_1242_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_fst_1272_, lean_object* v_init_1273_, lean_object* v_x_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1272_, v_init_1273_, v_x_1274_, v___y_1275_, v___y_1276_);
lean_dec_ref(v___y_1276_);
lean_dec(v_fst_1272_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(lean_object* v_toUpdate_1279_, lean_object* v___x_1280_, lean_object* v___x_1281_, lean_object* v_entries_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___y_1287_; 
if (lean_obj_tag(v_toUpdate_1279_) == 0)
{
lean_object* v_depConfigs_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_depConfigs_1329_ = lean_ctor_get(v___x_1280_, 12);
v___x_1330_ = l_Lean_NameSet_empty;
v___x_1331_ = lean_array_get_size(v_depConfigs_1329_);
v___x_1332_ = lean_nat_dec_lt(v___x_1281_, v___x_1331_);
if (v___x_1332_ == 0)
{
v___y_1287_ = v___x_1330_;
goto v___jp_1286_;
}
else
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_nat_dec_le(v___x_1331_, v___x_1331_);
if (v___x_1333_ == 0)
{
if (v___x_1332_ == 0)
{
v___y_1287_ = v___x_1330_;
goto v___jp_1286_;
}
else
{
size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = lean_usize_of_nat(v___x_1331_);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_1329_, v___x_1334_, v___x_1335_, v___x_1330_);
v___y_1287_ = v___x_1336_;
goto v___jp_1286_;
}
}
else
{
size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = ((size_t)0ULL);
v___x_1338_ = lean_usize_of_nat(v___x_1331_);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_1329_, v___x_1337_, v___x_1338_, v___x_1330_);
v___y_1287_ = v___x_1339_;
goto v___jp_1286_;
}
}
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v___y_1283_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
v___jp_1286_:
{
size_t v_sz_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v_sz_1288_ = lean_array_size(v_entries_1282_);
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_entries_1282_, v_sz_1288_, v___x_1289_, v___y_1287_, v___y_1283_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v_fst_1292_; lean_object* v_snd_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v_fst_1292_ = lean_ctor_get(v_a_1291_, 0);
lean_inc(v_fst_1292_);
v_snd_1293_ = lean_ctor_get(v_a_1291_, 1);
lean_inc(v_snd_1293_);
lean_dec(v_a_1291_);
v___x_1294_ = lean_box(0);
v___x_1295_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1292_, v___x_1294_, v_toUpdate_1279_, v_snd_1293_, v___y_1284_);
lean_dec(v_fst_1292_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1312_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1312_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1312_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_snd_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1310_; 
v_snd_1300_ = lean_ctor_get(v_a_1296_, 1);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_a_1296_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; 
v_unused_1311_ = lean_ctor_get(v_a_1296_, 0);
lean_dec(v_unused_1311_);
v___x_1302_ = v_a_1296_;
v_isShared_1303_ = v_isSharedCheck_1310_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snd_1300_);
lean_dec(v_a_1296_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1310_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1294_);
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_snd_1300_);
v___x_1305_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1307_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1305_);
v___x_1307_ = v___x_1298_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
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
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_a_1313_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1295_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1295_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v_toUpdate_1279_);
v_a_1321_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1290_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1290_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0___boxed(lean_object* v_toUpdate_1343_, lean_object* v___x_1344_, lean_object* v___x_1345_, lean_object* v_entries_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1343_, v___x_1344_, v___x_1345_, v_entries_1346_, v___y_1347_, v___y_1348_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v_entries_1346_);
lean_dec(v___x_1345_);
lean_dec_ref(v___x_1344_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(lean_object* v_as_1351_, size_t v_i_1352_, size_t v_stop_1353_, lean_object* v_b_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_eq(v_i_1352_, v_stop_1353_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; 
v___x_1358_ = lean_array_uget_borrowed(v_as_1351_, v_i_1352_);
lean_inc_ref(v___y_1355_);
lean_inc(v___x_1358_);
v___x_1359_ = lean_apply_2(v___y_1355_, v___x_1358_, lean_box(0));
v___x_1360_ = ((size_t)1ULL);
v___x_1361_ = lean_usize_add(v_i_1352_, v___x_1360_);
v_i_1352_ = v___x_1361_;
v_b_1354_ = v___x_1359_;
goto _start;
}
else
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_b_1354_);
return v___x_1363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3___boxed(lean_object* v_as_1364_, lean_object* v_i_1365_, lean_object* v_stop_1366_, lean_object* v_b_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
size_t v_i_boxed_1370_; size_t v_stop_boxed_1371_; lean_object* v_res_1372_; 
v_i_boxed_1370_ = lean_unbox_usize(v_i_1365_);
lean_dec(v_i_1365_);
v_stop_boxed_1371_ = lean_unbox_usize(v_stop_1366_);
lean_dec(v_stop_1366_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_as_1364_, v_i_boxed_1370_, v_stop_boxed_1371_, v_b_1367_, v___y_1368_);
lean_dec_ref(v___y_1368_);
lean_dec_ref(v_as_1364_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(lean_object* v_toUpdate_1373_, lean_object* v_as_1374_, size_t v_i_1375_, size_t v_stop_1376_, lean_object* v_b_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_fst_1381_; lean_object* v_snd_1382_; uint8_t v___x_1388_; 
v___x_1388_ = lean_usize_dec_eq(v_i_1375_, v_stop_1376_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; uint8_t v_inherited_1390_; 
v___x_1389_ = lean_array_uget_borrowed(v_as_1374_, v_i_1375_);
v_inherited_1390_ = lean_ctor_get_uint8(v___x_1389_, sizeof(void*)*5);
if (v_inherited_1390_ == 0)
{
lean_object* v_name_1391_; uint8_t v___x_1392_; 
v_name_1391_ = lean_ctor_get(v___x_1389_, 0);
v___x_1392_ = l_Lean_NameSet_contains(v_toUpdate_1373_, v_name_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_box(0);
lean_inc(v___x_1389_);
lean_inc(v_name_1391_);
v___x_1394_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1391_, v___x_1389_, v___y_1378_);
v_fst_1381_ = v___x_1393_;
v_snd_1382_ = v___x_1394_;
goto v___jp_1380_;
}
else
{
goto v___jp_1386_;
}
}
else
{
goto v___jp_1386_;
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_b_1377_);
lean_ctor_set(v___x_1395_, 1, v___y_1378_);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
v___jp_1380_:
{
size_t v___x_1383_; size_t v___x_1384_; 
v___x_1383_ = ((size_t)1ULL);
v___x_1384_ = lean_usize_add(v_i_1375_, v___x_1383_);
v_i_1375_ = v___x_1384_;
v_b_1377_ = v_fst_1381_;
v___y_1378_ = v_snd_1382_;
goto _start;
}
v___jp_1386_:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_box(0);
v_fst_1381_ = v___x_1387_;
v_snd_1382_ = v___y_1378_;
goto v___jp_1380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg___boxed(lean_object* v_toUpdate_1397_, lean_object* v_as_1398_, lean_object* v_i_1399_, lean_object* v_stop_1400_, lean_object* v_b_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
size_t v_i_boxed_1404_; size_t v_stop_boxed_1405_; lean_object* v_res_1406_; 
v_i_boxed_1404_ = lean_unbox_usize(v_i_1399_);
lean_dec(v_i_1399_);
v_stop_boxed_1405_ = lean_unbox_usize(v_stop_1400_);
lean_dec(v_stop_1400_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1397_, v_as_1398_, v_i_boxed_1404_, v_stop_boxed_1405_, v_b_1401_, v___y_1402_);
lean_dec_ref(v_as_1398_);
lean_dec(v_toUpdate_1397_);
return v_res_1406_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1414_ = lean_array_get_size(v___x_1413_);
return v___x_1414_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1415_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_nat_dec_lt(v___x_1416_, v___x_1415_);
return v___x_1417_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7(void){
_start:
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1419_ = lean_nat_dec_le(v___x_1418_, v___x_1418_);
return v___x_1419_;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8(void){
_start:
{
lean_object* v___x_1420_; size_t v___x_1421_; 
v___x_1420_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1421_ = lean_usize_of_nat(v___x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* v_ws_1424_, lean_object* v_toUpdate_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___y_1430_; lean_object* v___y_1435_; lean_object* v_fst_1436_; lean_object* v_snd_1437_; lean_object* v_packages_1456_; lean_object* v___x_1457_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v_val_1462_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___x_1510_; lean_object* v_baseName_1511_; lean_object* v_dir_1512_; lean_object* v_config_1513_; lean_object* v_relManifestFile_1514_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; uint8_t v_fst_1519_; lean_object* v_snd_1520_; lean_object* v_packagesDir_x3f_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1577_; lean_object* v___y_1578_; uint8_t v___x_1582_; lean_object* v_rootName_1583_; lean_object* v_fst_1585_; lean_object* v_snd_1586_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v_val_1655_; lean_object* v___x_1681_; 
v_packages_1456_ = lean_ctor_get(v_ws_1424_, 4);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_array_fget_borrowed(v_packages_1456_, v___x_1457_);
v_baseName_1511_ = lean_ctor_get(v___x_1510_, 1);
v_dir_1512_ = lean_ctor_get(v___x_1510_, 4);
v_config_1513_ = lean_ctor_get(v___x_1510_, 6);
v_relManifestFile_1514_ = lean_ctor_get(v___x_1510_, 9);
v___x_1582_ = 0;
lean_inc(v_baseName_1511_);
v_rootName_1583_ = l_Lean_Name_toString(v_baseName_1511_, v___x_1582_);
lean_inc_ref(v_relManifestFile_1514_);
lean_inc_ref(v_dir_1512_);
v___x_1652_ = l_Lake_joinRelative(v_dir_1512_, v_relManifestFile_1514_);
v___x_1653_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1681_ = l_Lake_Manifest_load(v___x_1652_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 1);
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
v_val_1655_ = v___x_1687_;
goto v___jp_1654_;
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1690_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1681_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1681_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 0);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
v_val_1655_ = v___x_1695_;
goto v___jp_1654_;
}
}
}
v___jp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v___y_1430_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
v___jp_1434_:
{
if (lean_obj_tag(v_fst_1436_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_snd_1437_);
v_a_1438_ = lean_ctor_get(v_fst_1436_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_fst_1436_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1440_ = v_fst_1436_;
v_isShared_1441_ = v_isSharedCheck_1452_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v_fst_1436_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1452_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1442_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_1443_ = lean_io_error_to_string(v_a_1438_);
v___x_1444_ = lean_string_append(v___x_1442_, v___x_1443_);
lean_dec_ref(v___x_1443_);
v___x_1445_ = 3;
v___x_1446_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set_uint8(v___x_1446_, sizeof(void*)*1, v___x_1445_);
lean_inc_ref(v___y_1435_);
v___x_1447_ = lean_apply_2(v___y_1435_, v___x_1446_, lean_box(0));
v___x_1448_ = lean_box(0);
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 1);
lean_ctor_set(v___x_1440_, 0, v___x_1448_);
v___x_1450_ = v___x_1440_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec_ref(v_fst_1436_);
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v_snd_1437_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
}
v___jp_1458_:
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = lean_array_get_size(v___y_1460_);
v___x_1464_ = lean_nat_dec_lt(v___x_1457_, v___x_1463_);
if (v___x_1464_ == 0)
{
v___y_1435_ = v___y_1461_;
v_fst_1436_ = v_val_1462_;
v_snd_1437_ = v___y_1459_;
goto v___jp_1434_;
}
else
{
lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = lean_box(0);
v___x_1466_ = lean_nat_dec_le(v___x_1463_, v___x_1463_);
if (v___x_1466_ == 0)
{
if (v___x_1464_ == 0)
{
v___y_1435_ = v___y_1461_;
v_fst_1436_ = v_val_1462_;
v_snd_1437_ = v___y_1459_;
goto v___jp_1434_;
}
else
{
size_t v___x_1467_; size_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = ((size_t)0ULL);
v___x_1468_ = lean_usize_of_nat(v___x_1463_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1460_, v___x_1467_, v___x_1468_, v___x_1465_, v___y_1461_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_dec_ref_known(v___x_1469_, 1);
v___y_1435_ = v___y_1461_;
v_fst_1436_ = v_val_1462_;
v_snd_1437_ = v___y_1459_;
goto v___jp_1434_;
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_val_1462_);
lean_dec(v___y_1459_);
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
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
return v___x_1475_;
}
}
}
}
}
else
{
size_t v___x_1478_; size_t v___x_1479_; lean_object* v___x_1480_; 
v___x_1478_ = ((size_t)0ULL);
v___x_1479_ = lean_usize_of_nat(v___x_1463_);
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1460_, v___x_1478_, v___x_1479_, v___x_1465_, v___y_1461_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_dec_ref_known(v___x_1480_, 1);
v___y_1435_ = v___y_1461_;
v_fst_1436_ = v_val_1462_;
v_snd_1437_ = v___y_1459_;
goto v___jp_1434_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v_val_1462_);
lean_dec(v___y_1459_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
v___jp_1489_:
{
if (lean_obj_tag(v___y_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
v_a_1494_ = lean_ctor_get(v___y_1493_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___y_1493_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___y_1493_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___y_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 1);
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
v___y_1459_ = v___y_1490_;
v___y_1460_ = v___y_1491_;
v___y_1461_ = v___y_1492_;
v_val_1462_ = v___x_1499_;
goto v___jp_1458_;
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_a_1502_ = lean_ctor_get(v___y_1493_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___y_1493_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___y_1493_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___y_1493_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set_tag(v___x_1504_, 0);
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
v___y_1459_ = v___y_1490_;
v___y_1460_ = v___y_1491_;
v___y_1461_ = v___y_1492_;
v_val_1462_ = v___x_1507_;
goto v___jp_1458_;
}
}
}
}
v___jp_1515_:
{
lean_object* v_toWorkspaceConfig_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v_toWorkspaceConfig_1521_ = lean_ctor_get(v_config_1513_, 0);
v___x_1522_ = l_System_FilePath_normalize(v___y_1516_);
lean_inc_ref(v_toWorkspaceConfig_1521_);
v___x_1523_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1521_);
lean_inc_ref(v___x_1523_);
v___x_1524_ = l_System_FilePath_normalize(v___x_1523_);
v___x_1525_ = lean_string_dec_eq(v___x_1522_, v___x_1524_);
lean_dec_ref(v___x_1524_);
lean_dec_ref(v___x_1522_);
if (v___x_1525_ == 0)
{
if (v_fst_1519_ == 0)
{
lean_dec_ref(v___x_1523_);
lean_dec_ref(v___y_1518_);
v___y_1430_ = v_snd_1520_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1526_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_1527_ = lean_string_append(v___x_1526_, v___y_1518_);
v___x_1528_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_1529_ = lean_string_append(v___x_1527_, v___x_1528_);
lean_inc_ref(v_dir_1512_);
v___x_1530_ = l_Lake_joinRelative(v_dir_1512_, v___x_1523_);
v___x_1531_ = lean_string_append(v___x_1529_, v___x_1530_);
v___x_1532_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1533_ = lean_string_append(v___x_1531_, v___x_1532_);
v___x_1534_ = 1;
v___x_1535_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*1, v___x_1534_);
lean_inc_ref(v___y_1517_);
v___x_1536_ = lean_apply_2(v___y_1517_, v___x_1535_, lean_box(0));
v___x_1537_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_1530_);
v___x_1538_ = l_Lake_createParentDirs(v___x_1530_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1539_; 
lean_dec_ref_known(v___x_1538_, 1);
v___x_1539_ = lean_io_rename(v___y_1518_, v___x_1530_);
lean_dec_ref(v___x_1530_);
lean_dec_ref(v___y_1518_);
v___y_1490_ = v_snd_1520_;
v___y_1491_ = v___x_1537_;
v___y_1492_ = v___y_1517_;
v___y_1493_ = v___x_1539_;
goto v___jp_1489_;
}
else
{
lean_dec_ref(v___x_1530_);
lean_dec_ref(v___y_1518_);
v___y_1490_ = v_snd_1520_;
v___y_1491_ = v___x_1537_;
v___y_1492_ = v___y_1517_;
v___y_1493_ = v___x_1538_;
goto v___jp_1489_;
}
}
}
else
{
lean_dec_ref(v___x_1523_);
lean_dec_ref(v___y_1518_);
v___y_1430_ = v_snd_1520_;
goto v___jp_1429_;
}
}
v___jp_1540_:
{
if (lean_obj_tag(v_packagesDir_x3f_1541_) == 1)
{
lean_object* v_val_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_val_1544_ = lean_ctor_get(v_packagesDir_x3f_1541_, 0);
lean_inc_n(v_val_1544_, 2);
lean_dec_ref_known(v_packagesDir_x3f_1541_, 1);
lean_inc_ref(v_dir_1512_);
v___x_1545_ = l_Lake_joinRelative(v_dir_1512_, v_val_1544_);
v___x_1546_ = l_System_FilePath_pathExists(v___x_1545_);
v___x_1547_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1548_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1548_ == 0)
{
v___y_1516_ = v_val_1544_;
v___y_1517_ = v___y_1543_;
v___y_1518_ = v___x_1545_;
v_fst_1519_ = v___x_1546_;
v_snd_1520_ = v___y_1542_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1550_ == 0)
{
if (v___x_1548_ == 0)
{
v___y_1516_ = v_val_1544_;
v___y_1517_ = v___y_1543_;
v___y_1518_ = v___x_1545_;
v_fst_1519_ = v___x_1546_;
v_snd_1520_ = v___y_1542_;
goto v___jp_1515_;
}
else
{
size_t v___x_1551_; size_t v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = ((size_t)0ULL);
v___x_1552_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1547_, v___x_1551_, v___x_1552_, v___x_1549_, v___y_1543_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_dec_ref_known(v___x_1553_, 1);
v___y_1516_ = v_val_1544_;
v___y_1517_ = v___y_1543_;
v___y_1518_ = v___x_1545_;
v_fst_1519_ = v___x_1546_;
v_snd_1520_ = v___y_1542_;
goto v___jp_1515_;
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec_ref(v___x_1545_);
lean_dec(v_val_1544_);
lean_dec(v___y_1542_);
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
else
{
size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1547_, v___x_1562_, v___x_1563_, v___x_1549_, v___y_1543_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_dec_ref_known(v___x_1564_, 1);
v___y_1516_ = v_val_1544_;
v___y_1517_ = v___y_1543_;
v___y_1518_ = v___x_1545_;
v_fst_1519_ = v___x_1546_;
v_snd_1520_ = v___y_1542_;
goto v___jp_1515_;
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec_ref(v___x_1545_);
lean_dec(v_val_1544_);
lean_dec(v___y_1542_);
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec(v_packagesDir_x3f_1541_);
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v___y_1542_);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
v___jp_1576_:
{
if (lean_obj_tag(v___y_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v_snd_1580_; lean_object* v_packagesDir_x3f_1581_; 
v_a_1579_ = lean_ctor_get(v___y_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___y_1578_, 1);
v_snd_1580_ = lean_ctor_get(v_a_1579_, 1);
lean_inc(v_snd_1580_);
lean_dec(v_a_1579_);
v_packagesDir_x3f_1581_ = lean_ctor_get(v___y_1577_, 2);
lean_inc(v_packagesDir_x3f_1581_);
lean_dec_ref(v___y_1577_);
v_packagesDir_x3f_1541_ = v_packagesDir_x3f_1581_;
v___y_1542_ = v_snd_1580_;
v___y_1543_ = v_a_1427_;
goto v___jp_1540_;
}
else
{
lean_dec_ref(v___y_1577_);
return v___y_1578_;
}
}
v___jp_1584_:
{
if (lean_obj_tag(v_fst_1585_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1634_; 
v_a_1587_ = lean_ctor_get(v_fst_1585_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_fst_1585_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1589_ = v_fst_1585_;
v_isShared_1590_ = v_isSharedCheck_1634_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v_fst_1585_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1634_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
if (lean_obj_tag(v_a_1587_) == 11)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec_ref_known(v_a_1587_, 2);
lean_del_object(v___x_1589_);
v___x_1591_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_1592_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1425_, v___x_1510_, v___x_1457_, v___x_1591_, v_snd_1586_, v_a_1427_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1614_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1614_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1614_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_snd_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1612_; 
v_snd_1597_ = lean_ctor_get(v_a_1593_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_a_1593_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v_a_1593_, 0);
lean_dec(v_unused_1613_);
v___x_1599_ = v_a_1593_;
v_isShared_1600_ = v_isSharedCheck_1612_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_snd_1597_);
lean_dec(v_a_1593_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1612_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1601_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_1602_ = lean_string_append(v_rootName_1583_, v___x_1601_);
v___x_1603_ = 1;
v___x_1604_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*1, v___x_1603_);
lean_inc_ref(v_a_1427_);
v___x_1605_ = lean_apply_2(v_a_1427_, v___x_1604_, lean_box(0));
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1605_);
v___x_1607_ = v___x_1599_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_snd_1597_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1607_);
v___x_1609_ = v___x_1595_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_1583_);
return v___x_1592_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_1425_) == 0)
{
lean_object* v___x_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_dec_ref_known(v_toUpdate_1425_, 5);
lean_dec(v_snd_1586_);
lean_dec_ref(v_rootName_1583_);
v___x_1615_ = lean_io_error_to_string(v_a_1587_);
v___x_1616_ = 3;
v___x_1617_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*1, v___x_1616_);
lean_inc_ref(v_a_1427_);
v___x_1618_ = lean_apply_2(v_a_1427_, v___x_1617_, lean_box(0));
v___x_1619_ = lean_box(0);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 1);
lean_ctor_set(v___x_1589_, 0, v___x_1619_);
v___x_1621_ = v___x_1589_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1623_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_1624_ = lean_string_append(v_rootName_1583_, v___x_1623_);
v___x_1625_ = lean_io_error_to_string(v_a_1587_);
v___x_1626_ = lean_string_append(v___x_1624_, v___x_1625_);
lean_dec_ref(v___x_1625_);
v___x_1627_ = 2;
v___x_1628_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set_uint8(v___x_1628_, sizeof(void*)*1, v___x_1627_);
lean_inc_ref(v_a_1427_);
v___x_1629_ = lean_apply_2(v_a_1427_, v___x_1628_, lean_box(0));
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v_snd_1586_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1630_);
v___x_1632_ = v___x_1589_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v_packagesDir_x3f_1636_; lean_object* v_packages_1637_; lean_object* v___x_1638_; 
lean_dec_ref(v_rootName_1583_);
v_a_1635_ = lean_ctor_get(v_fst_1585_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v_fst_1585_, 1);
v_packagesDir_x3f_1636_ = lean_ctor_get(v_a_1635_, 2);
v_packages_1637_ = lean_ctor_get(v_a_1635_, 3);
lean_inc(v_toUpdate_1425_);
v___x_1638_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1425_, v___x_1510_, v___x_1457_, v_packages_1637_, v_snd_1586_, v_a_1427_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
if (lean_obj_tag(v_toUpdate_1425_) == 0)
{
lean_object* v_snd_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v_snd_1640_ = lean_ctor_get(v_a_1639_, 1);
lean_inc(v_snd_1640_);
lean_dec(v_a_1639_);
v___x_1641_ = lean_array_get_size(v_packages_1637_);
v___x_1642_ = lean_nat_dec_lt(v___x_1457_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_inc(v_packagesDir_x3f_1636_);
lean_dec_ref_known(v_toUpdate_1425_, 5);
lean_dec(v_a_1635_);
v_packagesDir_x3f_1541_ = v_packagesDir_x3f_1636_;
v___y_1542_ = v_snd_1640_;
v___y_1543_ = v_a_1427_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_nat_dec_le(v___x_1641_, v___x_1641_);
if (v___x_1644_ == 0)
{
if (v___x_1642_ == 0)
{
lean_inc(v_packagesDir_x3f_1636_);
lean_dec_ref_known(v_toUpdate_1425_, 5);
lean_dec(v_a_1635_);
v_packagesDir_x3f_1541_ = v_packagesDir_x3f_1636_;
v___y_1542_ = v_snd_1640_;
v___y_1543_ = v_a_1427_;
goto v___jp_1540_;
}
else
{
size_t v___x_1645_; size_t v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = ((size_t)0ULL);
v___x_1646_ = lean_usize_of_nat(v___x_1641_);
v___x_1647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1425_, v_packages_1637_, v___x_1645_, v___x_1646_, v___x_1643_, v_snd_1640_);
lean_dec_ref_known(v_toUpdate_1425_, 5);
v___y_1577_ = v_a_1635_;
v___y_1578_ = v___x_1647_;
goto v___jp_1576_;
}
}
else
{
size_t v___x_1648_; size_t v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = ((size_t)0ULL);
v___x_1649_ = lean_usize_of_nat(v___x_1641_);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1425_, v_packages_1637_, v___x_1648_, v___x_1649_, v___x_1643_, v_snd_1640_);
lean_dec_ref_known(v_toUpdate_1425_, 5);
v___y_1577_ = v_a_1635_;
v___y_1578_ = v___x_1650_;
goto v___jp_1576_;
}
}
}
else
{
lean_object* v_snd_1651_; 
lean_inc(v_packagesDir_x3f_1636_);
lean_dec(v_a_1635_);
v_snd_1651_ = lean_ctor_get(v_a_1639_, 1);
lean_inc(v_snd_1651_);
lean_dec(v_a_1639_);
v_packagesDir_x3f_1541_ = v_packagesDir_x3f_1636_;
v___y_1542_ = v_snd_1651_;
v___y_1543_ = v_a_1427_;
goto v___jp_1540_;
}
}
else
{
lean_dec(v_a_1635_);
lean_dec(v_toUpdate_1425_);
return v___x_1638_;
}
}
}
v___jp_1654_:
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1656_ == 0)
{
v_fst_1585_ = v_val_1655_;
v_snd_1586_ = v_a_1426_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1658_ == 0)
{
if (v___x_1656_ == 0)
{
v_fst_1585_ = v_val_1655_;
v_snd_1586_ = v_a_1426_;
goto v___jp_1584_;
}
else
{
size_t v___x_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = ((size_t)0ULL);
v___x_1660_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1653_, v___x_1659_, v___x_1660_, v___x_1657_, v_a_1427_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_dec_ref_known(v___x_1661_, 1);
v_fst_1585_ = v_val_1655_;
v_snd_1586_ = v_a_1426_;
goto v___jp_1584_;
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v_val_1655_);
lean_dec_ref(v_rootName_1583_);
lean_dec(v_a_1426_);
lean_dec(v_toUpdate_1425_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
else
{
size_t v___x_1670_; size_t v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = ((size_t)0ULL);
v___x_1671_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1653_, v___x_1670_, v___x_1671_, v___x_1657_, v_a_1427_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_dec_ref_known(v___x_1672_, 1);
v_fst_1585_ = v_val_1655_;
v_snd_1586_ = v_a_1426_;
goto v___jp_1584_;
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v_val_1655_);
lean_dec_ref(v_rootName_1583_);
lean_dec(v_a_1426_);
lean_dec(v_toUpdate_1425_);
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_1698_, lean_object* v_toUpdate_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1698_, v_toUpdate_1699_, v_a_1700_, v_a_1701_);
lean_dec_ref(v_a_1701_);
lean_dec_ref(v_ws_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* v_as_1704_, size_t v_sz_1705_, size_t v_i_1706_, lean_object* v_b_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1704_, v_sz_1705_, v_i_1706_, v_b_1707_, v___y_1708_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* v_as_1712_, lean_object* v_sz_1713_, lean_object* v_i_1714_, lean_object* v_b_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
size_t v_sz_boxed_1719_; size_t v_i_boxed_1720_; lean_object* v_res_1721_; 
v_sz_boxed_1719_ = lean_unbox_usize(v_sz_1713_);
lean_dec(v_sz_1713_);
v_i_boxed_1720_ = lean_unbox_usize(v_i_1714_);
lean_dec(v_i_1714_);
v_res_1721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_1712_, v_sz_boxed_1719_, v_i_boxed_1720_, v_b_1715_, v___y_1716_, v___y_1717_);
lean_dec_ref(v___y_1717_);
lean_dec_ref(v_as_1712_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(lean_object* v_toUpdate_1722_, lean_object* v_as_1723_, size_t v_i_1724_, size_t v_stop_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1722_, v_as_1723_, v_i_1724_, v_stop_1725_, v_b_1726_, v___y_1727_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___boxed(lean_object* v_toUpdate_1731_, lean_object* v_as_1732_, lean_object* v_i_1733_, lean_object* v_stop_1734_, lean_object* v_b_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
size_t v_i_boxed_1739_; size_t v_stop_boxed_1740_; lean_object* v_res_1741_; 
v_i_boxed_1739_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_stop_boxed_1740_ = lean_unbox_usize(v_stop_1734_);
lean_dec(v_stop_1734_);
v_res_1741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(v_toUpdate_1731_, v_as_1732_, v_i_boxed_1739_, v_stop_boxed_1740_, v_b_1735_, v___y_1736_, v___y_1737_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v_as_1732_);
lean_dec(v_toUpdate_1731_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_dep_1742_, lean_object* v_as_1743_, size_t v_i_1744_, size_t v_stop_1745_, lean_object* v_b_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_fst_1750_; lean_object* v_snd_1751_; lean_object* v___y_1756_; lean_object* v_name_1757_; uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_eq(v_i_1744_, v_stop_1745_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v_name_1762_; lean_object* v_scope_1763_; lean_object* v_configFile_1764_; lean_object* v_manifestFile_x3f_1765_; lean_object* v_src_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1789_; 
v___x_1761_ = lean_array_uget(v_as_1743_, v_i_1744_);
v_name_1762_ = lean_ctor_get(v___x_1761_, 0);
v_scope_1763_ = lean_ctor_get(v___x_1761_, 1);
v_configFile_1764_ = lean_ctor_get(v___x_1761_, 2);
v_manifestFile_x3f_1765_ = lean_ctor_get(v___x_1761_, 3);
v_src_1766_ = lean_ctor_get(v___x_1761_, 4);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1768_ = v___x_1761_;
v_isShared_1769_ = v_isSharedCheck_1789_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_src_1766_);
lean_inc(v_manifestFile_x3f_1765_);
lean_inc(v_configFile_1764_);
lean_inc(v_scope_1763_);
lean_inc(v_name_1762_);
lean_dec(v___x_1761_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1789_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
uint8_t v___x_1770_; 
v___x_1770_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1762_, v___y_1747_);
if (v___x_1770_ == 0)
{
uint8_t v___x_1771_; 
v___x_1771_ = 1;
if (lean_obj_tag(v_src_1766_) == 0)
{
lean_object* v_dir_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1784_; 
v_dir_1772_ = lean_ctor_get(v_src_1766_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_src_1766_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1774_ = v_src_1766_;
v_isShared_1775_ = v_isSharedCheck_1784_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_dir_1772_);
lean_dec(v_src_1766_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1784_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_relPkgDir_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v_relPkgDir_1776_ = lean_ctor_get(v_dep_1742_, 1);
lean_inc_ref(v_relPkgDir_1776_);
v___x_1777_ = l_Lake_joinRelative(v_relPkgDir_1776_, v_dir_1772_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1777_);
v___x_1779_ = v___x_1774_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
lean_inc(v_name_1762_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 4, v___x_1779_);
v___x_1781_ = v___x_1768_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_name_1762_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_scope_1763_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_configFile_1764_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_manifestFile_x3f_1765_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_ctor_set_uint8(v___x_1781_, sizeof(void*)*5, v___x_1771_);
v___y_1756_ = v___x_1781_;
v_name_1757_ = v_name_1762_;
goto v___jp_1755_;
}
}
}
}
else
{
lean_object* v___x_1786_; 
lean_inc(v_name_1762_);
if (v_isShared_1769_ == 0)
{
v___x_1786_ = v___x_1768_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_name_1762_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_scope_1763_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_configFile_1764_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v_manifestFile_x3f_1765_);
lean_ctor_set(v_reuseFailAlloc_1787_, 4, v_src_1766_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*5, v___x_1771_);
v___y_1756_ = v___x_1786_;
v_name_1757_ = v_name_1762_;
goto v___jp_1755_;
}
}
}
else
{
lean_object* v___x_1788_; 
lean_del_object(v___x_1768_);
lean_dec_ref(v_src_1766_);
lean_dec(v_manifestFile_x3f_1765_);
lean_dec_ref(v_configFile_1764_);
lean_dec_ref(v_scope_1763_);
lean_dec(v_name_1762_);
v___x_1788_ = lean_box(0);
v_fst_1750_ = v___x_1788_;
v_snd_1751_ = v___y_1747_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_dec_ref(v_dep_1742_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_b_1746_);
lean_ctor_set(v___x_1790_, 1, v___y_1747_);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
v___jp_1749_:
{
size_t v___x_1752_; size_t v___x_1753_; 
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_add(v_i_1744_, v___x_1752_);
v_i_1744_ = v___x_1753_;
v_b_1746_ = v_fst_1750_;
v___y_1747_ = v_snd_1751_;
goto _start;
}
v___jp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_box(0);
v___x_1759_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1757_, v___y_1756_, v___y_1747_);
v_fst_1750_ = v___x_1758_;
v_snd_1751_ = v___x_1759_;
goto v___jp_1749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1792_, lean_object* v_as_1793_, lean_object* v_i_1794_, lean_object* v_stop_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
size_t v_i_boxed_1799_; size_t v_stop_boxed_1800_; lean_object* v_res_1801_; 
v_i_boxed_1799_ = lean_unbox_usize(v_i_1794_);
lean_dec(v_i_1794_);
v_stop_boxed_1800_ = lean_unbox_usize(v_stop_1795_);
lean_dec(v_stop_1795_);
v_res_1801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1792_, v_as_1793_, v_i_boxed_1799_, v_stop_boxed_1800_, v_b_1796_, v___y_1797_);
lean_dec_ref(v_as_1793_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_manifestEntry_1808_; lean_object* v_pkgDir_1809_; lean_object* v_name_1810_; lean_object* v_manifestFile_x3f_1811_; lean_object* v___y_1813_; lean_object* v_fst_1814_; lean_object* v_snd_1815_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v_val_1875_; lean_object* v___y_1903_; 
v_manifestEntry_1808_ = lean_ctor_get(v_dep_1804_, 4);
v_pkgDir_1809_ = lean_ctor_get(v_dep_1804_, 0);
v_name_1810_ = lean_ctor_get(v_manifestEntry_1808_, 0);
v_manifestFile_x3f_1811_ = lean_ctor_get(v_manifestEntry_1808_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1811_) == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1809_);
v___x_1924_ = l_Lake_joinRelative(v_pkgDir_1809_, v___x_1923_);
v___y_1903_ = v___x_1924_;
goto v___jp_1902_;
}
else
{
lean_object* v_val_1925_; lean_object* v___x_1926_; 
v_val_1925_ = lean_ctor_get(v_manifestFile_x3f_1811_, 0);
lean_inc(v_val_1925_);
lean_inc_ref(v_pkgDir_1809_);
v___x_1926_ = l_Lake_joinRelative(v_pkgDir_1809_, v_val_1925_);
v___y_1903_ = v___x_1926_;
goto v___jp_1902_;
}
v___jp_1812_:
{
if (lean_obj_tag(v_fst_1814_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1845_; 
lean_inc(v_name_1810_);
lean_dec_ref(v_dep_1804_);
v_a_1816_ = lean_ctor_get(v_fst_1814_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_fst_1814_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1818_ = v_fst_1814_;
v_isShared_1819_ = v_isSharedCheck_1845_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v_fst_1814_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1845_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
if (lean_obj_tag(v_a_1816_) == 11)
{
uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
lean_dec_ref_known(v_a_1816_, 2);
v___x_1820_ = 0;
v___x_1821_ = l_Lean_Name_toString(v_name_1810_, v___x_1820_);
v___x_1822_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1823_ = lean_string_append(v___x_1821_, v___x_1822_);
v___x_1824_ = lean_string_append(v___x_1823_, v___y_1813_);
lean_dec_ref(v___y_1813_);
v___x_1825_ = 2;
v___x_1826_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set_uint8(v___x_1826_, sizeof(void*)*1, v___x_1825_);
lean_inc_ref(v_a_1806_);
v___x_1827_ = lean_apply_2(v_a_1806_, v___x_1826_, lean_box(0));
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v_snd_1815_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1828_);
v___x_1830_ = v___x_1818_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
else
{
uint8_t v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
lean_dec_ref(v___y_1813_);
v___x_1832_ = 0;
v___x_1833_ = l_Lean_Name_toString(v_name_1810_, v___x_1832_);
v___x_1834_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1835_ = lean_string_append(v___x_1833_, v___x_1834_);
v___x_1836_ = lean_io_error_to_string(v_a_1816_);
v___x_1837_ = lean_string_append(v___x_1835_, v___x_1836_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = 2;
v___x_1839_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set_uint8(v___x_1839_, sizeof(void*)*1, v___x_1838_);
lean_inc_ref(v_a_1806_);
v___x_1840_ = lean_apply_2(v_a_1806_, v___x_1839_, lean_box(0));
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v_snd_1815_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1841_);
v___x_1843_ = v___x_1818_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
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
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v___y_1813_);
v_a_1846_ = lean_ctor_get(v_fst_1814_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_fst_1814_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1848_ = v_fst_1814_;
v_isShared_1849_ = v_isSharedCheck_1870_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v_fst_1814_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1870_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v_packages_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v_packages_1850_ = lean_ctor_get(v_a_1846_, 3);
lean_inc_ref(v_packages_1850_);
lean_dec(v_a_1846_);
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_array_get_size(v_packages_1850_);
v___x_1853_ = lean_box(0);
v___x_1854_ = lean_nat_dec_lt(v___x_1851_, v___x_1852_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec_ref(v_packages_1850_);
lean_dec_ref(v_dep_1804_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v_snd_1815_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1855_);
v___x_1857_ = v___x_1848_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
else
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_nat_dec_le(v___x_1852_, v___x_1852_);
if (v___x_1859_ == 0)
{
if (v___x_1854_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
lean_dec_ref(v_packages_1850_);
lean_dec_ref(v_dep_1804_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1853_);
lean_ctor_set(v___x_1860_, 1, v_snd_1815_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1860_);
v___x_1862_ = v___x_1848_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
else
{
size_t v___x_1864_; size_t v___x_1865_; lean_object* v___x_1866_; 
lean_del_object(v___x_1848_);
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = lean_usize_of_nat(v___x_1852_);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1804_, v_packages_1850_, v___x_1864_, v___x_1865_, v___x_1853_, v_snd_1815_);
lean_dec_ref(v_packages_1850_);
return v___x_1866_;
}
}
else
{
size_t v___x_1867_; size_t v___x_1868_; lean_object* v___x_1869_; 
lean_del_object(v___x_1848_);
v___x_1867_ = ((size_t)0ULL);
v___x_1868_ = lean_usize_of_nat(v___x_1852_);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1804_, v_packages_1850_, v___x_1867_, v___x_1868_, v___x_1853_, v_snd_1815_);
lean_dec_ref(v_packages_1850_);
return v___x_1869_;
}
}
}
}
}
v___jp_1871_:
{
lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = lean_array_get_size(v___y_1872_);
v___x_1877_ = lean_nat_dec_lt(v___y_1873_, v___x_1876_);
if (v___x_1877_ == 0)
{
v___y_1813_ = v___y_1874_;
v_fst_1814_ = v_val_1875_;
v_snd_1815_ = v_a_1805_;
goto v___jp_1812_;
}
else
{
lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = lean_box(0);
v___x_1879_ = lean_nat_dec_le(v___x_1876_, v___x_1876_);
if (v___x_1879_ == 0)
{
if (v___x_1877_ == 0)
{
v___y_1813_ = v___y_1874_;
v_fst_1814_ = v_val_1875_;
v_snd_1815_ = v_a_1805_;
goto v___jp_1812_;
}
else
{
size_t v___x_1880_; size_t v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = ((size_t)0ULL);
v___x_1881_ = lean_usize_of_nat(v___x_1876_);
v___x_1882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1872_, v___x_1880_, v___x_1881_, v___x_1878_, v_a_1806_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_dec_ref_known(v___x_1882_, 1);
v___y_1813_ = v___y_1874_;
v_fst_1814_ = v_val_1875_;
v_snd_1815_ = v_a_1805_;
goto v___jp_1812_;
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref(v_val_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v_a_1805_);
lean_dec_ref(v_dep_1804_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
else
{
size_t v___x_1891_; size_t v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = ((size_t)0ULL);
v___x_1892_ = lean_usize_of_nat(v___x_1876_);
v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1872_, v___x_1891_, v___x_1892_, v___x_1878_, v_a_1806_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_dec_ref_known(v___x_1893_, 1);
v___y_1813_ = v___y_1874_;
v_fst_1814_ = v_val_1875_;
v_snd_1815_ = v_a_1805_;
goto v___jp_1812_;
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v_val_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v_a_1805_);
lean_dec_ref(v_dep_1804_);
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
}
v___jp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1903_);
v___x_1906_ = l_Lake_Manifest_load(v___y_1903_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 1);
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
v___y_1872_ = v___x_1905_;
v___y_1873_ = v___x_1904_;
v___y_1874_ = v___y_1903_;
v_val_1875_ = v___x_1912_;
goto v___jp_1871_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1906_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1906_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 0);
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
v___y_1872_ = v___x_1905_;
v___y_1873_ = v___x_1904_;
v___y_1874_ = v___y_1903_;
v_val_1875_ = v___x_1920_;
goto v___jp_1871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1927_, v_a_1928_, v_a_1929_);
lean_dec_ref(v_a_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1932_, lean_object* v_as_1933_, size_t v_i_1934_, size_t v_stop_1935_, lean_object* v_b_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1932_, v_as_1933_, v_i_1934_, v_stop_1935_, v_b_1936_, v___y_1937_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1941_, lean_object* v_as_1942_, lean_object* v_i_1943_, lean_object* v_stop_1944_, lean_object* v_b_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
size_t v_i_boxed_1949_; size_t v_stop_boxed_1950_; lean_object* v_res_1951_; 
v_i_boxed_1949_ = lean_unbox_usize(v_i_1943_);
lean_dec(v_i_1943_);
v_stop_boxed_1950_ = lean_unbox_usize(v_stop_1944_);
lean_dec(v_stop_1944_);
v_res_1951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1941_, v_as_1942_, v_i_boxed_1949_, v_stop_boxed_1950_, v_b_1945_, v___y_1946_, v___y_1947_);
lean_dec_ref(v___y_1947_);
lean_dec_ref(v_as_1942_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1953_, lean_object* v_pkg_1954_, lean_object* v_dep_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
uint8_t v___y_1960_; lean_object* v___y_1961_; lean_object* v_name_1991_; lean_object* v___x_1992_; 
v_name_1991_ = lean_ctor_get(v_dep_1955_, 0);
v___x_1992_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1956_, v_name_1991_);
if (lean_obj_tag(v___x_1992_) == 1)
{
lean_object* v_val_1993_; lean_object* v_lakeEnv_1994_; lean_object* v_packages_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_config_1998_; lean_object* v_dir_1999_; lean_object* v_toWorkspaceConfig_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_dec_ref(v_dep_1955_);
lean_dec_ref(v_pkg_1954_);
v_val_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_val_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v_lakeEnv_1994_ = lean_ctor_get(v_ws_1953_, 0);
lean_inc_ref(v_lakeEnv_1994_);
v_packages_1995_ = lean_ctor_get(v_ws_1953_, 4);
lean_inc_ref(v_packages_1995_);
lean_dec_ref(v_ws_1953_);
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = lean_array_fget(v_packages_1995_, v___x_1996_);
lean_dec_ref(v_packages_1995_);
v_config_1998_ = lean_ctor_get(v___x_1997_, 6);
lean_inc_ref(v_config_1998_);
v_dir_1999_ = lean_ctor_get(v___x_1997_, 4);
lean_inc_ref(v_dir_1999_);
lean_dec(v___x_1997_);
v_toWorkspaceConfig_2000_ = lean_ctor_get(v_config_1998_, 0);
lean_inc_ref(v_toWorkspaceConfig_2000_);
lean_dec_ref(v_config_1998_);
v___x_2001_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2000_);
v___x_2002_ = l_Lake_PackageEntry_materialize(v_val_1993_, v_lakeEnv_1994_, v_dir_1999_, v___x_2001_, v_a_1957_);
lean_dec_ref(v_lakeEnv_1994_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2011_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v_a_2003_);
lean_ctor_set(v___x_2007_, 1, v_a_1956_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2007_);
v___x_2009_ = v___x_2005_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v_a_1956_);
v_a_2012_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2002_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2002_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
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
else
{
lean_object* v_wsIdx_2020_; lean_object* v_relDir_2021_; uint8_t v___y_2023_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
lean_dec(v___x_1992_);
v_wsIdx_2020_ = lean_ctor_get(v_pkg_1954_, 0);
lean_inc(v_wsIdx_2020_);
v_relDir_2021_ = lean_ctor_get(v_pkg_1954_, 5);
lean_inc_ref(v_relDir_2021_);
lean_dec_ref(v_pkg_1954_);
v___x_2027_ = lean_unsigned_to_nat(0u);
v___x_2028_ = lean_nat_dec_eq(v_wsIdx_2020_, v___x_2027_);
lean_dec(v_wsIdx_2020_);
if (v___x_2028_ == 0)
{
uint8_t v___x_2029_; 
v___x_2029_ = 1;
v___y_2023_ = v___x_2029_;
goto v___jp_2022_;
}
else
{
uint8_t v___x_2030_; 
v___x_2030_ = 0;
v___y_2023_ = v___x_2030_;
goto v___jp_2022_;
}
v___jp_2022_:
{
lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2025_ = lean_string_dec_eq(v_relDir_2021_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lake_joinRelative(v_relDir_2021_, v___x_2024_);
v___y_1960_ = v___y_2023_;
v___y_1961_ = v___x_2026_;
goto v___jp_1959_;
}
else
{
v___y_1960_ = v___y_2023_;
v___y_1961_ = v_relDir_2021_;
goto v___jp_1959_;
}
}
}
v___jp_1959_:
{
lean_object* v_lakeEnv_1962_; lean_object* v_packages_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v_config_1966_; lean_object* v_dir_1967_; lean_object* v_toWorkspaceConfig_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_lakeEnv_1962_ = lean_ctor_get(v_ws_1953_, 0);
lean_inc_ref(v_lakeEnv_1962_);
v_packages_1963_ = lean_ctor_get(v_ws_1953_, 4);
lean_inc_ref(v_packages_1963_);
lean_dec_ref(v_ws_1953_);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_array_fget(v_packages_1963_, v___x_1964_);
lean_dec_ref(v_packages_1963_);
v_config_1966_ = lean_ctor_get(v___x_1965_, 6);
lean_inc_ref(v_config_1966_);
v_dir_1967_ = lean_ctor_get(v___x_1965_, 4);
lean_inc_ref(v_dir_1967_);
lean_dec(v___x_1965_);
v_toWorkspaceConfig_1968_ = lean_ctor_get(v_config_1966_, 0);
lean_inc_ref(v_toWorkspaceConfig_1968_);
lean_dec_ref(v_config_1966_);
v___x_1969_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1968_);
v___x_1970_ = l_Lake_Dependency_materialize(v_dep_1955_, v___y_1960_, v_lakeEnv_1962_, v_dir_1967_, v___x_1969_, v___y_1961_, v_a_1957_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1982_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1982_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1982_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_manifestEntry_1975_; lean_object* v_name_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v_manifestEntry_1975_ = lean_ctor_get(v_a_1971_, 4);
v_name_1976_ = lean_ctor_get(v_manifestEntry_1975_, 0);
lean_inc_ref(v_manifestEntry_1975_);
lean_inc(v_name_1976_);
v___x_1977_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1976_, v_manifestEntry_1975_, v_a_1956_);
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v_a_1971_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1978_);
v___x_1980_ = v___x_1973_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_a_1956_);
v_a_1983_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1970_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1970_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_2031_, lean_object* v_pkg_2032_, lean_object* v_dep_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2031_, v_pkg_2032_, v_dep_2033_, v_a_2034_, v_a_2035_);
lean_dec_ref(v_a_2035_);
return v_res_2037_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_2038_; 
v___x_2038_ = 4;
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_2039_, lean_object* v_tc_x3f_2040_, uint8_t v_fixed_2041_, lean_object* v_self_2042_){
_start:
{
lean_object* v_clashes_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v_clashes_2043_ = lean_ctor_get(v_self_2042_, 2);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_self_2042_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; lean_object* v_unused_2052_; 
v_unused_2051_ = lean_ctor_get(v_self_2042_, 1);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_self_2042_, 0);
lean_dec(v_unused_2052_);
v___x_2045_ = v_self_2042_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_clashes_2043_);
lean_dec(v_self_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 1, v_tc_x3f_2040_);
lean_ctor_set(v___x_2045_, 0, v_src_2039_);
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_src_2039_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_tc_x3f_2040_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_clashes_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*3, v_fixed_2041_);
return v___x_2048_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_2053_, lean_object* v_tc_x3f_2054_, lean_object* v_fixed_2055_, lean_object* v_self_2056_){
_start:
{
uint8_t v_fixed_boxed_2057_; lean_object* v_res_2058_; 
v_fixed_boxed_2057_ = lean_unbox(v_fixed_2055_);
v_res_2058_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_2053_, v_tc_x3f_2054_, v_fixed_boxed_2057_, v_self_2056_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_2059_, lean_object* v_ver_2060_, uint8_t v_fixed_2061_, lean_object* v_self_2062_){
_start:
{
lean_object* v_src_2063_; lean_object* v_tc_x3f_2064_; lean_object* v_clashes_2065_; uint8_t v_fixed_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2075_; 
v_src_2063_ = lean_ctor_get(v_self_2062_, 0);
v_tc_x3f_2064_ = lean_ctor_get(v_self_2062_, 1);
v_clashes_2065_ = lean_ctor_get(v_self_2062_, 2);
v_fixed_2066_ = lean_ctor_get_uint8(v_self_2062_, sizeof(void*)*3);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_self_2062_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2068_ = v_self_2062_;
v_isShared_2069_ = v_isSharedCheck_2075_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_clashes_2065_);
lean_inc(v_tc_x3f_2064_);
lean_inc(v_src_2063_);
lean_dec(v_self_2062_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2075_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2070_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2070_, 0, v_src_2059_);
lean_ctor_set(v___x_2070_, 1, v_ver_2060_);
lean_ctor_set_uint8(v___x_2070_, sizeof(void*)*2, v_fixed_2061_);
v___x_2071_ = lean_array_push(v_clashes_2065_, v___x_2070_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 2, v___x_2071_);
v___x_2073_ = v___x_2068_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_src_2063_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_tc_x3f_2064_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v___x_2071_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*3, v_fixed_2066_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_2076_, lean_object* v_ver_2077_, lean_object* v_fixed_2078_, lean_object* v_self_2079_){
_start:
{
uint8_t v_fixed_boxed_2080_; lean_object* v_res_2081_; 
v_fixed_boxed_2080_ = lean_unbox(v_fixed_2078_);
v_res_2081_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_2076_, v_ver_2077_, v_fixed_boxed_2080_, v_self_2079_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v_as_2086_, size_t v_i_2087_, size_t v_stop_2088_, lean_object* v_b_2089_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = lean_usize_dec_eq(v_i_2087_, v_stop_2088_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v_src_2092_; lean_object* v_ver_2093_; uint8_t v_fixed_2094_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2110_; 
v___x_2091_ = lean_array_uget_borrowed(v_as_2086_, v_i_2087_);
v_src_2092_ = lean_ctor_get(v___x_2091_, 0);
v_ver_2093_ = lean_ctor_get(v___x_2091_, 1);
v_fixed_2094_ = lean_ctor_get_uint8(v___x_2091_, sizeof(void*)*2);
if (v_fixed_2094_ == 0)
{
lean_object* v___x_2114_; 
v___x_2114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2110_ = v___x_2114_;
goto v___jp_2109_;
}
else
{
lean_object* v___x_2115_; 
v___x_2115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2110_ = v___x_2115_;
goto v___jp_2109_;
}
v___jp_2095_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; size_t v___x_2106_; size_t v___x_2107_; 
v___x_2099_ = lean_string_append(v___y_2097_, v___y_2098_);
lean_dec_ref(v___y_2098_);
v___x_2100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2101_ = lean_string_append(v___x_2099_, v___x_2100_);
v___x_2102_ = 1;
lean_inc(v_src_2092_);
v___x_2103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2092_, v___x_2102_);
v___x_2104_ = lean_string_append(v___x_2101_, v___x_2103_);
lean_dec_ref(v___x_2103_);
v___x_2105_ = lean_string_append(v___x_2104_, v___y_2096_);
v___x_2106_ = ((size_t)1ULL);
v___x_2107_ = lean_usize_add(v_i_2087_, v___x_2106_);
v_i_2087_ = v___x_2107_;
v_b_2089_ = v___x_2105_;
goto _start;
}
v___jp_2109_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_toString_2113_; 
v___x_2111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2112_ = lean_string_append(v_b_2089_, v___x_2111_);
v_toString_2113_ = lean_ctor_get(v_ver_2093_, 0);
lean_inc_ref(v_toString_2113_);
v___y_2096_ = v___y_2110_;
v___y_2097_ = v___x_2112_;
v___y_2098_ = v_toString_2113_;
goto v___jp_2095_;
}
}
else
{
return v_b_2089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v_as_2116_, lean_object* v_i_2117_, lean_object* v_stop_2118_, lean_object* v_b_2119_){
_start:
{
size_t v_i_boxed_2120_; size_t v_stop_boxed_2121_; lean_object* v_res_2122_; 
v_i_boxed_2120_ = lean_unbox_usize(v_i_2117_);
lean_dec(v_i_2117_);
v_stop_boxed_2121_ = lean_unbox_usize(v_stop_2118_);
lean_dec(v_stop_2118_);
v_res_2122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_2116_, v_i_boxed_2120_, v_stop_boxed_2121_, v_b_2119_);
lean_dec_ref(v_as_2116_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v_as_2123_, size_t v_i_2124_, size_t v_stop_2125_, lean_object* v_b_2126_){
_start:
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_usize_dec_eq(v_i_2124_, v_stop_2125_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v_src_2129_; lean_object* v_ver_2130_; uint8_t v_fixed_2131_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2147_; 
v___x_2128_ = lean_array_uget_borrowed(v_as_2123_, v_i_2124_);
v_src_2129_ = lean_ctor_get(v___x_2128_, 0);
v_ver_2130_ = lean_ctor_get(v___x_2128_, 1);
v_fixed_2131_ = lean_ctor_get_uint8(v___x_2128_, sizeof(void*)*2);
if (v_fixed_2131_ == 0)
{
lean_object* v___x_2151_; 
v___x_2151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2147_ = v___x_2151_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2152_; 
v___x_2152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2147_ = v___x_2152_;
goto v___jp_2146_;
}
v___jp_2132_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; size_t v___x_2143_; size_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2136_ = lean_string_append(v___y_2134_, v___y_2135_);
lean_dec_ref(v___y_2135_);
v___x_2137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2138_ = lean_string_append(v___x_2136_, v___x_2137_);
v___x_2139_ = 1;
lean_inc(v_src_2129_);
v___x_2140_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2129_, v___x_2139_);
v___x_2141_ = lean_string_append(v___x_2138_, v___x_2140_);
lean_dec_ref(v___x_2140_);
v___x_2142_ = lean_string_append(v___x_2141_, v___y_2133_);
v___x_2143_ = ((size_t)1ULL);
v___x_2144_ = lean_usize_add(v_i_2124_, v___x_2143_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_2123_, v___x_2144_, v_stop_2125_, v___x_2142_);
return v___x_2145_;
}
v___jp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v_toString_2150_; 
v___x_2148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2149_ = lean_string_append(v_b_2126_, v___x_2148_);
v_toString_2150_ = lean_ctor_get(v_ver_2130_, 0);
lean_inc_ref(v_toString_2150_);
v___y_2133_ = v___y_2147_;
v___y_2134_ = v___x_2149_;
v___y_2135_ = v_toString_2150_;
goto v___jp_2132_;
}
}
else
{
return v_b_2126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v_as_2153_, lean_object* v_i_2154_, lean_object* v_stop_2155_, lean_object* v_b_2156_){
_start:
{
size_t v_i_boxed_2157_; size_t v_stop_boxed_2158_; lean_object* v_res_2159_; 
v_i_boxed_2157_ = lean_unbox_usize(v_i_2154_);
lean_dec(v_i_2154_);
v_stop_boxed_2158_ = lean_unbox_usize(v_stop_2155_);
lean_dec(v_stop_2155_);
v_res_2159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v_as_2153_, v_i_boxed_2157_, v_stop_boxed_2158_, v_b_2156_);
lean_dec_ref(v_as_2153_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_2160_, lean_object* v_as_2161_, size_t v_i_2162_, size_t v_stop_2163_, lean_object* v_b_2164_, lean_object* v___y_2165_){
_start:
{
uint8_t v___x_2167_; 
v___x_2167_ = lean_usize_dec_eq(v_i_2162_, v_stop_2163_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v_relPkgDir_2169_; lean_object* v_manifestEntry_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2168_ = lean_array_uget_borrowed(v_as_2161_, v_i_2162_);
v_relPkgDir_2169_ = lean_ctor_get(v___x_2168_, 1);
v_manifestEntry_2170_ = lean_ctor_get(v___x_2168_, 4);
lean_inc_ref(v_relPkgDir_2169_);
lean_inc_ref(v___x_2160_);
v___x_2171_ = l_Lake_joinRelative(v___x_2160_, v_relPkgDir_2169_);
v___x_2172_ = l_Lake_toolchainFileName;
v___x_2173_ = l_System_FilePath_join(v___x_2171_, v___x_2172_);
v___x_2174_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2173_);
lean_dec_ref(v___x_2173_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v_a_2177_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
if (lean_obj_tag(v_a_2175_) == 1)
{
lean_object* v_tc_x3f_2181_; 
v_tc_x3f_2181_ = lean_ctor_get(v_b_2164_, 1);
if (lean_obj_tag(v_tc_x3f_2181_) == 1)
{
lean_object* v_val_2182_; lean_object* v_src_2183_; lean_object* v_clashes_2184_; uint8_t v_fixed_2185_; lean_object* v_val_2186_; uint8_t v___x_2187_; 
v_val_2182_ = lean_ctor_get(v_a_2175_, 0);
v_src_2183_ = lean_ctor_get(v_b_2164_, 0);
v_clashes_2184_ = lean_ctor_get(v_b_2164_, 2);
v_fixed_2185_ = lean_ctor_get_uint8(v_b_2164_, sizeof(void*)*3);
v_val_2186_ = lean_ctor_get(v_tc_x3f_2181_, 0);
v___x_2187_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2168_);
if (v___x_2187_ == 0)
{
uint8_t v___x_2197_; 
v___x_2197_ = l_Lake_ToolchainVer_ble(v_val_2182_, v_val_2186_);
if (v___x_2197_ == 0)
{
lean_inc_ref(v_clashes_2184_);
lean_inc(v_src_2183_);
lean_inc_ref(v_tc_x3f_2181_);
lean_dec_ref(v_b_2164_);
if (v_fixed_2185_ == 0)
{
goto v___jp_2193_;
}
else
{
if (v___x_2187_ == 0)
{
lean_inc(v_val_2182_);
lean_dec_ref_known(v_a_2175_, 1);
goto v___jp_2188_;
}
else
{
goto v___jp_2193_;
}
}
}
else
{
lean_dec_ref_known(v_a_2175_, 1);
v_a_2177_ = v_b_2164_;
goto v___jp_2176_;
}
}
else
{
if (v_fixed_2185_ == 0)
{
lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2212_; 
lean_inc_ref(v_clashes_2184_);
lean_inc(v_src_2183_);
lean_inc_ref(v_tc_x3f_2181_);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_b_2164_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; 
v_unused_2213_ = lean_ctor_get(v_b_2164_, 2);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_b_2164_, 1);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_b_2164_, 0);
lean_dec(v_unused_2215_);
v___x_2199_ = v_b_2164_;
v_isShared_2200_ = v_isSharedCheck_2212_;
goto v_resetjp_2198_;
}
else
{
lean_dec(v_b_2164_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2212_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Lake_ToolchainVer_ble(v_val_2186_, v_val_2182_);
if (v___x_2201_ == 0)
{
lean_object* v_name_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
lean_inc(v_val_2182_);
lean_dec_ref_known(v_a_2175_, 1);
v_name_2202_ = lean_ctor_get(v_manifestEntry_2170_, 0);
lean_inc(v_name_2202_);
v___x_2203_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2203_, 0, v_name_2202_);
lean_ctor_set(v___x_2203_, 1, v_val_2182_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*2, v___x_2187_);
v___x_2204_ = lean_array_push(v_clashes_2184_, v___x_2203_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 2, v___x_2204_);
v___x_2206_ = v___x_2199_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_src_2183_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_tc_x3f_2181_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v___x_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2207_, sizeof(void*)*3, v_fixed_2185_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
v_a_2177_ = v___x_2206_;
goto v___jp_2176_;
}
}
else
{
lean_object* v_name_2208_; lean_object* v___x_2210_; 
lean_dec(v_src_2183_);
lean_dec_ref_known(v_tc_x3f_2181_, 1);
v_name_2208_ = lean_ctor_get(v_manifestEntry_2170_, 0);
lean_inc(v_name_2208_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 1, v_a_2175_);
lean_ctor_set(v___x_2199_, 0, v_name_2208_);
v___x_2210_ = v___x_2199_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_name_2208_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_a_2175_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_clashes_2184_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*3, v___x_2187_);
v_a_2177_ = v___x_2210_;
goto v___jp_2176_;
}
}
}
}
else
{
uint8_t v___x_2216_; 
lean_inc_n(v_val_2182_, 2);
lean_dec_ref_known(v_a_2175_, 1);
lean_inc(v_val_2186_);
v___x_2216_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2186_, v_val_2182_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2226_; 
lean_inc_ref(v_clashes_2184_);
lean_inc(v_src_2183_);
lean_inc_ref(v_tc_x3f_2181_);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_b_2164_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; lean_object* v_unused_2228_; lean_object* v_unused_2229_; 
v_unused_2227_ = lean_ctor_get(v_b_2164_, 2);
lean_dec(v_unused_2227_);
v_unused_2228_ = lean_ctor_get(v_b_2164_, 1);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_b_2164_, 0);
lean_dec(v_unused_2229_);
v___x_2218_ = v_b_2164_;
v_isShared_2219_ = v_isSharedCheck_2226_;
goto v_resetjp_2217_;
}
else
{
lean_dec(v_b_2164_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2226_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v_name_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v_name_2220_ = lean_ctor_get(v_manifestEntry_2170_, 0);
lean_inc(v_name_2220_);
v___x_2221_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2221_, 0, v_name_2220_);
lean_ctor_set(v___x_2221_, 1, v_val_2182_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*2, v___x_2187_);
v___x_2222_ = lean_array_push(v_clashes_2184_, v___x_2221_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 2, v___x_2222_);
v___x_2224_ = v___x_2218_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_src_2183_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_tc_x3f_2181_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v___x_2222_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*3, v_fixed_2185_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
v_a_2177_ = v___x_2224_;
goto v___jp_2176_;
}
}
}
else
{
lean_dec(v_val_2182_);
v_a_2177_ = v_b_2164_;
goto v___jp_2176_;
}
}
}
v___jp_2188_:
{
lean_object* v_name_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_name_2189_ = lean_ctor_get(v_manifestEntry_2170_, 0);
lean_inc(v_name_2189_);
v___x_2190_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2190_, 0, v_name_2189_);
lean_ctor_set(v___x_2190_, 1, v_val_2182_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*2, v___x_2187_);
v___x_2191_ = lean_array_push(v_clashes_2184_, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2192_, 0, v_src_2183_);
lean_ctor_set(v___x_2192_, 1, v_tc_x3f_2181_);
lean_ctor_set(v___x_2192_, 2, v___x_2191_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*3, v_fixed_2185_);
v_a_2177_ = v___x_2192_;
goto v___jp_2176_;
}
v___jp_2193_:
{
uint8_t v___x_2194_; 
v___x_2194_ = l_Lake_ToolchainVer_blt(v_val_2186_, v_val_2182_);
if (v___x_2194_ == 0)
{
lean_inc(v_val_2182_);
lean_dec_ref_known(v_a_2175_, 1);
goto v___jp_2188_;
}
else
{
lean_object* v_name_2195_; lean_object* v___x_2196_; 
lean_dec(v_src_2183_);
lean_dec_ref_known(v_tc_x3f_2181_, 1);
v_name_2195_ = lean_ctor_get(v_manifestEntry_2170_, 0);
lean_inc(v_name_2195_);
v___x_2196_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2196_, 0, v_name_2195_);
lean_ctor_set(v___x_2196_, 1, v_a_2175_);
lean_ctor_set(v___x_2196_, 2, v_clashes_2184_);
lean_ctor_set_uint8(v___x_2196_, sizeof(void*)*3, v___x_2187_);
v_a_2177_ = v___x_2196_;
goto v___jp_2176_;
}
}
}
else
{
lean_object* v_clashes_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2239_; 
v_clashes_2230_ = lean_ctor_get(v_b_2164_, 2);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_b_2164_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; lean_object* v_unused_2241_; 
v_unused_2240_ = lean_ctor_get(v_b_2164_, 1);
lean_dec(v_unused_2240_);
v_unused_2241_ = lean_ctor_get(v_b_2164_, 0);
lean_dec(v_unused_2241_);
v___x_2232_ = v_b_2164_;
v_isShared_2233_ = v_isSharedCheck_2239_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_clashes_2230_);
lean_dec(v_b_2164_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2239_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_name_2234_; uint8_t v___x_2235_; lean_object* v___x_2237_; 
v_name_2234_ = lean_ctor_get(v_manifestEntry_2170_, 0);
v___x_2235_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2168_);
lean_inc(v_name_2234_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v_a_2175_);
lean_ctor_set(v___x_2232_, 0, v_name_2234_);
v___x_2237_ = v___x_2232_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_name_2234_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_a_2175_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_clashes_2230_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_ctor_set_uint8(v___x_2237_, sizeof(void*)*3, v___x_2235_);
v_a_2177_ = v___x_2237_;
goto v___jp_2176_;
}
}
}
}
else
{
lean_dec(v_a_2175_);
v_a_2177_ = v_b_2164_;
goto v___jp_2176_;
}
v___jp_2176_:
{
size_t v___x_2178_; size_t v___x_2179_; 
v___x_2178_ = ((size_t)1ULL);
v___x_2179_ = lean_usize_add(v_i_2162_, v___x_2178_);
v_i_2162_ = v___x_2179_;
v_b_2164_ = v_a_2177_;
goto _start;
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v_b_2164_);
lean_dec_ref(v___x_2160_);
v_a_2242_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2244_ = v___x_2174_;
v_isShared_2245_ = v_isSharedCheck_2254_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2174_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2254_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2246_ = lean_io_error_to_string(v_a_2242_);
v___x_2247_ = 3;
v___x_2248_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set_uint8(v___x_2248_, sizeof(void*)*1, v___x_2247_);
lean_inc_ref(v___y_2165_);
v___x_2249_ = lean_apply_2(v___y_2165_, v___x_2248_, lean_box(0));
v___x_2250_ = lean_box(0);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2250_);
v___x_2252_ = v___x_2244_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v___x_2255_; 
lean_dec_ref(v___x_2160_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v_b_2164_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2256_, lean_object* v_as_2257_, lean_object* v_i_2258_, lean_object* v_stop_2259_, lean_object* v_b_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
size_t v_i_boxed_2263_; size_t v_stop_boxed_2264_; lean_object* v_res_2265_; 
v_i_boxed_2263_ = lean_unbox_usize(v_i_2258_);
lean_dec(v_i_2258_);
v_stop_boxed_2264_ = lean_unbox_usize(v_stop_2259_);
lean_dec(v_stop_2259_);
v_res_2265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2256_, v_as_2257_, v_i_boxed_2263_, v_stop_boxed_2264_, v_b_2260_, v___y_2261_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_as_2257_);
return v_res_2265_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2275_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v___x_2276_ = lean_unsigned_to_nat(4u);
v___x_2277_ = lean_mk_empty_array_with_capacity(v___x_2276_);
v___x_2278_ = lean_array_push(v___x_2277_, v___x_2275_);
return v___x_2278_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2280_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6);
v___x_2281_ = lean_array_push(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10(void){
_start:
{
uint32_t v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = 4;
v___x_2287_ = lean_uint32_to_uint8(v___x_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2305_, lean_object* v_rootDeps_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___y_2310_; lean_object* v_lakeEnv_2315_; lean_object* v_lakeArgs_x3f_2316_; lean_object* v_packages_2317_; lean_object* v___y_2319_; lean_object* v___y_2320_; uint8_t v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2464_; lean_object* v___y_2465_; uint8_t v___y_2466_; lean_object* v___x_2469_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; uint8_t v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2497_; uint8_t v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___x_2505_; lean_object* v_baseName_2506_; lean_object* v_dir_2507_; lean_object* v_config_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_lakeEnv_2315_ = lean_ctor_get(v_ws_2305_, 0);
lean_inc_ref(v_lakeEnv_2315_);
v_lakeArgs_x3f_2316_ = lean_ctor_get(v_ws_2305_, 3);
lean_inc(v_lakeArgs_x3f_2316_);
v_packages_2317_ = lean_ctor_get(v_ws_2305_, 4);
lean_inc_ref(v_packages_2317_);
lean_dec_ref(v_ws_2305_);
v___x_2469_ = lean_unsigned_to_nat(0u);
v___x_2505_ = lean_array_fget(v_packages_2317_, v___x_2469_);
lean_dec_ref(v_packages_2317_);
v_baseName_2506_ = lean_ctor_get(v___x_2505_, 1);
lean_inc(v_baseName_2506_);
v_dir_2507_ = lean_ctor_get(v___x_2505_, 4);
lean_inc_ref_n(v_dir_2507_, 2);
v_config_2508_ = lean_ctor_get(v___x_2505_, 6);
lean_inc_ref(v_config_2508_);
lean_dec(v___x_2505_);
v___x_2509_ = l_Lake_toolchainFileName;
v___x_2510_ = l_System_FilePath_join(v_dir_2507_, v___x_2509_);
v___x_2511_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2510_);
lean_dec_ref(v___x_2510_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2570_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2570_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2570_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v_src_2517_; lean_object* v_tc_x3f_2518_; lean_object* v_clashes_2519_; uint8_t v_fixed_2520_; lean_object* v___y_2544_; uint8_t v_fixedToolchain_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v_fixedToolchain_2558_ = lean_ctor_get_uint8(v_config_2508_, sizeof(void*)*27 + 6);
lean_dec_ref(v_config_2508_);
v___x_2559_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_2560_ = lean_array_get_size(v_rootDeps_2306_);
v___x_2561_ = lean_nat_dec_lt(v___x_2469_, v___x_2560_);
if (v___x_2561_ == 0)
{
lean_inc(v_a_2512_);
v_src_2517_ = v_baseName_2506_;
v_tc_x3f_2518_ = v_a_2512_;
v_clashes_2519_ = v___x_2559_;
v_fixed_2520_ = v_fixedToolchain_2558_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2562_; uint8_t v___x_2563_; 
lean_inc(v_a_2512_);
lean_inc(v_baseName_2506_);
v___x_2562_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2562_, 0, v_baseName_2506_);
lean_ctor_set(v___x_2562_, 1, v_a_2512_);
lean_ctor_set(v___x_2562_, 2, v___x_2559_);
lean_ctor_set_uint8(v___x_2562_, sizeof(void*)*3, v_fixedToolchain_2558_);
v___x_2563_ = lean_nat_dec_le(v___x_2560_, v___x_2560_);
if (v___x_2563_ == 0)
{
if (v___x_2561_ == 0)
{
lean_dec_ref_known(v___x_2562_, 3);
lean_inc(v_a_2512_);
v_src_2517_ = v_baseName_2506_;
v_tc_x3f_2518_ = v_a_2512_;
v_clashes_2519_ = v___x_2559_;
v_fixed_2520_ = v_fixedToolchain_2558_;
goto v___jp_2516_;
}
else
{
size_t v___x_2564_; size_t v___x_2565_; lean_object* v___x_2566_; 
lean_dec(v_baseName_2506_);
v___x_2564_ = ((size_t)0ULL);
v___x_2565_ = lean_usize_of_nat(v___x_2560_);
lean_inc_ref(v_dir_2507_);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2507_, v_rootDeps_2306_, v___x_2564_, v___x_2565_, v___x_2562_, v_a_2307_);
v___y_2544_ = v___x_2566_;
goto v___jp_2543_;
}
}
else
{
size_t v___x_2567_; size_t v___x_2568_; lean_object* v___x_2569_; 
lean_dec(v_baseName_2506_);
v___x_2567_ = ((size_t)0ULL);
v___x_2568_ = lean_usize_of_nat(v___x_2560_);
lean_inc_ref(v_dir_2507_);
v___x_2569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2507_, v_rootDeps_2306_, v___x_2567_, v___x_2568_, v___x_2562_, v_a_2307_);
v___y_2544_ = v___x_2569_;
goto v___jp_2543_;
}
}
v___jp_2516_:
{
lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = lean_array_get_size(v_clashes_2519_);
v___x_2522_ = lean_nat_dec_lt(v___x_2469_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_dec_ref(v_clashes_2519_);
lean_dec(v_src_2517_);
if (lean_obj_tag(v_tc_x3f_2518_) == 1)
{
lean_object* v_val_2523_; lean_object* v_rootToolchainFile_2524_; 
v_val_2523_ = lean_ctor_get(v_tc_x3f_2518_, 0);
lean_inc(v_val_2523_);
lean_dec_ref_known(v_tc_x3f_2518_, 1);
v_rootToolchainFile_2524_ = l_Lake_joinRelative(v_dir_2507_, v___x_2509_);
if (lean_obj_tag(v_a_2512_) == 0)
{
lean_del_object(v___x_2514_);
v___y_2464_ = v_rootToolchainFile_2524_;
v___y_2465_ = v_val_2523_;
v___y_2466_ = v___x_2522_;
goto v___jp_2463_;
}
else
{
lean_object* v_val_2525_; uint8_t v___x_2526_; 
v_val_2525_ = lean_ctor_get(v_a_2512_, 0);
lean_inc(v_val_2525_);
lean_dec_ref_known(v_a_2512_, 1);
lean_inc(v_val_2523_);
v___x_2526_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2525_, v_val_2523_);
if (v___x_2526_ == 0)
{
lean_del_object(v___x_2514_);
v___y_2464_ = v_rootToolchainFile_2524_;
v___y_2465_ = v_val_2523_;
v___y_2466_ = v___x_2526_;
goto v___jp_2463_;
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
lean_dec_ref(v_rootToolchainFile_2524_);
lean_dec(v_val_2523_);
lean_dec(v_lakeArgs_x3f_2316_);
lean_dec_ref(v_lakeEnv_2315_);
v___x_2527_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2307_);
v___x_2528_ = lean_apply_2(v_a_2307_, v___x_2527_, lean_box(0));
v___x_2529_ = lean_box(0);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2529_);
v___x_2531_ = v___x_2514_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
lean_dec(v_tc_x3f_2518_);
lean_dec(v_a_2512_);
lean_dec_ref(v_dir_2507_);
lean_dec(v_lakeArgs_x3f_2316_);
lean_dec_ref(v_lakeEnv_2315_);
v___x_2533_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2307_);
v___x_2534_ = lean_apply_2(v_a_2307_, v___x_2533_, lean_box(0));
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2534_);
v___x_2536_ = v___x_2514_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
else
{
lean_del_object(v___x_2514_);
lean_dec(v_a_2512_);
lean_dec_ref(v_dir_2507_);
lean_dec(v_lakeArgs_x3f_2316_);
lean_dec_ref(v_lakeEnv_2315_);
if (lean_obj_tag(v_tc_x3f_2518_) == 1)
{
if (v_fixed_2520_ == 0)
{
lean_object* v_val_2538_; lean_object* v___x_2539_; 
v_val_2538_ = lean_ctor_get(v_tc_x3f_2518_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v_tc_x3f_2518_, 1);
v___x_2539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2497_ = v_val_2538_;
v___y_2498_ = v___x_2522_;
v___y_2499_ = v___x_2521_;
v___y_2500_ = v_src_2517_;
v___y_2501_ = v_clashes_2519_;
v___y_2502_ = v___x_2539_;
goto v___jp_2496_;
}
else
{
lean_object* v_val_2540_; lean_object* v___x_2541_; 
v_val_2540_ = lean_ctor_get(v_tc_x3f_2518_, 0);
lean_inc(v_val_2540_);
lean_dec_ref_known(v_tc_x3f_2518_, 1);
v___x_2541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2497_ = v_val_2540_;
v___y_2498_ = v___x_2522_;
v___y_2499_ = v___x_2521_;
v___y_2500_ = v_src_2517_;
v___y_2501_ = v_clashes_2519_;
v___y_2502_ = v___x_2541_;
goto v___jp_2496_;
}
}
else
{
lean_object* v___x_2542_; 
lean_dec(v_tc_x3f_2518_);
lean_dec(v_src_2517_);
v___x_2542_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_2471_ = v___x_2521_;
v___y_2472_ = v_clashes_2519_;
v___y_2473_ = v___x_2542_;
goto v___jp_2470_;
}
}
}
v___jp_2543_:
{
if (lean_obj_tag(v___y_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v_src_2546_; lean_object* v_tc_x3f_2547_; lean_object* v_clashes_2548_; uint8_t v_fixed_2549_; 
v_a_2545_ = lean_ctor_get(v___y_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___y_2544_, 1);
v_src_2546_ = lean_ctor_get(v_a_2545_, 0);
lean_inc(v_src_2546_);
v_tc_x3f_2547_ = lean_ctor_get(v_a_2545_, 1);
lean_inc(v_tc_x3f_2547_);
v_clashes_2548_ = lean_ctor_get(v_a_2545_, 2);
lean_inc_ref(v_clashes_2548_);
v_fixed_2549_ = lean_ctor_get_uint8(v_a_2545_, sizeof(void*)*3);
lean_dec(v_a_2545_);
v_src_2517_ = v_src_2546_;
v_tc_x3f_2518_ = v_tc_x3f_2547_;
v_clashes_2519_ = v_clashes_2548_;
v_fixed_2520_ = v_fixed_2549_;
goto v___jp_2516_;
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_del_object(v___x_2514_);
lean_dec(v_a_2512_);
lean_dec_ref(v_dir_2507_);
lean_dec(v_lakeArgs_x3f_2316_);
lean_dec_ref(v_lakeEnv_2315_);
v_a_2550_ = lean_ctor_get(v___y_2544_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___y_2544_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___y_2544_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___y_2544_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2583_; 
lean_dec_ref(v_config_2508_);
lean_dec_ref(v_dir_2507_);
lean_dec(v_baseName_2506_);
lean_dec(v_lakeArgs_x3f_2316_);
lean_dec_ref(v_lakeEnv_2315_);
v_a_2571_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2573_ = v___x_2511_;
v_isShared_2574_ = v_isSharedCheck_2583_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2511_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2583_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; uint8_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2575_ = lean_io_error_to_string(v_a_2571_);
v___x_2576_ = 3;
v___x_2577_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*1, v___x_2576_);
lean_inc_ref(v_a_2307_);
v___x_2578_ = lean_apply_2(v_a_2307_, v___x_2577_, lean_box(0));
v___x_2579_ = lean_box(0);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2579_);
v___x_2581_ = v___x_2573_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
v___jp_2309_:
{
uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2311_ = 2;
v___x_2312_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2312_, 0, v___y_2310_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*1, v___x_2311_);
lean_inc_ref(v_a_2307_);
v___x_2313_ = lean_apply_2(v_a_2307_, v___x_2312_, lean_box(0));
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
return v___x_2314_;
}
v___jp_2318_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_inc_ref(v___y_2320_);
v___x_2323_ = lean_string_append(v___y_2320_, v___y_2322_);
v___x_2324_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2325_ = lean_string_append(v___x_2323_, v___x_2324_);
v___x_2326_ = 1;
v___x_2327_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*1, v___x_2326_);
lean_inc_ref(v_a_2307_);
v___x_2328_ = lean_apply_2(v_a_2307_, v___x_2327_, lean_box(0));
v___x_2329_ = l_IO_FS_writeFile(v___y_2319_, v___y_2322_);
lean_dec_ref(v___y_2319_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_dec_ref_known(v___x_2329_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2316_) == 1)
{
lean_object* v_elan_x3f_2330_; 
v_elan_x3f_2330_ = lean_ctor_get(v_lakeEnv_2315_, 2);
if (lean_obj_tag(v_elan_x3f_2330_) == 1)
{
lean_object* v_val_2331_; lean_object* v_val_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v_elan_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v_val_2331_ = lean_ctor_get(v_lakeArgs_x3f_2316_, 0);
lean_inc(v_val_2331_);
lean_dec_ref_known(v_lakeArgs_x3f_2316_, 1);
v_val_2332_ = lean_ctor_get(v_elan_x3f_2330_, 0);
v___x_2333_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2307_);
v___x_2334_ = lean_apply_2(v_a_2307_, v___x_2333_, lean_box(0));
v___x_2335_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_2336_ = lean_ctor_get(v_val_2332_, 1);
lean_inc_ref(v_elan_2336_);
v___x_2337_ = 1;
v___x_2338_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2339_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2340_ = lean_array_push(v___x_2339_, v___y_2322_);
v___x_2341_ = lean_array_push(v___x_2340_, v___x_2338_);
v___x_2342_ = l_Array_append___redArg(v___x_2341_, v_val_2331_);
lean_dec(v_val_2331_);
v___x_2343_ = lean_box(0);
v___x_2344_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2315_);
v___x_2345_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2345_, 0, v___x_2335_);
lean_ctor_set(v___x_2345_, 1, v_elan_2336_);
lean_ctor_set(v___x_2345_, 2, v___x_2342_);
lean_ctor_set(v___x_2345_, 3, v___x_2343_);
lean_ctor_set(v___x_2345_, 4, v___x_2344_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*5, v___x_2337_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*5 + 1, v___y_2321_);
v___x_2346_ = lean_io_process_spawn(v___x_2345_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2348_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v___x_2348_ = lean_io_process_child_wait(v___x_2335_, v_a_2347_);
lean_dec(v_a_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; uint32_t v___x_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = lean_unbox_uint32(v_a_2349_);
lean_dec(v_a_2349_);
v___x_2351_ = lean_uint32_to_uint8(v___x_2350_);
v___x_2352_ = lean_io_exit(v___x_2351_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2373_; 
v_a_2361_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2363_ = v___x_2352_;
v_isShared_2364_ = v_isSharedCheck_2373_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2352_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2373_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2365_ = lean_io_error_to_string(v_a_2361_);
v___x_2366_ = 3;
v___x_2367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*1, v___x_2366_);
lean_inc_ref(v_a_2307_);
v___x_2368_ = lean_apply_2(v_a_2307_, v___x_2367_, lean_box(0));
v___x_2369_ = lean_box(0);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2369_);
v___x_2371_ = v___x_2363_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2386_; 
v_a_2374_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2376_ = v___x_2348_;
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2348_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; uint8_t v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2378_ = lean_io_error_to_string(v_a_2374_);
v___x_2379_ = 3;
v___x_2380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*1, v___x_2379_);
lean_inc_ref(v_a_2307_);
v___x_2381_ = lean_apply_2(v_a_2307_, v___x_2380_, lean_box(0));
v___x_2382_ = lean_box(0);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2382_);
v___x_2384_ = v___x_2376_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2399_; 
v_a_2387_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2389_ = v___x_2346_;
v_isShared_2390_ = v_isSharedCheck_2399_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2346_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2399_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2391_ = lean_io_error_to_string(v_a_2387_);
v___x_2392_ = 3;
v___x_2393_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set_uint8(v___x_2393_, sizeof(void*)*1, v___x_2392_);
lean_inc_ref(v_a_2307_);
v___x_2394_ = lean_apply_2(v_a_2307_, v___x_2393_, lean_box(0));
v___x_2395_ = lean_box(0);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2395_);
v___x_2397_ = v___x_2389_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; 
lean_dec_ref_known(v_lakeArgs_x3f_2316_, 1);
lean_dec_ref(v___y_2322_);
lean_dec_ref(v_lakeEnv_2315_);
v___x_2400_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2307_);
v___x_2401_ = lean_apply_2(v_a_2307_, v___x_2400_, lean_box(0));
v___x_2402_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2403_ = lean_io_exit(v___x_2402_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2424_; 
v_a_2412_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2414_ = v___x_2403_;
v_isShared_2415_ = v_isSharedCheck_2424_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2403_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2424_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2416_ = lean_io_error_to_string(v_a_2412_);
v___x_2417_ = 3;
v___x_2418_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*1, v___x_2417_);
lean_inc_ref(v_a_2307_);
v___x_2419_ = lean_apply_2(v_a_2307_, v___x_2418_, lean_box(0));
v___x_2420_ = lean_box(0);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2420_);
v___x_2422_ = v___x_2414_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; 
lean_dec_ref(v___y_2322_);
lean_dec(v_lakeArgs_x3f_2316_);
lean_dec_ref(v_lakeEnv_2315_);
v___x_2425_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2307_);
v___x_2426_ = lean_apply_2(v_a_2307_, v___x_2425_, lean_box(0));
v___x_2427_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2428_ = lean_io_exit(v___x_2427_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2449_; 
v_a_2437_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2439_ = v___x_2428_;
v_isShared_2440_ = v_isSharedCheck_2449_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2428_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2449_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2441_ = lean_io_error_to_string(v_a_2437_);
v___x_2442_ = 3;
v___x_2443_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set_uint8(v___x_2443_, sizeof(void*)*1, v___x_2442_);
lean_inc_ref(v_a_2307_);
v___x_2444_ = lean_apply_2(v_a_2307_, v___x_2443_, lean_box(0));
v___x_2445_ = lean_box(0);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2445_);
v___x_2447_ = v___x_2439_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2462_; 
lean_dec_ref(v___y_2322_);
lean_dec(v_lakeArgs_x3f_2316_);
lean_dec_ref(v_lakeEnv_2315_);
v_a_2450_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2452_ = v___x_2329_;
v_isShared_2453_ = v_isSharedCheck_2462_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2329_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2462_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2460_; 
v___x_2454_ = lean_io_error_to_string(v_a_2450_);
v___x_2455_ = 3;
v___x_2456_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set_uint8(v___x_2456_, sizeof(void*)*1, v___x_2455_);
lean_inc_ref(v_a_2307_);
v___x_2457_ = lean_apply_2(v_a_2307_, v___x_2456_, lean_box(0));
v___x_2458_ = lean_box(0);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2458_);
v___x_2460_ = v___x_2452_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
v___jp_2463_:
{
lean_object* v___x_2467_; lean_object* v_toString_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2468_ = lean_ctor_get(v___y_2465_, 0);
lean_inc_ref(v_toString_2468_);
lean_dec_ref(v___y_2465_);
v___y_2319_ = v___y_2464_;
v___y_2320_ = v___x_2467_;
v___y_2321_ = v___y_2466_;
v___y_2322_ = v_toString_2468_;
goto v___jp_2318_;
}
v___jp_2470_:
{
uint8_t v___x_2474_; 
v___x_2474_ = lean_nat_dec_lt(v___x_2469_, v___y_2471_);
if (v___x_2474_ == 0)
{
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
v___y_2310_ = v___y_2473_;
goto v___jp_2309_;
}
else
{
uint8_t v___x_2475_; 
v___x_2475_ = lean_nat_dec_le(v___y_2471_, v___y_2471_);
if (v___x_2475_ == 0)
{
if (v___x_2474_ == 0)
{
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
v___y_2310_ = v___y_2473_;
goto v___jp_2309_;
}
else
{
size_t v___x_2476_; size_t v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = ((size_t)0ULL);
v___x_2477_ = lean_usize_of_nat(v___y_2471_);
lean_dec(v___y_2471_);
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2472_, v___x_2476_, v___x_2477_, v___y_2473_);
lean_dec_ref(v___y_2472_);
v___y_2310_ = v___x_2478_;
goto v___jp_2309_;
}
}
else
{
size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = ((size_t)0ULL);
v___x_2480_ = lean_usize_of_nat(v___y_2471_);
lean_dec(v___y_2471_);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2472_, v___x_2479_, v___x_2480_, v___y_2473_);
lean_dec_ref(v___y_2472_);
v___y_2310_ = v___x_2481_;
goto v___jp_2309_;
}
}
}
v___jp_2482_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_inc_ref(v___y_2484_);
v___x_2490_ = lean_string_append(v___y_2484_, v___y_2489_);
lean_dec_ref(v___y_2489_);
v___x_2491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2492_ = lean_string_append(v___x_2490_, v___x_2491_);
v___x_2493_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2486_, v___y_2483_);
v___x_2494_ = lean_string_append(v___x_2492_, v___x_2493_);
lean_dec_ref(v___x_2493_);
v___x_2495_ = lean_string_append(v___x_2494_, v___y_2488_);
v___y_2471_ = v___y_2485_;
v___y_2472_ = v___y_2487_;
v___y_2473_ = v___x_2495_;
goto v___jp_2470_;
}
v___jp_2496_:
{
lean_object* v___x_2503_; lean_object* v_toString_2504_; 
v___x_2503_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_2504_ = lean_ctor_get(v___y_2497_, 0);
lean_inc_ref(v_toString_2504_);
lean_dec_ref(v___y_2497_);
v___y_2483_ = v___y_2498_;
v___y_2484_ = v___x_2503_;
v___y_2485_ = v___y_2499_;
v___y_2486_ = v___y_2500_;
v___y_2487_ = v___y_2501_;
v___y_2488_ = v___y_2502_;
v___y_2489_ = v_toString_2504_;
goto v___jp_2482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2584_, lean_object* v_rootDeps_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2584_, v_rootDeps_2585_, v_a_2586_);
lean_dec_ref(v_a_2586_);
lean_dec_ref(v_rootDeps_2585_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2589_, lean_object* v_dep_2590_, lean_object* v_ws_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2591_, v_pkg_2589_, v_dep_2590_, v_a_2592_, v_a_2593_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v_fst_2597_; lean_object* v_snd_2598_; lean_object* v___x_2599_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v_fst_2597_ = lean_ctor_get(v_a_2596_, 0);
lean_inc_n(v_fst_2597_, 2);
v_snd_2598_ = lean_ctor_get(v_a_2596_, 1);
lean_inc(v_snd_2598_);
lean_dec(v_a_2596_);
v___x_2599_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2597_, v_snd_2598_, v_a_2593_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2616_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2616_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2616_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v_snd_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2614_; 
v_snd_2604_ = lean_ctor_get(v_a_2600_, 1);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_a_2600_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v_a_2600_, 0);
lean_dec(v_unused_2615_);
v___x_2606_ = v_a_2600_;
v_isShared_2607_ = v_isSharedCheck_2614_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_snd_2604_);
lean_dec(v_a_2600_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2614_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v_fst_2597_);
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_fst_2597_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_snd_2604_);
v___x_2609_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2611_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2609_);
v___x_2611_ = v___x_2602_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v_fst_2597_);
v_a_2617_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2599_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2599_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2625_, lean_object* v_dep_2626_, lean_object* v_ws_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2625_, v_dep_2626_, v_ws_2627_, v_a_2628_, v_a_2629_);
lean_dec_ref(v_a_2629_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2632_, lean_object* v_ws_2633_, lean_object* v_pkg_2634_, lean_object* v_dep_2635_, lean_object* v_a_2636_){
_start:
{
uint8_t v___y_2639_; lean_object* v___y_2640_; lean_object* v_name_2670_; lean_object* v___x_2671_; 
v_name_2670_ = lean_ctor_get(v_dep_2635_, 0);
v___x_2671_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2636_, v_name_2670_);
if (lean_obj_tag(v___x_2671_) == 1)
{
lean_object* v_val_2672_; lean_object* v_lakeEnv_2673_; lean_object* v_packages_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v_config_2677_; lean_object* v_dir_2678_; lean_object* v_toWorkspaceConfig_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_dec_ref(v_dep_2635_);
lean_dec_ref(v_pkg_2634_);
v_val_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_val_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v_lakeEnv_2673_ = lean_ctor_get(v_ws_2633_, 0);
lean_inc_ref(v_lakeEnv_2673_);
v_packages_2674_ = lean_ctor_get(v_ws_2633_, 4);
lean_inc_ref(v_packages_2674_);
lean_dec_ref(v_ws_2633_);
v___x_2675_ = lean_unsigned_to_nat(0u);
v___x_2676_ = lean_array_fget(v_packages_2674_, v___x_2675_);
lean_dec_ref(v_packages_2674_);
v_config_2677_ = lean_ctor_get(v___x_2676_, 6);
lean_inc_ref(v_config_2677_);
v_dir_2678_ = lean_ctor_get(v___x_2676_, 4);
lean_inc_ref(v_dir_2678_);
lean_dec(v___x_2676_);
v_toWorkspaceConfig_2679_ = lean_ctor_get(v_config_2677_, 0);
lean_inc_ref(v_toWorkspaceConfig_2679_);
lean_dec_ref(v_config_2677_);
v___x_2680_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2679_);
v___x_2681_ = l_Lake_PackageEntry_materialize(v_val_2672_, v_lakeEnv_2673_, v_dir_2678_, v___x_2680_, v___y_2632_);
lean_dec_ref(v_lakeEnv_2673_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2690_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2684_ = v___x_2681_;
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v_a_2682_);
lean_ctor_set(v___x_2686_, 1, v_a_2636_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 0, v___x_2686_);
v___x_2688_ = v___x_2684_;
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
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_a_2636_);
v_a_2691_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2681_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2681_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
else
{
lean_object* v_wsIdx_2699_; lean_object* v_relDir_2700_; uint8_t v___y_2702_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
lean_dec(v___x_2671_);
v_wsIdx_2699_ = lean_ctor_get(v_pkg_2634_, 0);
lean_inc(v_wsIdx_2699_);
v_relDir_2700_ = lean_ctor_get(v_pkg_2634_, 5);
lean_inc_ref(v_relDir_2700_);
lean_dec_ref(v_pkg_2634_);
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = lean_nat_dec_eq(v_wsIdx_2699_, v___x_2706_);
lean_dec(v_wsIdx_2699_);
if (v___x_2707_ == 0)
{
uint8_t v___x_2708_; 
v___x_2708_ = 1;
v___y_2702_ = v___x_2708_;
goto v___jp_2701_;
}
else
{
uint8_t v___x_2709_; 
v___x_2709_ = 0;
v___y_2702_ = v___x_2709_;
goto v___jp_2701_;
}
v___jp_2701_:
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2704_ = lean_string_dec_eq(v_relDir_2700_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lake_joinRelative(v_relDir_2700_, v___x_2703_);
v___y_2639_ = v___y_2702_;
v___y_2640_ = v___x_2705_;
goto v___jp_2638_;
}
else
{
v___y_2639_ = v___y_2702_;
v___y_2640_ = v_relDir_2700_;
goto v___jp_2638_;
}
}
}
v___jp_2638_:
{
lean_object* v_lakeEnv_2641_; lean_object* v_packages_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v_config_2645_; lean_object* v_dir_2646_; lean_object* v_toWorkspaceConfig_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_lakeEnv_2641_ = lean_ctor_get(v_ws_2633_, 0);
lean_inc_ref(v_lakeEnv_2641_);
v_packages_2642_ = lean_ctor_get(v_ws_2633_, 4);
lean_inc_ref(v_packages_2642_);
lean_dec_ref(v_ws_2633_);
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_array_fget(v_packages_2642_, v___x_2643_);
lean_dec_ref(v_packages_2642_);
v_config_2645_ = lean_ctor_get(v___x_2644_, 6);
lean_inc_ref(v_config_2645_);
v_dir_2646_ = lean_ctor_get(v___x_2644_, 4);
lean_inc_ref(v_dir_2646_);
lean_dec(v___x_2644_);
v_toWorkspaceConfig_2647_ = lean_ctor_get(v_config_2645_, 0);
lean_inc_ref(v_toWorkspaceConfig_2647_);
lean_dec_ref(v_config_2645_);
v___x_2648_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2647_);
v___x_2649_ = l_Lake_Dependency_materialize(v_dep_2635_, v___y_2639_, v_lakeEnv_2641_, v_dir_2646_, v___x_2648_, v___y_2640_, v___y_2632_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2661_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2661_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2661_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v_manifestEntry_2654_; lean_object* v_name_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2659_; 
v_manifestEntry_2654_ = lean_ctor_get(v_a_2650_, 4);
v_name_2655_ = lean_ctor_get(v_manifestEntry_2654_, 0);
lean_inc_ref(v_manifestEntry_2654_);
lean_inc(v_name_2655_);
v___x_2656_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2655_, v_manifestEntry_2654_, v_a_2636_);
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v_a_2650_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2657_);
v___x_2659_ = v___x_2652_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_a_2636_);
v_a_2662_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2649_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2649_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2710_, lean_object* v_ws_2711_, lean_object* v_pkg_2712_, lean_object* v_dep_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2710_, v_ws_2711_, v_pkg_2712_, v_dep_2713_, v_a_2714_);
lean_dec_ref(v___y_2710_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2717_, lean_object* v_dep_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_manifestEntry_2721_; lean_object* v_pkgDir_2722_; lean_object* v_name_2723_; lean_object* v_manifestFile_x3f_2724_; lean_object* v___y_2726_; lean_object* v_fst_2727_; lean_object* v_snd_2728_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v_val_2788_; lean_object* v___y_2816_; 
v_manifestEntry_2721_ = lean_ctor_get(v_dep_2718_, 4);
v_pkgDir_2722_ = lean_ctor_get(v_dep_2718_, 0);
v_name_2723_ = lean_ctor_get(v_manifestEntry_2721_, 0);
v_manifestFile_x3f_2724_ = lean_ctor_get(v_manifestEntry_2721_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2724_) == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2722_);
v___x_2837_ = l_Lake_joinRelative(v_pkgDir_2722_, v___x_2836_);
v___y_2816_ = v___x_2837_;
goto v___jp_2815_;
}
else
{
lean_object* v_val_2838_; lean_object* v___x_2839_; 
v_val_2838_ = lean_ctor_get(v_manifestFile_x3f_2724_, 0);
lean_inc(v_val_2838_);
lean_inc_ref(v_pkgDir_2722_);
v___x_2839_ = l_Lake_joinRelative(v_pkgDir_2722_, v_val_2838_);
v___y_2816_ = v___x_2839_;
goto v___jp_2815_;
}
v___jp_2725_:
{
if (lean_obj_tag(v_fst_2727_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2758_; 
lean_inc(v_name_2723_);
lean_dec_ref(v_dep_2718_);
v_a_2729_ = lean_ctor_get(v_fst_2727_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_fst_2727_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2731_ = v_fst_2727_;
v_isShared_2732_ = v_isSharedCheck_2758_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v_fst_2727_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2758_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
if (lean_obj_tag(v_a_2729_) == 11)
{
uint8_t v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_dec_ref_known(v_a_2729_, 2);
v___x_2733_ = 0;
v___x_2734_ = l_Lean_Name_toString(v_name_2723_, v___x_2733_);
v___x_2735_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2736_ = lean_string_append(v___x_2734_, v___x_2735_);
v___x_2737_ = lean_string_append(v___x_2736_, v___y_2726_);
lean_dec_ref(v___y_2726_);
v___x_2738_ = 2;
v___x_2739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2739_, 0, v___x_2737_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*1, v___x_2738_);
v___x_2740_ = lean_apply_2(v___y_2717_, v___x_2739_, lean_box(0));
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v_snd_2728_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v___x_2741_);
v___x_2743_ = v___x_2731_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
else
{
uint8_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
lean_dec_ref(v___y_2726_);
v___x_2745_ = 0;
v___x_2746_ = l_Lean_Name_toString(v_name_2723_, v___x_2745_);
v___x_2747_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2748_ = lean_string_append(v___x_2746_, v___x_2747_);
v___x_2749_ = lean_io_error_to_string(v_a_2729_);
v___x_2750_ = lean_string_append(v___x_2748_, v___x_2749_);
lean_dec_ref(v___x_2749_);
v___x_2751_ = 2;
v___x_2752_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set_uint8(v___x_2752_, sizeof(void*)*1, v___x_2751_);
v___x_2753_ = lean_apply_2(v___y_2717_, v___x_2752_, lean_box(0));
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v_snd_2728_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v___x_2754_);
v___x_2756_ = v___x_2731_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v___y_2726_);
lean_dec_ref(v___y_2717_);
v_a_2759_ = lean_ctor_get(v_fst_2727_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_fst_2727_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2761_ = v_fst_2727_;
v_isShared_2762_ = v_isSharedCheck_2783_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v_fst_2727_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2783_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v_packages_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_packages_2763_ = lean_ctor_get(v_a_2759_, 3);
lean_inc_ref(v_packages_2763_);
lean_dec(v_a_2759_);
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = lean_array_get_size(v_packages_2763_);
v___x_2766_ = lean_box(0);
v___x_2767_ = lean_nat_dec_lt(v___x_2764_, v___x_2765_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2770_; 
lean_dec_ref(v_packages_2763_);
lean_dec_ref(v_dep_2718_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v_snd_2728_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set_tag(v___x_2761_, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2768_);
v___x_2770_ = v___x_2761_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
else
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_nat_dec_le(v___x_2765_, v___x_2765_);
if (v___x_2772_ == 0)
{
if (v___x_2767_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_dec_ref(v_packages_2763_);
lean_dec_ref(v_dep_2718_);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2766_);
lean_ctor_set(v___x_2773_, 1, v_snd_2728_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set_tag(v___x_2761_, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2773_);
v___x_2775_ = v___x_2761_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
else
{
size_t v___x_2777_; size_t v___x_2778_; lean_object* v___x_2779_; 
lean_del_object(v___x_2761_);
v___x_2777_ = ((size_t)0ULL);
v___x_2778_ = lean_usize_of_nat(v___x_2765_);
v___x_2779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2718_, v_packages_2763_, v___x_2777_, v___x_2778_, v___x_2766_, v_snd_2728_);
lean_dec_ref(v_packages_2763_);
return v___x_2779_;
}
}
else
{
size_t v___x_2780_; size_t v___x_2781_; lean_object* v___x_2782_; 
lean_del_object(v___x_2761_);
v___x_2780_ = ((size_t)0ULL);
v___x_2781_ = lean_usize_of_nat(v___x_2765_);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2718_, v_packages_2763_, v___x_2780_, v___x_2781_, v___x_2766_, v_snd_2728_);
lean_dec_ref(v_packages_2763_);
return v___x_2782_;
}
}
}
}
}
v___jp_2784_:
{
lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2789_ = lean_array_get_size(v___y_2786_);
v___x_2790_ = lean_nat_dec_lt(v___y_2787_, v___x_2789_);
if (v___x_2790_ == 0)
{
v___y_2726_ = v___y_2785_;
v_fst_2727_ = v_val_2788_;
v_snd_2728_ = v_a_2719_;
goto v___jp_2725_;
}
else
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2791_ = lean_box(0);
v___x_2792_ = lean_nat_dec_le(v___x_2789_, v___x_2789_);
if (v___x_2792_ == 0)
{
if (v___x_2790_ == 0)
{
v___y_2726_ = v___y_2785_;
v_fst_2727_ = v_val_2788_;
v_snd_2728_ = v_a_2719_;
goto v___jp_2725_;
}
else
{
size_t v___x_2793_; size_t v___x_2794_; lean_object* v___x_2795_; 
v___x_2793_ = ((size_t)0ULL);
v___x_2794_ = lean_usize_of_nat(v___x_2789_);
v___x_2795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2786_, v___x_2793_, v___x_2794_, v___x_2791_, v___y_2717_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_dec_ref_known(v___x_2795_, 1);
v___y_2726_ = v___y_2785_;
v_fst_2727_ = v_val_2788_;
v_snd_2728_ = v_a_2719_;
goto v___jp_2725_;
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_val_2788_);
lean_dec_ref(v___y_2785_);
lean_dec(v_a_2719_);
lean_dec_ref(v_dep_2718_);
lean_dec_ref(v___y_2717_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
else
{
size_t v___x_2804_; size_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = lean_usize_of_nat(v___x_2789_);
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2786_, v___x_2804_, v___x_2805_, v___x_2791_, v___y_2717_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_dec_ref_known(v___x_2806_, 1);
v___y_2726_ = v___y_2785_;
v_fst_2727_ = v_val_2788_;
v_snd_2728_ = v_a_2719_;
goto v___jp_2725_;
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec_ref(v_val_2788_);
lean_dec_ref(v___y_2785_);
lean_dec(v_a_2719_);
lean_dec_ref(v_dep_2718_);
lean_dec_ref(v___y_2717_);
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
}
v___jp_2815_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2817_ = lean_unsigned_to_nat(0u);
v___x_2818_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2816_);
v___x_2819_ = l_Lake_Manifest_load(v___y_2816_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set_tag(v___x_2822_, 1);
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
v___y_2785_ = v___y_2816_;
v___y_2786_ = v___x_2818_;
v___y_2787_ = v___x_2817_;
v_val_2788_ = v___x_2825_;
goto v___jp_2784_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
v_a_2828_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2819_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2819_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set_tag(v___x_2830_, 0);
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
v___y_2785_ = v___y_2816_;
v___y_2786_ = v___x_2818_;
v___y_2787_ = v___x_2817_;
v_val_2788_ = v___x_2833_;
goto v___jp_2784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2840_, lean_object* v_dep_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2840_, v_dep_2841_, v_a_2842_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2849_, v___y_2847_, v___y_2845_, v___y_2846_, v___y_2848_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v_fst_2853_; lean_object* v_snd_2854_; lean_object* v___x_2855_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v___x_2851_, 1);
v_fst_2853_ = lean_ctor_get(v_a_2852_, 0);
lean_inc_n(v_fst_2853_, 2);
v_snd_2854_ = lean_ctor_get(v_a_2852_, 1);
lean_inc(v_snd_2854_);
lean_dec(v_a_2852_);
v___x_2855_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2849_, v_fst_2853_, v_snd_2854_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2872_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2858_ = v___x_2855_;
v_isShared_2859_ = v_isSharedCheck_2872_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2872_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v_snd_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2870_; 
v_snd_2860_ = lean_ctor_get(v_a_2856_, 1);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_a_2856_);
if (v_isSharedCheck_2870_ == 0)
{
lean_object* v_unused_2871_; 
v_unused_2871_ = lean_ctor_get(v_a_2856_, 0);
lean_dec(v_unused_2871_);
v___x_2862_ = v_a_2856_;
v_isShared_2863_ = v_isSharedCheck_2870_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_snd_2860_);
lean_dec(v_a_2856_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2870_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v_fst_2853_);
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_fst_2853_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_snd_2860_);
v___x_2865_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2867_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2865_);
v___x_2867_ = v___x_2858_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec(v_fst_2853_);
v_a_2873_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2855_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2855_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_dec_ref(v___y_2849_);
return v___x_2851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2888_, lean_object* v_ws_2889_, lean_object* v_toUpdate_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___y_2894_; lean_object* v___y_2899_; lean_object* v_fst_2900_; lean_object* v_snd_2901_; lean_object* v_packages_2920_; lean_object* v___x_2921_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v_val_2926_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___x_2974_; lean_object* v_baseName_2975_; lean_object* v_dir_2976_; lean_object* v_config_2977_; lean_object* v_relManifestFile_2978_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; uint8_t v_fst_2983_; lean_object* v_snd_2984_; lean_object* v_packagesDir_x3f_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3041_; lean_object* v___y_3042_; uint8_t v___x_3046_; lean_object* v_rootName_3047_; lean_object* v_fst_3049_; lean_object* v_snd_3050_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v_val_3119_; lean_object* v___x_3145_; 
v_packages_2920_ = lean_ctor_get(v_ws_2889_, 4);
v___x_2921_ = lean_unsigned_to_nat(0u);
v___x_2974_ = lean_array_fget_borrowed(v_packages_2920_, v___x_2921_);
v_baseName_2975_ = lean_ctor_get(v___x_2974_, 1);
v_dir_2976_ = lean_ctor_get(v___x_2974_, 4);
v_config_2977_ = lean_ctor_get(v___x_2974_, 6);
v_relManifestFile_2978_ = lean_ctor_get(v___x_2974_, 9);
v___x_3046_ = 0;
lean_inc(v_baseName_2975_);
v_rootName_3047_ = l_Lean_Name_toString(v_baseName_2975_, v___x_3046_);
lean_inc_ref(v_relManifestFile_2978_);
lean_inc_ref(v_dir_2976_);
v___x_3116_ = l_Lake_joinRelative(v_dir_2976_, v_relManifestFile_2978_);
v___x_3117_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_3145_ = l_Lake_Manifest_load(v___x_3116_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3145_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3145_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
lean_ctor_set_tag(v___x_3148_, 1);
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
v_val_3119_ = v___x_3151_;
goto v___jp_3118_;
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v_a_3154_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3145_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3145_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set_tag(v___x_3156_, 0);
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
v_val_3119_ = v___x_3159_;
goto v___jp_3118_;
}
}
}
v___jp_2893_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2895_ = lean_box(0);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
lean_ctor_set(v___x_2896_, 1, v___y_2894_);
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
v___jp_2898_:
{
if (lean_obj_tag(v_fst_2900_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2916_; 
lean_dec(v_snd_2901_);
v_a_2902_ = lean_ctor_get(v_fst_2900_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_fst_2900_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2904_ = v_fst_2900_;
v_isShared_2905_ = v_isSharedCheck_2916_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v_fst_2900_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2916_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2906_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2907_ = lean_io_error_to_string(v_a_2902_);
v___x_2908_ = lean_string_append(v___x_2906_, v___x_2907_);
lean_dec_ref(v___x_2907_);
v___x_2909_ = 3;
v___x_2910_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set_uint8(v___x_2910_, sizeof(void*)*1, v___x_2909_);
lean_inc_ref(v___y_2899_);
v___x_2911_ = lean_apply_2(v___y_2899_, v___x_2910_, lean_box(0));
v___x_2912_ = lean_box(0);
if (v_isShared_2905_ == 0)
{
lean_ctor_set_tag(v___x_2904_, 1);
lean_ctor_set(v___x_2904_, 0, v___x_2912_);
v___x_2914_ = v___x_2904_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
else
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
lean_dec_ref(v_fst_2900_);
v___x_2917_ = lean_box(0);
v___x_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v_snd_2901_);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
v___jp_2922_:
{
lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2927_ = lean_array_get_size(v___y_2924_);
v___x_2928_ = lean_nat_dec_lt(v___x_2921_, v___x_2927_);
if (v___x_2928_ == 0)
{
v___y_2899_ = v___y_2923_;
v_fst_2900_ = v_val_2926_;
v_snd_2901_ = v___y_2925_;
goto v___jp_2898_;
}
else
{
lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2929_ = lean_box(0);
v___x_2930_ = lean_nat_dec_le(v___x_2927_, v___x_2927_);
if (v___x_2930_ == 0)
{
if (v___x_2928_ == 0)
{
v___y_2899_ = v___y_2923_;
v_fst_2900_ = v_val_2926_;
v_snd_2901_ = v___y_2925_;
goto v___jp_2898_;
}
else
{
size_t v___x_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = lean_usize_of_nat(v___x_2927_);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2924_, v___x_2931_, v___x_2932_, v___x_2929_, v___y_2923_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_dec_ref_known(v___x_2933_, 1);
v___y_2899_ = v___y_2923_;
v_fst_2900_ = v_val_2926_;
v_snd_2901_ = v___y_2925_;
goto v___jp_2898_;
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v_val_2926_);
lean_dec(v___y_2925_);
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
else
{
size_t v___x_2942_; size_t v___x_2943_; lean_object* v___x_2944_; 
v___x_2942_ = ((size_t)0ULL);
v___x_2943_ = lean_usize_of_nat(v___x_2927_);
v___x_2944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2924_, v___x_2942_, v___x_2943_, v___x_2929_, v___y_2923_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_dec_ref_known(v___x_2944_, 1);
v___y_2899_ = v___y_2923_;
v_fst_2900_ = v_val_2926_;
v_snd_2901_ = v___y_2925_;
goto v___jp_2898_;
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec_ref(v_val_2926_);
lean_dec(v___y_2925_);
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
}
v___jp_2953_:
{
if (lean_obj_tag(v___y_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
v_a_2958_ = lean_ctor_get(v___y_2957_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___y_2957_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___y_2957_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___y_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set_tag(v___x_2960_, 1);
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
v___y_2923_ = v___y_2954_;
v___y_2924_ = v___y_2955_;
v___y_2925_ = v___y_2956_;
v_val_2926_ = v___x_2963_;
goto v___jp_2922_;
}
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
v_a_2966_ = lean_ctor_get(v___y_2957_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___y_2957_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___y_2957_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___y_2957_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set_tag(v___x_2968_, 0);
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
v___y_2923_ = v___y_2954_;
v___y_2924_ = v___y_2955_;
v___y_2925_ = v___y_2956_;
v_val_2926_ = v___x_2971_;
goto v___jp_2922_;
}
}
}
}
v___jp_2979_:
{
lean_object* v_toWorkspaceConfig_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v_toWorkspaceConfig_2985_ = lean_ctor_get(v_config_2977_, 0);
v___x_2986_ = l_System_FilePath_normalize(v___y_2980_);
lean_inc_ref(v_toWorkspaceConfig_2985_);
v___x_2987_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2985_);
lean_inc_ref(v___x_2987_);
v___x_2988_ = l_System_FilePath_normalize(v___x_2987_);
v___x_2989_ = lean_string_dec_eq(v___x_2986_, v___x_2988_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v___x_2986_);
if (v___x_2989_ == 0)
{
if (v_fst_2983_ == 0)
{
lean_dec_ref(v___x_2987_);
lean_dec_ref(v___y_2982_);
v___y_2894_ = v_snd_2984_;
goto v___jp_2893_;
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2990_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2991_ = lean_string_append(v___x_2990_, v___y_2982_);
v___x_2992_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2993_ = lean_string_append(v___x_2991_, v___x_2992_);
lean_inc_ref(v_dir_2976_);
v___x_2994_ = l_Lake_joinRelative(v_dir_2976_, v___x_2987_);
v___x_2995_ = lean_string_append(v___x_2993_, v___x_2994_);
v___x_2996_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2997_ = lean_string_append(v___x_2995_, v___x_2996_);
v___x_2998_ = 1;
v___x_2999_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set_uint8(v___x_2999_, sizeof(void*)*1, v___x_2998_);
lean_inc_ref(v___y_2981_);
v___x_3000_ = lean_apply_2(v___y_2981_, v___x_2999_, lean_box(0));
v___x_3001_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2994_);
v___x_3002_ = l_Lake_createParentDirs(v___x_2994_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v___x_3003_; 
lean_dec_ref_known(v___x_3002_, 1);
v___x_3003_ = lean_io_rename(v___y_2982_, v___x_2994_);
lean_dec_ref(v___x_2994_);
lean_dec_ref(v___y_2982_);
v___y_2954_ = v___y_2981_;
v___y_2955_ = v___x_3001_;
v___y_2956_ = v_snd_2984_;
v___y_2957_ = v___x_3003_;
goto v___jp_2953_;
}
else
{
lean_dec_ref(v___x_2994_);
lean_dec_ref(v___y_2982_);
v___y_2954_ = v___y_2981_;
v___y_2955_ = v___x_3001_;
v___y_2956_ = v_snd_2984_;
v___y_2957_ = v___x_3002_;
goto v___jp_2953_;
}
}
}
else
{
lean_dec_ref(v___x_2987_);
lean_dec_ref(v___y_2982_);
v___y_2894_ = v_snd_2984_;
goto v___jp_2893_;
}
}
v___jp_3004_:
{
if (lean_obj_tag(v_packagesDir_x3f_3005_) == 1)
{
lean_object* v_val_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v_val_3008_ = lean_ctor_get(v_packagesDir_x3f_3005_, 0);
lean_inc_n(v_val_3008_, 2);
lean_dec_ref_known(v_packagesDir_x3f_3005_, 1);
lean_inc_ref(v_dir_2976_);
v___x_3009_ = l_Lake_joinRelative(v_dir_2976_, v_val_3008_);
v___x_3010_ = l_System_FilePath_pathExists(v___x_3009_);
v___x_3011_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_3012_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_3012_ == 0)
{
v___y_2980_ = v_val_3008_;
v___y_2981_ = v___y_3007_;
v___y_2982_ = v___x_3009_;
v_fst_2983_ = v___x_3010_;
v_snd_2984_ = v___y_3006_;
goto v___jp_2979_;
}
else
{
lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_3014_ == 0)
{
if (v___x_3012_ == 0)
{
v___y_2980_ = v_val_3008_;
v___y_2981_ = v___y_3007_;
v___y_2982_ = v___x_3009_;
v_fst_2983_ = v___x_3010_;
v_snd_2984_ = v___y_3006_;
goto v___jp_2979_;
}
else
{
size_t v___x_3015_; size_t v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = ((size_t)0ULL);
v___x_3016_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_3011_, v___x_3015_, v___x_3016_, v___x_3013_, v___y_3007_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_dec_ref_known(v___x_3017_, 1);
v___y_2980_ = v_val_3008_;
v___y_2981_ = v___y_3007_;
v___y_2982_ = v___x_3009_;
v_fst_2983_ = v___x_3010_;
v_snd_2984_ = v___y_3006_;
goto v___jp_2979_;
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec_ref(v___x_3009_);
lean_dec(v_val_3008_);
lean_dec(v___y_3006_);
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
else
{
size_t v___x_3026_; size_t v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = ((size_t)0ULL);
v___x_3027_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_3011_, v___x_3026_, v___x_3027_, v___x_3013_, v___y_3007_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_dec_ref_known(v___x_3028_, 1);
v___y_2980_ = v_val_3008_;
v___y_2981_ = v___y_3007_;
v___y_2982_ = v___x_3009_;
v_fst_2983_ = v___x_3010_;
v_snd_2984_ = v___y_3006_;
goto v___jp_2979_;
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref(v___x_3009_);
lean_dec(v_val_3008_);
lean_dec(v___y_3006_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_dec(v_packagesDir_x3f_3005_);
v___x_3037_ = lean_box(0);
v___x_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v___y_3006_);
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
return v___x_3039_;
}
}
v___jp_3040_:
{
if (lean_obj_tag(v___y_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v_snd_3044_; lean_object* v_packagesDir_x3f_3045_; 
v_a_3043_ = lean_ctor_get(v___y_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___y_3042_, 1);
v_snd_3044_ = lean_ctor_get(v_a_3043_, 1);
lean_inc(v_snd_3044_);
lean_dec(v_a_3043_);
v_packagesDir_x3f_3045_ = lean_ctor_get(v___y_3041_, 2);
lean_inc(v_packagesDir_x3f_3045_);
lean_dec_ref(v___y_3041_);
v_packagesDir_x3f_3005_ = v_packagesDir_x3f_3045_;
v___y_3006_ = v_snd_3044_;
v___y_3007_ = v_a_2888_;
goto v___jp_3004_;
}
else
{
lean_dec_ref(v___y_3041_);
return v___y_3042_;
}
}
v___jp_3048_:
{
if (lean_obj_tag(v_fst_3049_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3098_; 
v_a_3051_ = lean_ctor_get(v_fst_3049_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_fst_3049_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3053_ = v_fst_3049_;
v_isShared_3054_ = v_isSharedCheck_3098_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v_fst_3049_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3098_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
if (lean_obj_tag(v_a_3051_) == 11)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_dec_ref_known(v_a_3051_, 2);
lean_del_object(v___x_3053_);
v___x_3055_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_3056_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_2890_, v___x_2974_, v___x_2921_, v___x_3055_, v_snd_3050_, v_a_2888_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3078_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3078_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3078_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v_snd_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3076_; 
v_snd_3061_ = lean_ctor_get(v_a_3057_, 1);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_a_3057_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v_a_3057_, 0);
lean_dec(v_unused_3077_);
v___x_3063_ = v_a_3057_;
v_isShared_3064_ = v_isSharedCheck_3076_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_snd_3061_);
lean_dec(v_a_3057_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3076_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3071_; 
v___x_3065_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_3066_ = lean_string_append(v_rootName_3047_, v___x_3065_);
v___x_3067_ = 1;
v___x_3068_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set_uint8(v___x_3068_, sizeof(void*)*1, v___x_3067_);
lean_inc_ref(v_a_2888_);
v___x_3069_ = lean_apply_2(v_a_2888_, v___x_3068_, lean_box(0));
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 0, v___x_3069_);
v___x_3071_ = v___x_3063_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3069_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_snd_3061_);
v___x_3071_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3073_; 
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3071_);
v___x_3073_ = v___x_3059_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_3047_);
return v___x_3056_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2890_) == 0)
{
lean_object* v___x_3079_; uint8_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
lean_dec_ref_known(v_toUpdate_2890_, 5);
lean_dec(v_snd_3050_);
lean_dec_ref(v_rootName_3047_);
v___x_3079_ = lean_io_error_to_string(v_a_3051_);
v___x_3080_ = 3;
v___x_3081_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set_uint8(v___x_3081_, sizeof(void*)*1, v___x_3080_);
lean_inc_ref(v_a_2888_);
v___x_3082_ = lean_apply_2(v_a_2888_, v___x_3081_, lean_box(0));
v___x_3083_ = lean_box(0);
if (v_isShared_3054_ == 0)
{
lean_ctor_set_tag(v___x_3053_, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3083_);
v___x_3085_ = v___x_3053_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3087_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_3088_ = lean_string_append(v_rootName_3047_, v___x_3087_);
v___x_3089_ = lean_io_error_to_string(v_a_3051_);
v___x_3090_ = lean_string_append(v___x_3088_, v___x_3089_);
lean_dec_ref(v___x_3089_);
v___x_3091_ = 2;
v___x_3092_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3092_, 0, v___x_3090_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*1, v___x_3091_);
lean_inc_ref(v_a_2888_);
v___x_3093_ = lean_apply_2(v_a_2888_, v___x_3092_, lean_box(0));
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v_snd_3050_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v___x_3094_);
v___x_3096_ = v___x_3053_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v_packagesDir_x3f_3100_; lean_object* v_packages_3101_; lean_object* v___x_3102_; 
lean_dec_ref(v_rootName_3047_);
v_a_3099_ = lean_ctor_get(v_fst_3049_, 0);
lean_inc(v_a_3099_);
lean_dec_ref_known(v_fst_3049_, 1);
v_packagesDir_x3f_3100_ = lean_ctor_get(v_a_3099_, 2);
v_packages_3101_ = lean_ctor_get(v_a_3099_, 3);
lean_inc(v_toUpdate_2890_);
v___x_3102_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_2890_, v___x_2974_, v___x_2921_, v_packages_3101_, v_snd_3050_, v_a_2888_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
if (lean_obj_tag(v_toUpdate_2890_) == 0)
{
lean_object* v_snd_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v_snd_3104_ = lean_ctor_get(v_a_3103_, 1);
lean_inc(v_snd_3104_);
lean_dec(v_a_3103_);
v___x_3105_ = lean_array_get_size(v_packages_3101_);
v___x_3106_ = lean_nat_dec_lt(v___x_2921_, v___x_3105_);
if (v___x_3106_ == 0)
{
lean_inc(v_packagesDir_x3f_3100_);
lean_dec_ref_known(v_toUpdate_2890_, 5);
lean_dec(v_a_3099_);
v_packagesDir_x3f_3005_ = v_packagesDir_x3f_3100_;
v___y_3006_ = v_snd_3104_;
v___y_3007_ = v_a_2888_;
goto v___jp_3004_;
}
else
{
lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3107_ = lean_box(0);
v___x_3108_ = lean_nat_dec_le(v___x_3105_, v___x_3105_);
if (v___x_3108_ == 0)
{
if (v___x_3106_ == 0)
{
lean_inc(v_packagesDir_x3f_3100_);
lean_dec_ref_known(v_toUpdate_2890_, 5);
lean_dec(v_a_3099_);
v_packagesDir_x3f_3005_ = v_packagesDir_x3f_3100_;
v___y_3006_ = v_snd_3104_;
v___y_3007_ = v_a_2888_;
goto v___jp_3004_;
}
else
{
size_t v___x_3109_; size_t v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = ((size_t)0ULL);
v___x_3110_ = lean_usize_of_nat(v___x_3105_);
v___x_3111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_2890_, v_packages_3101_, v___x_3109_, v___x_3110_, v___x_3107_, v_snd_3104_);
lean_dec_ref_known(v_toUpdate_2890_, 5);
v___y_3041_ = v_a_3099_;
v___y_3042_ = v___x_3111_;
goto v___jp_3040_;
}
}
else
{
size_t v___x_3112_; size_t v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = ((size_t)0ULL);
v___x_3113_ = lean_usize_of_nat(v___x_3105_);
v___x_3114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_2890_, v_packages_3101_, v___x_3112_, v___x_3113_, v___x_3107_, v_snd_3104_);
lean_dec_ref_known(v_toUpdate_2890_, 5);
v___y_3041_ = v_a_3099_;
v___y_3042_ = v___x_3114_;
goto v___jp_3040_;
}
}
}
else
{
lean_object* v_snd_3115_; 
lean_inc(v_packagesDir_x3f_3100_);
lean_dec(v_a_3099_);
v_snd_3115_ = lean_ctor_get(v_a_3103_, 1);
lean_inc(v_snd_3115_);
lean_dec(v_a_3103_);
v_packagesDir_x3f_3005_ = v_packagesDir_x3f_3100_;
v___y_3006_ = v_snd_3115_;
v___y_3007_ = v_a_2888_;
goto v___jp_3004_;
}
}
else
{
lean_dec(v_a_3099_);
lean_dec(v_toUpdate_2890_);
return v___x_3102_;
}
}
}
v___jp_3118_:
{
uint8_t v___x_3120_; 
v___x_3120_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_3120_ == 0)
{
v_fst_3049_ = v_val_3119_;
v_snd_3050_ = v_a_2891_;
goto v___jp_3048_;
}
else
{
lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3121_ = lean_box(0);
v___x_3122_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_3122_ == 0)
{
if (v___x_3120_ == 0)
{
v_fst_3049_ = v_val_3119_;
v_snd_3050_ = v_a_2891_;
goto v___jp_3048_;
}
else
{
size_t v___x_3123_; size_t v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = ((size_t)0ULL);
v___x_3124_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_3117_, v___x_3123_, v___x_3124_, v___x_3121_, v_a_2888_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_dec_ref_known(v___x_3125_, 1);
v_fst_3049_ = v_val_3119_;
v_snd_3050_ = v_a_2891_;
goto v___jp_3048_;
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v_val_3119_);
lean_dec_ref(v_rootName_3047_);
lean_dec(v_a_2891_);
lean_dec(v_toUpdate_2890_);
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
else
{
size_t v___x_3134_; size_t v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = ((size_t)0ULL);
v___x_3135_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_3136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_3117_, v___x_3134_, v___x_3135_, v___x_3121_, v_a_2888_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_dec_ref_known(v___x_3136_, 1);
v_fst_3049_ = v_val_3119_;
v_snd_3050_ = v_a_2891_;
goto v___jp_3048_;
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec_ref(v_val_3119_);
lean_dec_ref(v_rootName_3047_);
lean_dec(v_a_2891_);
lean_dec(v_toUpdate_2890_);
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_3162_, lean_object* v_ws_3163_, lean_object* v_toUpdate_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_3162_, v_ws_3163_, v_toUpdate_3164_, v_a_3165_);
lean_dec_ref(v_ws_3163_);
lean_dec_ref(v_a_3162_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_a_3168_, lean_object* v_ws_3169_, lean_object* v_rootDeps_3170_){
_start:
{
lean_object* v___y_3173_; lean_object* v_lakeEnv_3178_; lean_object* v_lakeArgs_x3f_3179_; lean_object* v_packages_3180_; uint8_t v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3329_; lean_object* v___y_3330_; uint8_t v___y_3331_; lean_object* v___x_3334_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; uint8_t v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; uint8_t v___y_3366_; lean_object* v___y_3367_; lean_object* v___x_3370_; lean_object* v_baseName_3371_; lean_object* v_dir_3372_; lean_object* v_config_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_lakeEnv_3178_ = lean_ctor_get(v_ws_3169_, 0);
lean_inc_ref(v_lakeEnv_3178_);
v_lakeArgs_x3f_3179_ = lean_ctor_get(v_ws_3169_, 3);
lean_inc(v_lakeArgs_x3f_3179_);
v_packages_3180_ = lean_ctor_get(v_ws_3169_, 4);
lean_inc_ref(v_packages_3180_);
lean_dec_ref(v_ws_3169_);
v___x_3334_ = lean_unsigned_to_nat(0u);
v___x_3370_ = lean_array_fget(v_packages_3180_, v___x_3334_);
lean_dec_ref(v_packages_3180_);
v_baseName_3371_ = lean_ctor_get(v___x_3370_, 1);
lean_inc(v_baseName_3371_);
v_dir_3372_ = lean_ctor_get(v___x_3370_, 4);
lean_inc_ref_n(v_dir_3372_, 2);
v_config_3373_ = lean_ctor_get(v___x_3370_, 6);
lean_inc_ref(v_config_3373_);
lean_dec(v___x_3370_);
v___x_3374_ = l_Lake_toolchainFileName;
v___x_3375_ = l_System_FilePath_join(v_dir_3372_, v___x_3374_);
v___x_3376_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3375_);
lean_dec_ref(v___x_3375_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3435_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3379_ = v___x_3376_;
v_isShared_3380_ = v_isSharedCheck_3435_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3435_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v_src_3382_; lean_object* v_tc_x3f_3383_; lean_object* v_clashes_3384_; uint8_t v_fixed_3385_; lean_object* v___y_3409_; uint8_t v_fixedToolchain_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_fixedToolchain_3423_ = lean_ctor_get_uint8(v_config_3373_, sizeof(void*)*27 + 6);
lean_dec_ref(v_config_3373_);
v___x_3424_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_3425_ = lean_array_get_size(v_rootDeps_3170_);
v___x_3426_ = lean_nat_dec_lt(v___x_3334_, v___x_3425_);
if (v___x_3426_ == 0)
{
lean_inc(v_a_3377_);
v_src_3382_ = v_baseName_3371_;
v_tc_x3f_3383_ = v_a_3377_;
v_clashes_3384_ = v___x_3424_;
v_fixed_3385_ = v_fixedToolchain_3423_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3427_; uint8_t v___x_3428_; 
lean_inc(v_a_3377_);
lean_inc(v_baseName_3371_);
v___x_3427_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3427_, 0, v_baseName_3371_);
lean_ctor_set(v___x_3427_, 1, v_a_3377_);
lean_ctor_set(v___x_3427_, 2, v___x_3424_);
lean_ctor_set_uint8(v___x_3427_, sizeof(void*)*3, v_fixedToolchain_3423_);
v___x_3428_ = lean_nat_dec_le(v___x_3425_, v___x_3425_);
if (v___x_3428_ == 0)
{
if (v___x_3426_ == 0)
{
lean_dec_ref_known(v___x_3427_, 3);
lean_inc(v_a_3377_);
v_src_3382_ = v_baseName_3371_;
v_tc_x3f_3383_ = v_a_3377_;
v_clashes_3384_ = v___x_3424_;
v_fixed_3385_ = v_fixedToolchain_3423_;
goto v___jp_3381_;
}
else
{
size_t v___x_3429_; size_t v___x_3430_; lean_object* v___x_3431_; 
lean_dec(v_baseName_3371_);
v___x_3429_ = ((size_t)0ULL);
v___x_3430_ = lean_usize_of_nat(v___x_3425_);
lean_inc_ref(v_dir_3372_);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3372_, v_rootDeps_3170_, v___x_3429_, v___x_3430_, v___x_3427_, v_a_3168_);
v___y_3409_ = v___x_3431_;
goto v___jp_3408_;
}
}
else
{
size_t v___x_3432_; size_t v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v_baseName_3371_);
v___x_3432_ = ((size_t)0ULL);
v___x_3433_ = lean_usize_of_nat(v___x_3425_);
lean_inc_ref(v_dir_3372_);
v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3372_, v_rootDeps_3170_, v___x_3432_, v___x_3433_, v___x_3427_, v_a_3168_);
v___y_3409_ = v___x_3434_;
goto v___jp_3408_;
}
}
v___jp_3381_:
{
lean_object* v___x_3386_; uint8_t v___x_3387_; 
v___x_3386_ = lean_array_get_size(v_clashes_3384_);
v___x_3387_ = lean_nat_dec_lt(v___x_3334_, v___x_3386_);
if (v___x_3387_ == 0)
{
lean_dec_ref(v_clashes_3384_);
lean_dec(v_src_3382_);
if (lean_obj_tag(v_tc_x3f_3383_) == 1)
{
lean_object* v_val_3388_; lean_object* v_rootToolchainFile_3389_; 
v_val_3388_ = lean_ctor_get(v_tc_x3f_3383_, 0);
lean_inc(v_val_3388_);
lean_dec_ref_known(v_tc_x3f_3383_, 1);
v_rootToolchainFile_3389_ = l_Lake_joinRelative(v_dir_3372_, v___x_3374_);
if (lean_obj_tag(v_a_3377_) == 0)
{
lean_del_object(v___x_3379_);
v___y_3329_ = v_val_3388_;
v___y_3330_ = v_rootToolchainFile_3389_;
v___y_3331_ = v___x_3387_;
goto v___jp_3328_;
}
else
{
lean_object* v_val_3390_; uint8_t v___x_3391_; 
v_val_3390_ = lean_ctor_get(v_a_3377_, 0);
lean_inc(v_val_3390_);
lean_dec_ref_known(v_a_3377_, 1);
lean_inc(v_val_3388_);
v___x_3391_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3390_, v_val_3388_);
if (v___x_3391_ == 0)
{
lean_del_object(v___x_3379_);
v___y_3329_ = v_val_3388_;
v___y_3330_ = v_rootToolchainFile_3389_;
v___y_3331_ = v___x_3391_;
goto v___jp_3328_;
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
lean_dec_ref(v_rootToolchainFile_3389_);
lean_dec(v_val_3388_);
lean_dec(v_lakeArgs_x3f_3179_);
lean_dec_ref(v_lakeEnv_3178_);
v___x_3392_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_3168_);
v___x_3393_ = lean_apply_2(v_a_3168_, v___x_3392_, lean_box(0));
v___x_3394_ = lean_box(0);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3394_);
v___x_3396_ = v___x_3379_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3401_; 
lean_dec(v_tc_x3f_3383_);
lean_dec(v_a_3377_);
lean_dec_ref(v_dir_3372_);
lean_dec(v_lakeArgs_x3f_3179_);
lean_dec_ref(v_lakeEnv_3178_);
v___x_3398_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_3168_);
v___x_3399_ = lean_apply_2(v_a_3168_, v___x_3398_, lean_box(0));
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3399_);
v___x_3401_ = v___x_3379_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
else
{
lean_del_object(v___x_3379_);
lean_dec(v_a_3377_);
lean_dec_ref(v_dir_3372_);
lean_dec(v_lakeArgs_x3f_3179_);
lean_dec_ref(v_lakeEnv_3178_);
if (lean_obj_tag(v_tc_x3f_3383_) == 1)
{
if (v_fixed_3385_ == 0)
{
lean_object* v_val_3403_; lean_object* v___x_3404_; 
v_val_3403_ = lean_ctor_get(v_tc_x3f_3383_, 0);
lean_inc(v_val_3403_);
lean_dec_ref_known(v_tc_x3f_3383_, 1);
v___x_3404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3362_ = v_val_3403_;
v___y_3363_ = v_clashes_3384_;
v___y_3364_ = v_src_3382_;
v___y_3365_ = v___x_3386_;
v___y_3366_ = v___x_3387_;
v___y_3367_ = v___x_3404_;
goto v___jp_3361_;
}
else
{
lean_object* v_val_3405_; lean_object* v___x_3406_; 
v_val_3405_ = lean_ctor_get(v_tc_x3f_3383_, 0);
lean_inc(v_val_3405_);
lean_dec_ref_known(v_tc_x3f_3383_, 1);
v___x_3406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3362_ = v_val_3405_;
v___y_3363_ = v_clashes_3384_;
v___y_3364_ = v_src_3382_;
v___y_3365_ = v___x_3386_;
v___y_3366_ = v___x_3387_;
v___y_3367_ = v___x_3406_;
goto v___jp_3361_;
}
}
else
{
lean_object* v___x_3407_; 
lean_dec(v_tc_x3f_3383_);
lean_dec(v_src_3382_);
v___x_3407_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_3336_ = v_clashes_3384_;
v___y_3337_ = v___x_3386_;
v___y_3338_ = v___x_3407_;
goto v___jp_3335_;
}
}
}
v___jp_3408_:
{
if (lean_obj_tag(v___y_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v_src_3411_; lean_object* v_tc_x3f_3412_; lean_object* v_clashes_3413_; uint8_t v_fixed_3414_; 
v_a_3410_ = lean_ctor_get(v___y_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___y_3409_, 1);
v_src_3411_ = lean_ctor_get(v_a_3410_, 0);
lean_inc(v_src_3411_);
v_tc_x3f_3412_ = lean_ctor_get(v_a_3410_, 1);
lean_inc(v_tc_x3f_3412_);
v_clashes_3413_ = lean_ctor_get(v_a_3410_, 2);
lean_inc_ref(v_clashes_3413_);
v_fixed_3414_ = lean_ctor_get_uint8(v_a_3410_, sizeof(void*)*3);
lean_dec(v_a_3410_);
v_src_3382_ = v_src_3411_;
v_tc_x3f_3383_ = v_tc_x3f_3412_;
v_clashes_3384_ = v_clashes_3413_;
v_fixed_3385_ = v_fixed_3414_;
goto v___jp_3381_;
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_del_object(v___x_3379_);
lean_dec(v_a_3377_);
lean_dec_ref(v_dir_3372_);
lean_dec(v_lakeArgs_x3f_3179_);
lean_dec_ref(v_lakeEnv_3178_);
v_a_3415_ = lean_ctor_get(v___y_3409_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___y_3409_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___y_3409_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___y_3409_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3448_; 
lean_dec_ref(v_config_3373_);
lean_dec_ref(v_dir_3372_);
lean_dec(v_baseName_3371_);
lean_dec(v_lakeArgs_x3f_3179_);
lean_dec_ref(v_lakeEnv_3178_);
v_a_3436_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3438_ = v___x_3376_;
v_isShared_3439_ = v_isSharedCheck_3448_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3376_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3448_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; uint8_t v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3440_ = lean_io_error_to_string(v_a_3436_);
v___x_3441_ = 3;
v___x_3442_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3442_, 0, v___x_3440_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*1, v___x_3441_);
lean_inc_ref(v_a_3168_);
v___x_3443_ = lean_apply_2(v_a_3168_, v___x_3442_, lean_box(0));
v___x_3444_ = lean_box(0);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3444_);
v___x_3446_ = v___x_3438_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
v___jp_3172_:
{
uint8_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3174_ = 2;
v___x_3175_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3175_, 0, v___y_3173_);
lean_ctor_set_uint8(v___x_3175_, sizeof(void*)*1, v___x_3174_);
lean_inc_ref(v_a_3168_);
v___x_3176_ = lean_apply_2(v_a_3168_, v___x_3175_, lean_box(0));
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
return v___x_3177_;
}
v___jp_3181_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_inc_ref(v___y_3183_);
v___x_3186_ = lean_string_append(v___y_3183_, v___y_3185_);
v___x_3187_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_3188_ = lean_string_append(v___x_3186_, v___x_3187_);
v___x_3189_ = 1;
v___x_3190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3190_, 0, v___x_3188_);
lean_ctor_set_uint8(v___x_3190_, sizeof(void*)*1, v___x_3189_);
lean_inc_ref(v_a_3168_);
v___x_3191_ = lean_apply_2(v_a_3168_, v___x_3190_, lean_box(0));
v___x_3192_ = l_IO_FS_writeFile(v___y_3184_, v___y_3185_);
lean_dec_ref(v___y_3184_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_dec_ref_known(v___x_3192_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_3179_) == 1)
{
lean_object* v_elan_x3f_3193_; 
v_elan_x3f_3193_ = lean_ctor_get(v_lakeEnv_3178_, 2);
if (lean_obj_tag(v_elan_x3f_3193_) == 1)
{
lean_object* v_val_3194_; lean_object* v_val_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_elan_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_val_3194_ = lean_ctor_get(v_lakeArgs_x3f_3179_, 0);
lean_inc(v_val_3194_);
lean_dec_ref_known(v_lakeArgs_x3f_3179_, 1);
v_val_3195_ = lean_ctor_get(v_elan_x3f_3193_, 0);
v___x_3196_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_3168_);
v___x_3197_ = lean_apply_2(v_a_3168_, v___x_3196_, lean_box(0));
v___x_3198_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_3199_ = lean_ctor_get(v_val_3195_, 1);
lean_inc_ref(v_elan_3199_);
v___x_3200_ = 1;
v___x_3201_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_3202_ = lean_unsigned_to_nat(4u);
v___x_3203_ = lean_mk_empty_array_with_capacity(v___x_3202_);
lean_dec_ref(v___x_3203_);
v___x_3204_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_3205_ = lean_array_push(v___x_3204_, v___y_3185_);
v___x_3206_ = lean_array_push(v___x_3205_, v___x_3201_);
v___x_3207_ = l_Array_append___redArg(v___x_3206_, v_val_3194_);
lean_dec(v_val_3194_);
v___x_3208_ = lean_box(0);
v___x_3209_ = l_Lake_Env_noToolchainVars(v_lakeEnv_3178_);
v___x_3210_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3210_, 0, v___x_3198_);
lean_ctor_set(v___x_3210_, 1, v_elan_3199_);
lean_ctor_set(v___x_3210_, 2, v___x_3207_);
lean_ctor_set(v___x_3210_, 3, v___x_3208_);
lean_ctor_set(v___x_3210_, 4, v___x_3209_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*5, v___x_3200_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*5 + 1, v___y_3182_);
v___x_3211_ = lean_io_process_spawn(v___x_3210_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v___x_3213_ = lean_io_process_child_wait(v___x_3198_, v_a_3212_);
lean_dec(v_a_3212_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; uint32_t v___x_3215_; uint8_t v___x_3216_; lean_object* v___x_3217_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v___x_3215_ = lean_unbox_uint32(v_a_3214_);
lean_dec(v_a_3214_);
v___x_3216_ = lean_uint32_to_uint8(v___x_3215_);
v___x_3217_ = lean_io_exit(v___x_3216_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3238_; 
v_a_3226_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3228_ = v___x_3217_;
v_isShared_3229_ = v_isSharedCheck_3238_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3217_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3238_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; uint8_t v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3230_ = lean_io_error_to_string(v_a_3226_);
v___x_3231_ = 3;
v___x_3232_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3232_, 0, v___x_3230_);
lean_ctor_set_uint8(v___x_3232_, sizeof(void*)*1, v___x_3231_);
lean_inc_ref(v_a_3168_);
v___x_3233_ = lean_apply_2(v_a_3168_, v___x_3232_, lean_box(0));
v___x_3234_ = lean_box(0);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3234_);
v___x_3236_ = v___x_3228_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3251_; 
v_a_3239_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3241_ = v___x_3213_;
v_isShared_3242_ = v_isSharedCheck_3251_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3213_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3251_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; uint8_t v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3243_ = lean_io_error_to_string(v_a_3239_);
v___x_3244_ = 3;
v___x_3245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*1, v___x_3244_);
lean_inc_ref(v_a_3168_);
v___x_3246_ = lean_apply_2(v_a_3168_, v___x_3245_, lean_box(0));
v___x_3247_ = lean_box(0);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v___x_3247_);
v___x_3249_ = v___x_3241_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3264_; 
v_a_3252_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3254_ = v___x_3211_;
v_isShared_3255_ = v_isSharedCheck_3264_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3211_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3264_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3256_ = lean_io_error_to_string(v_a_3252_);
v___x_3257_ = 3;
v___x_3258_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set_uint8(v___x_3258_, sizeof(void*)*1, v___x_3257_);
lean_inc_ref(v_a_3168_);
v___x_3259_ = lean_apply_2(v_a_3168_, v___x_3258_, lean_box(0));
v___x_3260_ = lean_box(0);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v___x_3260_);
v___x_3262_ = v___x_3254_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; lean_object* v___x_3268_; 
lean_dec_ref_known(v_lakeArgs_x3f_3179_, 1);
lean_dec_ref(v___y_3185_);
lean_dec_ref(v_lakeEnv_3178_);
v___x_3265_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_3168_);
v___x_3266_ = lean_apply_2(v_a_3168_, v___x_3265_, lean_box(0));
v___x_3267_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3268_ = lean_io_exit(v___x_3267_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3289_; 
v_a_3277_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3279_ = v___x_3268_;
v_isShared_3280_ = v_isSharedCheck_3289_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3268_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3289_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3281_; uint8_t v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3287_; 
v___x_3281_ = lean_io_error_to_string(v_a_3277_);
v___x_3282_ = 3;
v___x_3283_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set_uint8(v___x_3283_, sizeof(void*)*1, v___x_3282_);
lean_inc_ref(v_a_3168_);
v___x_3284_ = lean_apply_2(v_a_3168_, v___x_3283_, lean_box(0));
v___x_3285_ = lean_box(0);
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 0, v___x_3285_);
v___x_3287_ = v___x_3279_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; lean_object* v___x_3293_; 
lean_dec_ref(v___y_3185_);
lean_dec(v_lakeArgs_x3f_3179_);
lean_dec_ref(v_lakeEnv_3178_);
v___x_3290_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_3168_);
v___x_3291_ = lean_apply_2(v_a_3168_, v___x_3290_, lean_box(0));
v___x_3292_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3293_ = lean_io_exit(v___x_3292_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3293_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3293_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3314_; 
v_a_3302_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3304_ = v___x_3293_;
v_isShared_3305_ = v_isSharedCheck_3314_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3293_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3314_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; uint8_t v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___x_3306_ = lean_io_error_to_string(v_a_3302_);
v___x_3307_ = 3;
v___x_3308_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*1, v___x_3307_);
lean_inc_ref(v_a_3168_);
v___x_3309_ = lean_apply_2(v_a_3168_, v___x_3308_, lean_box(0));
v___x_3310_ = lean_box(0);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3310_);
v___x_3312_ = v___x_3304_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3327_; 
lean_dec_ref(v___y_3185_);
lean_dec(v_lakeArgs_x3f_3179_);
lean_dec_ref(v_lakeEnv_3178_);
v_a_3315_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3317_ = v___x_3192_;
v_isShared_3318_ = v_isSharedCheck_3327_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3192_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3327_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3319_; uint8_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3325_; 
v___x_3319_ = lean_io_error_to_string(v_a_3315_);
v___x_3320_ = 3;
v___x_3321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3321_, 0, v___x_3319_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*1, v___x_3320_);
lean_inc_ref(v_a_3168_);
v___x_3322_ = lean_apply_2(v_a_3168_, v___x_3321_, lean_box(0));
v___x_3323_ = lean_box(0);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v___x_3323_);
v___x_3325_ = v___x_3317_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
v___jp_3328_:
{
lean_object* v___x_3332_; lean_object* v_toString_3333_; 
v___x_3332_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_3333_ = lean_ctor_get(v___y_3329_, 0);
lean_inc_ref(v_toString_3333_);
lean_dec_ref(v___y_3329_);
v___y_3182_ = v___y_3331_;
v___y_3183_ = v___x_3332_;
v___y_3184_ = v___y_3330_;
v___y_3185_ = v_toString_3333_;
goto v___jp_3181_;
}
v___jp_3335_:
{
uint8_t v___x_3339_; 
v___x_3339_ = lean_nat_dec_lt(v___x_3334_, v___y_3337_);
if (v___x_3339_ == 0)
{
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
v___y_3173_ = v___y_3338_;
goto v___jp_3172_;
}
else
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_nat_dec_le(v___y_3337_, v___y_3337_);
if (v___x_3340_ == 0)
{
if (v___x_3339_ == 0)
{
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
v___y_3173_ = v___y_3338_;
goto v___jp_3172_;
}
else
{
size_t v___x_3341_; size_t v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = ((size_t)0ULL);
v___x_3342_ = lean_usize_of_nat(v___y_3337_);
lean_dec(v___y_3337_);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3336_, v___x_3341_, v___x_3342_, v___y_3338_);
lean_dec_ref(v___y_3336_);
v___y_3173_ = v___x_3343_;
goto v___jp_3172_;
}
}
else
{
size_t v___x_3344_; size_t v___x_3345_; lean_object* v___x_3346_; 
v___x_3344_ = ((size_t)0ULL);
v___x_3345_ = lean_usize_of_nat(v___y_3337_);
lean_dec(v___y_3337_);
v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3336_, v___x_3344_, v___x_3345_, v___y_3338_);
lean_dec_ref(v___y_3336_);
v___y_3173_ = v___x_3346_;
goto v___jp_3172_;
}
}
}
v___jp_3347_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_inc_ref(v___y_3352_);
v___x_3355_ = lean_string_append(v___y_3352_, v___y_3354_);
lean_dec_ref(v___y_3354_);
v___x_3356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3357_ = lean_string_append(v___x_3355_, v___x_3356_);
v___x_3358_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3350_, v___y_3353_);
v___x_3359_ = lean_string_append(v___x_3357_, v___x_3358_);
lean_dec_ref(v___x_3358_);
v___x_3360_ = lean_string_append(v___x_3359_, v___y_3348_);
v___y_3336_ = v___y_3349_;
v___y_3337_ = v___y_3351_;
v___y_3338_ = v___x_3360_;
goto v___jp_3335_;
}
v___jp_3361_:
{
lean_object* v___x_3368_; lean_object* v_toString_3369_; 
v___x_3368_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_3369_ = lean_ctor_get(v___y_3362_, 0);
lean_inc_ref(v_toString_3369_);
lean_dec_ref(v___y_3362_);
v___y_3348_ = v___y_3367_;
v___y_3349_ = v___y_3363_;
v___y_3350_ = v___y_3364_;
v___y_3351_ = v___y_3365_;
v___y_3352_ = v___x_3368_;
v___y_3353_ = v___y_3366_;
v___y_3354_ = v_toString_3369_;
goto v___jp_3347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_a_3449_, lean_object* v_ws_3450_, lean_object* v_rootDeps_3451_, lean_object* v_a_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3449_, v_ws_3450_, v_rootDeps_3451_);
lean_dec_ref(v_rootDeps_3451_);
lean_dec_ref(v_a_3449_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(lean_object* v_msg_3454_){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_box(1);
v___x_3456_ = lean_panic_fn_borrowed(v___x_3455_, v_msg_3454_);
return v___x_3456_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3460_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3461_ = lean_unsigned_to_nat(35u);
v___x_3462_ = lean_unsigned_to_nat(182u);
v___x_3463_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3464_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3465_ = l_mkPanicMessageWithDecl(v___x_3464_, v___x_3463_, v___x_3462_, v___x_3461_, v___x_3460_);
return v___x_3465_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3466_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3467_ = lean_unsigned_to_nat(21u);
v___x_3468_ = lean_unsigned_to_nat(183u);
v___x_3469_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3470_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3471_ = l_mkPanicMessageWithDecl(v___x_3470_, v___x_3469_, v___x_3468_, v___x_3467_, v___x_3466_);
return v___x_3471_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3474_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3475_ = lean_unsigned_to_nat(35u);
v___x_3476_ = lean_unsigned_to_nat(276u);
v___x_3477_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3478_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3479_ = l_mkPanicMessageWithDecl(v___x_3478_, v___x_3477_, v___x_3476_, v___x_3475_, v___x_3474_);
return v___x_3479_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3480_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3481_ = lean_unsigned_to_nat(21u);
v___x_3482_ = lean_unsigned_to_nat(277u);
v___x_3483_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3484_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3485_ = l_mkPanicMessageWithDecl(v___x_3484_, v___x_3483_, v___x_3482_, v___x_3481_, v___x_3480_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(lean_object* v_k_3486_, lean_object* v_v_3487_, lean_object* v_t_3488_){
_start:
{
if (lean_obj_tag(v_t_3488_) == 0)
{
lean_object* v_size_3489_; lean_object* v_k_3490_; lean_object* v_v_3491_; lean_object* v_l_3492_; lean_object* v_r_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3849_; 
v_size_3489_ = lean_ctor_get(v_t_3488_, 0);
v_k_3490_ = lean_ctor_get(v_t_3488_, 1);
v_v_3491_ = lean_ctor_get(v_t_3488_, 2);
v_l_3492_ = lean_ctor_get(v_t_3488_, 3);
v_r_3493_ = lean_ctor_get(v_t_3488_, 4);
v_isSharedCheck_3849_ = !lean_is_exclusive(v_t_3488_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3495_ = v_t_3488_;
v_isShared_3496_ = v_isSharedCheck_3849_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_r_3493_);
lean_inc(v_l_3492_);
lean_inc(v_v_3491_);
lean_inc(v_k_3490_);
lean_inc(v_size_3489_);
lean_dec(v_t_3488_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3849_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
uint8_t v___x_3497_; 
v___x_3497_ = lean_string_compare(v_k_3486_, v_k_3490_);
switch(v___x_3497_)
{
case 0:
{
lean_object* v___x_3498_; 
lean_dec(v_size_3489_);
v___x_3498_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3486_, v_v_3487_, v_l_3492_);
if (lean_obj_tag(v_r_3493_) == 0)
{
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_size_3499_; lean_object* v_size_3500_; lean_object* v_k_3501_; lean_object* v_v_3502_; lean_object* v_l_3503_; lean_object* v_r_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; 
v_size_3499_ = lean_ctor_get(v_r_3493_, 0);
v_size_3500_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_size_3500_);
v_k_3501_ = lean_ctor_get(v___x_3498_, 1);
lean_inc(v_k_3501_);
v_v_3502_ = lean_ctor_get(v___x_3498_, 2);
lean_inc(v_v_3502_);
v_l_3503_ = lean_ctor_get(v___x_3498_, 3);
lean_inc(v_l_3503_);
v_r_3504_ = lean_ctor_get(v___x_3498_, 4);
lean_inc(v_r_3504_);
v___x_3505_ = lean_unsigned_to_nat(3u);
v___x_3506_ = lean_nat_mul(v___x_3505_, v_size_3499_);
v___x_3507_ = lean_nat_dec_lt(v___x_3506_, v_size_3500_);
lean_dec(v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3512_; 
lean_dec(v_r_3504_);
lean_dec(v_l_3503_);
lean_dec(v_v_3502_);
lean_dec(v_k_3501_);
v___x_3508_ = lean_unsigned_to_nat(1u);
v___x_3509_ = lean_nat_add(v___x_3508_, v_size_3500_);
lean_dec(v_size_3500_);
v___x_3510_ = lean_nat_add(v___x_3509_, v_size_3499_);
lean_dec(v___x_3509_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 3, v___x_3498_);
lean_ctor_set(v___x_3495_, 0, v___x_3510_);
v___x_3512_ = v___x_3495_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3513_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3513_, 3, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3513_, 4, v_r_3493_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
else
{
lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3585_; 
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; lean_object* v_unused_3587_; lean_object* v_unused_3588_; lean_object* v_unused_3589_; lean_object* v_unused_3590_; 
v_unused_3586_ = lean_ctor_get(v___x_3498_, 4);
lean_dec(v_unused_3586_);
v_unused_3587_ = lean_ctor_get(v___x_3498_, 3);
lean_dec(v_unused_3587_);
v_unused_3588_ = lean_ctor_get(v___x_3498_, 2);
lean_dec(v_unused_3588_);
v_unused_3589_ = lean_ctor_get(v___x_3498_, 1);
lean_dec(v_unused_3589_);
v_unused_3590_ = lean_ctor_get(v___x_3498_, 0);
lean_dec(v_unused_3590_);
v___x_3515_ = v___x_3498_;
v_isShared_3516_ = v_isSharedCheck_3585_;
goto v_resetjp_3514_;
}
else
{
lean_dec(v___x_3498_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3585_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
if (lean_obj_tag(v_l_3503_) == 0)
{
if (lean_obj_tag(v_r_3504_) == 0)
{
lean_object* v_size_3517_; lean_object* v_size_3518_; lean_object* v_k_3519_; lean_object* v_v_3520_; lean_object* v_l_3521_; lean_object* v_r_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v_size_3517_ = lean_ctor_get(v_l_3503_, 0);
v_size_3518_ = lean_ctor_get(v_r_3504_, 0);
v_k_3519_ = lean_ctor_get(v_r_3504_, 1);
v_v_3520_ = lean_ctor_get(v_r_3504_, 2);
v_l_3521_ = lean_ctor_get(v_r_3504_, 3);
v_r_3522_ = lean_ctor_get(v_r_3504_, 4);
v___x_3523_ = lean_unsigned_to_nat(2u);
v___x_3524_ = lean_nat_mul(v___x_3523_, v_size_3517_);
v___x_3525_ = lean_nat_dec_lt(v_size_3518_, v___x_3524_);
lean_dec(v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3555_; 
lean_inc(v_r_3522_);
lean_inc(v_l_3521_);
lean_inc(v_v_3520_);
lean_inc(v_k_3519_);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_r_3504_);
if (v_isSharedCheck_3555_ == 0)
{
lean_object* v_unused_3556_; lean_object* v_unused_3557_; lean_object* v_unused_3558_; lean_object* v_unused_3559_; lean_object* v_unused_3560_; 
v_unused_3556_ = lean_ctor_get(v_r_3504_, 4);
lean_dec(v_unused_3556_);
v_unused_3557_ = lean_ctor_get(v_r_3504_, 3);
lean_dec(v_unused_3557_);
v_unused_3558_ = lean_ctor_get(v_r_3504_, 2);
lean_dec(v_unused_3558_);
v_unused_3559_ = lean_ctor_get(v_r_3504_, 1);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_r_3504_, 0);
lean_dec(v_unused_3560_);
v___x_3527_ = v_r_3504_;
v_isShared_3528_ = v_isSharedCheck_3555_;
goto v_resetjp_3526_;
}
else
{
lean_dec(v_r_3504_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3555_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___x_3543_; lean_object* v___y_3545_; 
v___x_3529_ = lean_unsigned_to_nat(1u);
v___x_3530_ = lean_nat_add(v___x_3529_, v_size_3500_);
lean_dec(v_size_3500_);
v___x_3531_ = lean_nat_add(v___x_3530_, v_size_3499_);
lean_dec(v___x_3530_);
v___x_3543_ = lean_nat_add(v___x_3529_, v_size_3517_);
if (lean_obj_tag(v_l_3521_) == 0)
{
lean_object* v_size_3553_; 
v_size_3553_ = lean_ctor_get(v_l_3521_, 0);
lean_inc(v_size_3553_);
v___y_3545_ = v_size_3553_;
goto v___jp_3544_;
}
else
{
lean_object* v___x_3554_; 
v___x_3554_ = lean_unsigned_to_nat(0u);
v___y_3545_ = v___x_3554_;
goto v___jp_3544_;
}
v___jp_3532_:
{
lean_object* v___x_3536_; lean_object* v___x_3538_; 
v___x_3536_ = lean_nat_add(v___y_3533_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec(v___y_3533_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 4, v_r_3493_);
lean_ctor_set(v___x_3527_, 3, v_r_3522_);
lean_ctor_set(v___x_3527_, 2, v_v_3491_);
lean_ctor_set(v___x_3527_, 1, v_k_3490_);
lean_ctor_set(v___x_3527_, 0, v___x_3536_);
v___x_3538_ = v___x_3527_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3536_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3542_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3542_, 3, v_r_3522_);
lean_ctor_set(v_reuseFailAlloc_3542_, 4, v_r_3493_);
v___x_3538_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_object* v___x_3540_; 
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 4, v___x_3538_);
lean_ctor_set(v___x_3515_, 3, v___y_3534_);
lean_ctor_set(v___x_3515_, 2, v_v_3520_);
lean_ctor_set(v___x_3515_, 1, v_k_3519_);
lean_ctor_set(v___x_3515_, 0, v___x_3531_);
v___x_3540_ = v___x_3515_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_k_3519_);
lean_ctor_set(v_reuseFailAlloc_3541_, 2, v_v_3520_);
lean_ctor_set(v_reuseFailAlloc_3541_, 3, v___y_3534_);
lean_ctor_set(v_reuseFailAlloc_3541_, 4, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
v___jp_3544_:
{
lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3546_ = lean_nat_add(v___x_3543_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec(v___x_3543_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v_l_3521_);
lean_ctor_set(v___x_3495_, 3, v_l_3503_);
lean_ctor_set(v___x_3495_, 2, v_v_3502_);
lean_ctor_set(v___x_3495_, 1, v_k_3501_);
lean_ctor_set(v___x_3495_, 0, v___x_3546_);
v___x_3548_ = v___x_3495_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_k_3501_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_v_3502_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v_l_3503_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v_l_3521_);
v___x_3548_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
lean_object* v___x_3549_; 
v___x_3549_ = lean_nat_add(v___x_3529_, v_size_3499_);
if (lean_obj_tag(v_r_3522_) == 0)
{
lean_object* v_size_3550_; 
v_size_3550_ = lean_ctor_get(v_r_3522_, 0);
lean_inc(v_size_3550_);
v___y_3533_ = v___x_3549_;
v___y_3534_ = v___x_3548_;
v___y_3535_ = v_size_3550_;
goto v___jp_3532_;
}
else
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_unsigned_to_nat(0u);
v___y_3533_ = v___x_3549_;
v___y_3534_ = v___x_3548_;
v___y_3535_ = v___x_3551_;
goto v___jp_3532_;
}
}
}
}
}
else
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3567_; 
lean_del_object(v___x_3495_);
v___x_3561_ = lean_unsigned_to_nat(1u);
v___x_3562_ = lean_nat_add(v___x_3561_, v_size_3500_);
lean_dec(v_size_3500_);
v___x_3563_ = lean_nat_add(v___x_3562_, v_size_3499_);
lean_dec(v___x_3562_);
v___x_3564_ = lean_nat_add(v___x_3561_, v_size_3499_);
v___x_3565_ = lean_nat_add(v___x_3564_, v_size_3518_);
lean_dec(v___x_3564_);
lean_inc_ref(v_r_3493_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 4, v_r_3493_);
lean_ctor_set(v___x_3515_, 3, v_r_3504_);
lean_ctor_set(v___x_3515_, 2, v_v_3491_);
lean_ctor_set(v___x_3515_, 1, v_k_3490_);
lean_ctor_set(v___x_3515_, 0, v___x_3565_);
v___x_3567_ = v___x_3515_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3580_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3580_, 3, v_r_3504_);
lean_ctor_set(v_reuseFailAlloc_3580_, 4, v_r_3493_);
v___x_3567_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
v_isSharedCheck_3574_ = !lean_is_exclusive(v_r_3493_);
if (v_isSharedCheck_3574_ == 0)
{
lean_object* v_unused_3575_; lean_object* v_unused_3576_; lean_object* v_unused_3577_; lean_object* v_unused_3578_; lean_object* v_unused_3579_; 
v_unused_3575_ = lean_ctor_get(v_r_3493_, 4);
lean_dec(v_unused_3575_);
v_unused_3576_ = lean_ctor_get(v_r_3493_, 3);
lean_dec(v_unused_3576_);
v_unused_3577_ = lean_ctor_get(v_r_3493_, 2);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_r_3493_, 1);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_r_3493_, 0);
lean_dec(v_unused_3579_);
v___x_3569_ = v_r_3493_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_dec(v_r_3493_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 4, v___x_3567_);
lean_ctor_set(v___x_3569_, 3, v_l_3503_);
lean_ctor_set(v___x_3569_, 2, v_v_3502_);
lean_ctor_set(v___x_3569_, 1, v_k_3501_);
lean_ctor_set(v___x_3569_, 0, v___x_3563_);
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v_k_3501_);
lean_ctor_set(v_reuseFailAlloc_3573_, 2, v_v_3502_);
lean_ctor_set(v_reuseFailAlloc_3573_, 3, v_l_3503_);
lean_ctor_set(v_reuseFailAlloc_3573_, 4, v___x_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
lean_dec_ref_known(v_l_3503_, 5);
lean_del_object(v___x_3515_);
lean_dec(v_v_3502_);
lean_dec(v_k_3501_);
lean_dec(v_size_3500_);
lean_dec_ref_known(v_r_3493_, 5);
lean_del_object(v___x_3495_);
lean_dec(v_v_3491_);
lean_dec(v_k_3490_);
v___x_3581_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3);
v___x_3582_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3581_);
return v___x_3582_;
}
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_del_object(v___x_3515_);
lean_dec(v_r_3504_);
lean_dec(v_v_3502_);
lean_dec(v_k_3501_);
lean_dec(v_size_3500_);
lean_dec_ref_known(v_r_3493_, 5);
lean_del_object(v___x_3495_);
lean_dec(v_v_3491_);
lean_dec(v_k_3490_);
v___x_3583_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4);
v___x_3584_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3583_);
return v___x_3584_;
}
}
}
}
else
{
lean_object* v_size_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
v_size_3591_ = lean_ctor_get(v_r_3493_, 0);
v___x_3592_ = lean_unsigned_to_nat(1u);
v___x_3593_ = lean_nat_add(v___x_3592_, v_size_3591_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 3, v___x_3498_);
lean_ctor_set(v___x_3495_, 0, v___x_3593_);
v___x_3595_ = v___x_3495_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3596_, 3, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_r_3493_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
else
{
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_l_3597_; 
v_l_3597_ = lean_ctor_get(v___x_3498_, 3);
lean_inc(v_l_3597_);
if (lean_obj_tag(v_l_3597_) == 0)
{
lean_object* v_r_3598_; 
v_r_3598_ = lean_ctor_get(v___x_3498_, 4);
lean_inc(v_r_3598_);
if (lean_obj_tag(v_r_3598_) == 0)
{
lean_object* v_size_3599_; lean_object* v_k_3600_; lean_object* v_v_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3615_; 
v_size_3599_ = lean_ctor_get(v___x_3498_, 0);
v_k_3600_ = lean_ctor_get(v___x_3498_, 1);
v_v_3601_ = lean_ctor_get(v___x_3498_, 2);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; lean_object* v_unused_3617_; 
v_unused_3616_ = lean_ctor_get(v___x_3498_, 4);
lean_dec(v_unused_3616_);
v_unused_3617_ = lean_ctor_get(v___x_3498_, 3);
lean_dec(v_unused_3617_);
v___x_3603_ = v___x_3498_;
v_isShared_3604_ = v_isSharedCheck_3615_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_v_3601_);
lean_inc(v_k_3600_);
lean_inc(v_size_3599_);
lean_dec(v___x_3498_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3615_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_size_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
v_size_3605_ = lean_ctor_get(v_r_3598_, 0);
v___x_3606_ = lean_unsigned_to_nat(1u);
v___x_3607_ = lean_nat_add(v___x_3606_, v_size_3599_);
lean_dec(v_size_3599_);
v___x_3608_ = lean_nat_add(v___x_3606_, v_size_3605_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v_r_3493_);
lean_ctor_set(v___x_3603_, 3, v_r_3598_);
lean_ctor_set(v___x_3603_, 2, v_v_3491_);
lean_ctor_set(v___x_3603_, 1, v_k_3490_);
lean_ctor_set(v___x_3603_, 0, v___x_3608_);
v___x_3610_ = v___x_3603_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3614_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3614_, 3, v_r_3598_);
lean_ctor_set(v_reuseFailAlloc_3614_, 4, v_r_3493_);
v___x_3610_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3612_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v___x_3610_);
lean_ctor_set(v___x_3495_, 3, v_l_3597_);
lean_ctor_set(v___x_3495_, 2, v_v_3601_);
lean_ctor_set(v___x_3495_, 1, v_k_3600_);
lean_ctor_set(v___x_3495_, 0, v___x_3607_);
v___x_3612_ = v___x_3495_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_k_3600_);
lean_ctor_set(v_reuseFailAlloc_3613_, 2, v_v_3601_);
lean_ctor_set(v_reuseFailAlloc_3613_, 3, v_l_3597_);
lean_ctor_set(v_reuseFailAlloc_3613_, 4, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
lean_object* v_k_3618_; lean_object* v_v_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3631_; 
v_k_3618_ = lean_ctor_get(v___x_3498_, 1);
v_v_3619_ = lean_ctor_get(v___x_3498_, 2);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; lean_object* v_unused_3633_; lean_object* v_unused_3634_; 
v_unused_3632_ = lean_ctor_get(v___x_3498_, 4);
lean_dec(v_unused_3632_);
v_unused_3633_ = lean_ctor_get(v___x_3498_, 3);
lean_dec(v_unused_3633_);
v_unused_3634_ = lean_ctor_get(v___x_3498_, 0);
lean_dec(v_unused_3634_);
v___x_3621_ = v___x_3498_;
v_isShared_3622_ = v_isSharedCheck_3631_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_v_3619_);
lean_inc(v_k_3618_);
lean_dec(v___x_3498_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3631_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
v___x_3623_ = lean_unsigned_to_nat(3u);
v___x_3624_ = lean_unsigned_to_nat(1u);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 3, v_r_3598_);
lean_ctor_set(v___x_3621_, 2, v_v_3491_);
lean_ctor_set(v___x_3621_, 1, v_k_3490_);
lean_ctor_set(v___x_3621_, 0, v___x_3624_);
v___x_3626_ = v___x_3621_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3624_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_r_3598_);
lean_ctor_set(v_reuseFailAlloc_3630_, 4, v_r_3598_);
v___x_3626_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3628_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v___x_3626_);
lean_ctor_set(v___x_3495_, 3, v_l_3597_);
lean_ctor_set(v___x_3495_, 2, v_v_3619_);
lean_ctor_set(v___x_3495_, 1, v_k_3618_);
lean_ctor_set(v___x_3495_, 0, v___x_3623_);
v___x_3628_ = v___x_3495_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3629_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3629_, 3, v_l_3597_);
lean_ctor_set(v_reuseFailAlloc_3629_, 4, v___x_3626_);
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
}
else
{
lean_object* v_r_3635_; 
v_r_3635_ = lean_ctor_get(v___x_3498_, 4);
lean_inc(v_r_3635_);
if (lean_obj_tag(v_r_3635_) == 0)
{
lean_object* v_k_3636_; lean_object* v_v_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3661_; 
v_k_3636_ = lean_ctor_get(v___x_3498_, 1);
v_v_3637_ = lean_ctor_get(v___x_3498_, 2);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3661_ == 0)
{
lean_object* v_unused_3662_; lean_object* v_unused_3663_; lean_object* v_unused_3664_; 
v_unused_3662_ = lean_ctor_get(v___x_3498_, 4);
lean_dec(v_unused_3662_);
v_unused_3663_ = lean_ctor_get(v___x_3498_, 3);
lean_dec(v_unused_3663_);
v_unused_3664_ = lean_ctor_get(v___x_3498_, 0);
lean_dec(v_unused_3664_);
v___x_3639_ = v___x_3498_;
v_isShared_3640_ = v_isSharedCheck_3661_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_v_3637_);
lean_inc(v_k_3636_);
lean_dec(v___x_3498_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3661_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v_k_3641_; lean_object* v_v_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3657_; 
v_k_3641_ = lean_ctor_get(v_r_3635_, 1);
v_v_3642_ = lean_ctor_get(v_r_3635_, 2);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_r_3635_);
if (v_isSharedCheck_3657_ == 0)
{
lean_object* v_unused_3658_; lean_object* v_unused_3659_; lean_object* v_unused_3660_; 
v_unused_3658_ = lean_ctor_get(v_r_3635_, 4);
lean_dec(v_unused_3658_);
v_unused_3659_ = lean_ctor_get(v_r_3635_, 3);
lean_dec(v_unused_3659_);
v_unused_3660_ = lean_ctor_get(v_r_3635_, 0);
lean_dec(v_unused_3660_);
v___x_3644_ = v_r_3635_;
v_isShared_3645_ = v_isSharedCheck_3657_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_v_3642_);
lean_inc(v_k_3641_);
lean_dec(v_r_3635_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3657_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3646_ = lean_unsigned_to_nat(3u);
v___x_3647_ = lean_unsigned_to_nat(1u);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 4, v_l_3597_);
lean_ctor_set(v___x_3644_, 3, v_l_3597_);
lean_ctor_set(v___x_3644_, 2, v_v_3637_);
lean_ctor_set(v___x_3644_, 1, v_k_3636_);
lean_ctor_set(v___x_3644_, 0, v___x_3647_);
v___x_3649_ = v___x_3644_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_k_3636_);
lean_ctor_set(v_reuseFailAlloc_3656_, 2, v_v_3637_);
lean_ctor_set(v_reuseFailAlloc_3656_, 3, v_l_3597_);
lean_ctor_set(v_reuseFailAlloc_3656_, 4, v_l_3597_);
v___x_3649_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3651_; 
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 4, v_l_3597_);
lean_ctor_set(v___x_3639_, 2, v_v_3491_);
lean_ctor_set(v___x_3639_, 1, v_k_3490_);
lean_ctor_set(v___x_3639_, 0, v___x_3647_);
v___x_3651_ = v___x_3639_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3655_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3655_, 3, v_l_3597_);
lean_ctor_set(v_reuseFailAlloc_3655_, 4, v_l_3597_);
v___x_3651_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3653_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v___x_3651_);
lean_ctor_set(v___x_3495_, 3, v___x_3649_);
lean_ctor_set(v___x_3495_, 2, v_v_3642_);
lean_ctor_set(v___x_3495_, 1, v_k_3641_);
lean_ctor_set(v___x_3495_, 0, v___x_3646_);
v___x_3653_ = v___x_3495_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3654_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3654_, 3, v___x_3649_);
lean_ctor_set(v_reuseFailAlloc_3654_, 4, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
}
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3667_; 
v___x_3665_ = lean_unsigned_to_nat(2u);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v_r_3635_);
lean_ctor_set(v___x_3495_, 3, v___x_3498_);
lean_ctor_set(v___x_3495_, 0, v___x_3665_);
v___x_3667_ = v___x_3495_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3668_, 3, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3668_, 4, v_r_3635_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
else
{
lean_object* v___x_3669_; lean_object* v___x_3671_; 
v___x_3669_ = lean_unsigned_to_nat(1u);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v___x_3498_);
lean_ctor_set(v___x_3495_, 3, v___x_3498_);
lean_ctor_set(v___x_3495_, 0, v___x_3669_);
v___x_3671_ = v___x_3495_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3672_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3672_, 3, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3672_, 4, v___x_3498_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
case 1:
{
lean_object* v___x_3674_; 
lean_dec(v_v_3491_);
lean_dec(v_k_3490_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 2, v_v_3487_);
lean_ctor_set(v___x_3495_, 1, v_k_3486_);
v___x_3674_ = v___x_3495_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_size_3489_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_k_3486_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_v_3487_);
lean_ctor_set(v_reuseFailAlloc_3675_, 3, v_l_3492_);
lean_ctor_set(v_reuseFailAlloc_3675_, 4, v_r_3493_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
default: 
{
lean_object* v___x_3676_; 
lean_dec(v_size_3489_);
v___x_3676_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3486_, v_v_3487_, v_r_3493_);
if (lean_obj_tag(v_l_3492_) == 0)
{
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_size_3677_; lean_object* v_size_3678_; lean_object* v_k_3679_; lean_object* v_v_3680_; lean_object* v_l_3681_; lean_object* v_r_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v_size_3677_ = lean_ctor_get(v_l_3492_, 0);
v_size_3678_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_size_3678_);
v_k_3679_ = lean_ctor_get(v___x_3676_, 1);
lean_inc(v_k_3679_);
v_v_3680_ = lean_ctor_get(v___x_3676_, 2);
lean_inc(v_v_3680_);
v_l_3681_ = lean_ctor_get(v___x_3676_, 3);
lean_inc(v_l_3681_);
v_r_3682_ = lean_ctor_get(v___x_3676_, 4);
lean_inc(v_r_3682_);
v___x_3683_ = lean_unsigned_to_nat(3u);
v___x_3684_ = lean_nat_mul(v___x_3683_, v_size_3677_);
v___x_3685_ = lean_nat_dec_lt(v___x_3684_, v_size_3678_);
lean_dec(v___x_3684_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3690_; 
lean_dec(v_r_3682_);
lean_dec(v_l_3681_);
lean_dec(v_v_3680_);
lean_dec(v_k_3679_);
v___x_3686_ = lean_unsigned_to_nat(1u);
v___x_3687_ = lean_nat_add(v___x_3686_, v_size_3677_);
v___x_3688_ = lean_nat_add(v___x_3687_, v_size_3678_);
lean_dec(v_size_3678_);
lean_dec(v___x_3687_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v___x_3676_);
lean_ctor_set(v___x_3495_, 0, v___x_3688_);
v___x_3690_ = v___x_3495_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3691_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3691_, 3, v_l_3492_);
lean_ctor_set(v_reuseFailAlloc_3691_, 4, v___x_3676_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
else
{
lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3761_; 
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3761_ == 0)
{
lean_object* v_unused_3762_; lean_object* v_unused_3763_; lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; 
v_unused_3762_ = lean_ctor_get(v___x_3676_, 4);
lean_dec(v_unused_3762_);
v_unused_3763_ = lean_ctor_get(v___x_3676_, 3);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v___x_3676_, 2);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v___x_3676_, 1);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v___x_3676_, 0);
lean_dec(v_unused_3766_);
v___x_3693_ = v___x_3676_;
v_isShared_3694_ = v_isSharedCheck_3761_;
goto v_resetjp_3692_;
}
else
{
lean_dec(v___x_3676_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3761_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
if (lean_obj_tag(v_l_3681_) == 0)
{
if (lean_obj_tag(v_r_3682_) == 0)
{
lean_object* v_size_3695_; lean_object* v_k_3696_; lean_object* v_v_3697_; lean_object* v_l_3698_; lean_object* v_r_3699_; lean_object* v_size_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; uint8_t v___x_3703_; 
v_size_3695_ = lean_ctor_get(v_l_3681_, 0);
v_k_3696_ = lean_ctor_get(v_l_3681_, 1);
v_v_3697_ = lean_ctor_get(v_l_3681_, 2);
v_l_3698_ = lean_ctor_get(v_l_3681_, 3);
v_r_3699_ = lean_ctor_get(v_l_3681_, 4);
v_size_3700_ = lean_ctor_get(v_r_3682_, 0);
v___x_3701_ = lean_unsigned_to_nat(2u);
v___x_3702_ = lean_nat_mul(v___x_3701_, v_size_3700_);
v___x_3703_ = lean_nat_dec_lt(v_size_3695_, v___x_3702_);
lean_dec(v___x_3702_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3732_; 
lean_inc(v_r_3699_);
lean_inc(v_l_3698_);
lean_inc(v_v_3697_);
lean_inc(v_k_3696_);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_l_3681_);
if (v_isSharedCheck_3732_ == 0)
{
lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; lean_object* v_unused_3736_; lean_object* v_unused_3737_; 
v_unused_3733_ = lean_ctor_get(v_l_3681_, 4);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_l_3681_, 3);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_l_3681_, 2);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_l_3681_, 1);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_l_3681_, 0);
lean_dec(v_unused_3737_);
v___x_3705_ = v_l_3681_;
v_isShared_3706_ = v_isSharedCheck_3732_;
goto v_resetjp_3704_;
}
else
{
lean_dec(v_l_3681_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3732_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3722_; 
v___x_3707_ = lean_unsigned_to_nat(1u);
v___x_3708_ = lean_nat_add(v___x_3707_, v_size_3677_);
v___x_3709_ = lean_nat_add(v___x_3708_, v_size_3678_);
lean_dec(v_size_3678_);
if (lean_obj_tag(v_l_3698_) == 0)
{
lean_object* v_size_3730_; 
v_size_3730_ = lean_ctor_get(v_l_3698_, 0);
lean_inc(v_size_3730_);
v___y_3722_ = v_size_3730_;
goto v___jp_3721_;
}
else
{
lean_object* v___x_3731_; 
v___x_3731_ = lean_unsigned_to_nat(0u);
v___y_3722_ = v___x_3731_;
goto v___jp_3721_;
}
v___jp_3710_:
{
lean_object* v___x_3714_; lean_object* v___x_3716_; 
v___x_3714_ = lean_nat_add(v___y_3711_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec(v___y_3711_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 4, v_r_3682_);
lean_ctor_set(v___x_3705_, 3, v_r_3699_);
lean_ctor_set(v___x_3705_, 2, v_v_3680_);
lean_ctor_set(v___x_3705_, 1, v_k_3679_);
lean_ctor_set(v___x_3705_, 0, v___x_3714_);
v___x_3716_ = v___x_3705_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3720_, 1, v_k_3679_);
lean_ctor_set(v_reuseFailAlloc_3720_, 2, v_v_3680_);
lean_ctor_set(v_reuseFailAlloc_3720_, 3, v_r_3699_);
lean_ctor_set(v_reuseFailAlloc_3720_, 4, v_r_3682_);
v___x_3716_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3718_; 
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 4, v___x_3716_);
lean_ctor_set(v___x_3693_, 3, v___y_3712_);
lean_ctor_set(v___x_3693_, 2, v_v_3697_);
lean_ctor_set(v___x_3693_, 1, v_k_3696_);
lean_ctor_set(v___x_3693_, 0, v___x_3709_);
v___x_3718_ = v___x_3693_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_k_3696_);
lean_ctor_set(v_reuseFailAlloc_3719_, 2, v_v_3697_);
lean_ctor_set(v_reuseFailAlloc_3719_, 3, v___y_3712_);
lean_ctor_set(v_reuseFailAlloc_3719_, 4, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
v___jp_3721_:
{
lean_object* v___x_3723_; lean_object* v___x_3725_; 
v___x_3723_ = lean_nat_add(v___x_3708_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec(v___x_3708_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v_l_3698_);
lean_ctor_set(v___x_3495_, 0, v___x_3723_);
v___x_3725_ = v___x_3495_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_l_3492_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_l_3698_);
v___x_3725_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_nat_add(v___x_3707_, v_size_3700_);
if (lean_obj_tag(v_r_3699_) == 0)
{
lean_object* v_size_3727_; 
v_size_3727_ = lean_ctor_get(v_r_3699_, 0);
lean_inc(v_size_3727_);
v___y_3711_ = v___x_3726_;
v___y_3712_ = v___x_3725_;
v___y_3713_ = v_size_3727_;
goto v___jp_3710_;
}
else
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_unsigned_to_nat(0u);
v___y_3711_ = v___x_3726_;
v___y_3712_ = v___x_3725_;
v___y_3713_ = v___x_3728_;
goto v___jp_3710_;
}
}
}
}
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3743_; 
lean_del_object(v___x_3495_);
v___x_3738_ = lean_unsigned_to_nat(1u);
v___x_3739_ = lean_nat_add(v___x_3738_, v_size_3677_);
v___x_3740_ = lean_nat_add(v___x_3739_, v_size_3678_);
lean_dec(v_size_3678_);
v___x_3741_ = lean_nat_add(v___x_3739_, v_size_3695_);
lean_dec(v___x_3739_);
lean_inc_ref(v_l_3492_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 4, v_l_3681_);
lean_ctor_set(v___x_3693_, 3, v_l_3492_);
lean_ctor_set(v___x_3693_, 2, v_v_3491_);
lean_ctor_set(v___x_3693_, 1, v_k_3490_);
lean_ctor_set(v___x_3693_, 0, v___x_3741_);
v___x_3743_ = v___x_3693_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v_l_3492_);
lean_ctor_set(v_reuseFailAlloc_3756_, 4, v_l_3681_);
v___x_3743_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
v_isSharedCheck_3750_ = !lean_is_exclusive(v_l_3492_);
if (v_isSharedCheck_3750_ == 0)
{
lean_object* v_unused_3751_; lean_object* v_unused_3752_; lean_object* v_unused_3753_; lean_object* v_unused_3754_; lean_object* v_unused_3755_; 
v_unused_3751_ = lean_ctor_get(v_l_3492_, 4);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_l_3492_, 3);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_l_3492_, 2);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_l_3492_, 1);
lean_dec(v_unused_3754_);
v_unused_3755_ = lean_ctor_get(v_l_3492_, 0);
lean_dec(v_unused_3755_);
v___x_3745_ = v_l_3492_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_dec(v_l_3492_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 4, v_r_3682_);
lean_ctor_set(v___x_3745_, 3, v___x_3743_);
lean_ctor_set(v___x_3745_, 2, v_v_3680_);
lean_ctor_set(v___x_3745_, 1, v_k_3679_);
lean_ctor_set(v___x_3745_, 0, v___x_3740_);
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3740_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_k_3679_);
lean_ctor_set(v_reuseFailAlloc_3749_, 2, v_v_3680_);
lean_ctor_set(v_reuseFailAlloc_3749_, 3, v___x_3743_);
lean_ctor_set(v_reuseFailAlloc_3749_, 4, v_r_3682_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
lean_dec_ref_known(v_l_3681_, 5);
lean_del_object(v___x_3693_);
lean_dec(v_v_3680_);
lean_dec(v_k_3679_);
lean_dec(v_size_3678_);
lean_dec_ref_known(v_l_3492_, 5);
lean_del_object(v___x_3495_);
lean_dec(v_v_3491_);
lean_dec(v_k_3490_);
v___x_3757_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7);
v___x_3758_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3757_);
return v___x_3758_;
}
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_del_object(v___x_3693_);
lean_dec(v_r_3682_);
lean_dec(v_v_3680_);
lean_dec(v_k_3679_);
lean_dec(v_size_3678_);
lean_dec_ref_known(v_l_3492_, 5);
lean_del_object(v___x_3495_);
lean_dec(v_v_3491_);
lean_dec(v_k_3490_);
v___x_3759_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8);
v___x_3760_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3759_);
return v___x_3760_;
}
}
}
}
else
{
lean_object* v_size_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3771_; 
v_size_3767_ = lean_ctor_get(v_l_3492_, 0);
v___x_3768_ = lean_unsigned_to_nat(1u);
v___x_3769_ = lean_nat_add(v___x_3768_, v_size_3767_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v___x_3676_);
lean_ctor_set(v___x_3495_, 0, v___x_3769_);
v___x_3771_ = v___x_3495_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3772_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3772_, 3, v_l_3492_);
lean_ctor_set(v_reuseFailAlloc_3772_, 4, v___x_3676_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
else
{
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_l_3773_; 
v_l_3773_ = lean_ctor_get(v___x_3676_, 3);
lean_inc(v_l_3773_);
if (lean_obj_tag(v_l_3773_) == 0)
{
lean_object* v_r_3774_; 
v_r_3774_ = lean_ctor_get(v___x_3676_, 4);
lean_inc(v_r_3774_);
if (lean_obj_tag(v_r_3774_) == 0)
{
lean_object* v_size_3775_; lean_object* v_k_3776_; lean_object* v_v_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3791_; 
v_size_3775_ = lean_ctor_get(v___x_3676_, 0);
v_k_3776_ = lean_ctor_get(v___x_3676_, 1);
v_v_3777_ = lean_ctor_get(v___x_3676_, 2);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; lean_object* v_unused_3793_; 
v_unused_3792_ = lean_ctor_get(v___x_3676_, 4);
lean_dec(v_unused_3792_);
v_unused_3793_ = lean_ctor_get(v___x_3676_, 3);
lean_dec(v_unused_3793_);
v___x_3779_ = v___x_3676_;
v_isShared_3780_ = v_isSharedCheck_3791_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_v_3777_);
lean_inc(v_k_3776_);
lean_inc(v_size_3775_);
lean_dec(v___x_3676_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3791_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v_size_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3786_; 
v_size_3781_ = lean_ctor_get(v_l_3773_, 0);
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = lean_nat_add(v___x_3782_, v_size_3775_);
lean_dec(v_size_3775_);
v___x_3784_ = lean_nat_add(v___x_3782_, v_size_3781_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 4, v_l_3773_);
lean_ctor_set(v___x_3779_, 3, v_l_3492_);
lean_ctor_set(v___x_3779_, 2, v_v_3491_);
lean_ctor_set(v___x_3779_, 1, v_k_3490_);
lean_ctor_set(v___x_3779_, 0, v___x_3784_);
v___x_3786_ = v___x_3779_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3790_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3790_, 3, v_l_3492_);
lean_ctor_set(v_reuseFailAlloc_3790_, 4, v_l_3773_);
v___x_3786_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3788_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v_r_3774_);
lean_ctor_set(v___x_3495_, 3, v___x_3786_);
lean_ctor_set(v___x_3495_, 2, v_v_3777_);
lean_ctor_set(v___x_3495_, 1, v_k_3776_);
lean_ctor_set(v___x_3495_, 0, v___x_3783_);
v___x_3788_ = v___x_3495_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_k_3776_);
lean_ctor_set(v_reuseFailAlloc_3789_, 2, v_v_3777_);
lean_ctor_set(v_reuseFailAlloc_3789_, 3, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3789_, 4, v_r_3774_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
else
{
lean_object* v_k_3794_; lean_object* v_v_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3819_; 
v_k_3794_ = lean_ctor_get(v___x_3676_, 1);
v_v_3795_ = lean_ctor_get(v___x_3676_, 2);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; lean_object* v_unused_3821_; lean_object* v_unused_3822_; 
v_unused_3820_ = lean_ctor_get(v___x_3676_, 4);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v___x_3676_, 3);
lean_dec(v_unused_3821_);
v_unused_3822_ = lean_ctor_get(v___x_3676_, 0);
lean_dec(v_unused_3822_);
v___x_3797_ = v___x_3676_;
v_isShared_3798_ = v_isSharedCheck_3819_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_v_3795_);
lean_inc(v_k_3794_);
lean_dec(v___x_3676_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3819_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v_k_3799_; lean_object* v_v_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3815_; 
v_k_3799_ = lean_ctor_get(v_l_3773_, 1);
v_v_3800_ = lean_ctor_get(v_l_3773_, 2);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_l_3773_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; lean_object* v_unused_3817_; lean_object* v_unused_3818_; 
v_unused_3816_ = lean_ctor_get(v_l_3773_, 4);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_l_3773_, 3);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_l_3773_, 0);
lean_dec(v_unused_3818_);
v___x_3802_ = v_l_3773_;
v_isShared_3803_ = v_isSharedCheck_3815_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_v_3800_);
lean_inc(v_k_3799_);
lean_dec(v_l_3773_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3815_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3804_ = lean_unsigned_to_nat(3u);
v___x_3805_ = lean_unsigned_to_nat(1u);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 4, v_r_3774_);
lean_ctor_set(v___x_3802_, 3, v_r_3774_);
lean_ctor_set(v___x_3802_, 2, v_v_3491_);
lean_ctor_set(v___x_3802_, 1, v_k_3490_);
lean_ctor_set(v___x_3802_, 0, v___x_3805_);
v___x_3807_ = v___x_3802_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3814_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3814_, 3, v_r_3774_);
lean_ctor_set(v_reuseFailAlloc_3814_, 4, v_r_3774_);
v___x_3807_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3809_; 
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 3, v_r_3774_);
lean_ctor_set(v___x_3797_, 0, v___x_3805_);
v___x_3809_ = v___x_3797_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_k_3794_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_v_3795_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_r_3774_);
lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_r_3774_);
v___x_3809_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3811_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v___x_3809_);
lean_ctor_set(v___x_3495_, 3, v___x_3807_);
lean_ctor_set(v___x_3495_, 2, v_v_3800_);
lean_ctor_set(v___x_3495_, 1, v_k_3799_);
lean_ctor_set(v___x_3495_, 0, v___x_3804_);
v___x_3811_ = v___x_3495_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_k_3799_);
lean_ctor_set(v_reuseFailAlloc_3812_, 2, v_v_3800_);
lean_ctor_set(v_reuseFailAlloc_3812_, 3, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3812_, 4, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3823_; 
v_r_3823_ = lean_ctor_get(v___x_3676_, 4);
lean_inc(v_r_3823_);
if (lean_obj_tag(v_r_3823_) == 0)
{
lean_object* v_k_3824_; lean_object* v_v_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3837_; 
v_k_3824_ = lean_ctor_get(v___x_3676_, 1);
v_v_3825_ = lean_ctor_get(v___x_3676_, 2);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; lean_object* v_unused_3839_; lean_object* v_unused_3840_; 
v_unused_3838_ = lean_ctor_get(v___x_3676_, 4);
lean_dec(v_unused_3838_);
v_unused_3839_ = lean_ctor_get(v___x_3676_, 3);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v___x_3676_, 0);
lean_dec(v_unused_3840_);
v___x_3827_ = v___x_3676_;
v_isShared_3828_ = v_isSharedCheck_3837_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_v_3825_);
lean_inc(v_k_3824_);
lean_dec(v___x_3676_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3837_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3832_; 
v___x_3829_ = lean_unsigned_to_nat(3u);
v___x_3830_ = lean_unsigned_to_nat(1u);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 4, v_l_3773_);
lean_ctor_set(v___x_3827_, 2, v_v_3491_);
lean_ctor_set(v___x_3827_, 1, v_k_3490_);
lean_ctor_set(v___x_3827_, 0, v___x_3830_);
v___x_3832_ = v___x_3827_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3836_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3836_, 3, v_l_3773_);
lean_ctor_set(v_reuseFailAlloc_3836_, 4, v_l_3773_);
v___x_3832_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3834_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v_r_3823_);
lean_ctor_set(v___x_3495_, 3, v___x_3832_);
lean_ctor_set(v___x_3495_, 2, v_v_3825_);
lean_ctor_set(v___x_3495_, 1, v_k_3824_);
lean_ctor_set(v___x_3495_, 0, v___x_3829_);
v___x_3834_ = v___x_3495_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_k_3824_);
lean_ctor_set(v_reuseFailAlloc_3835_, 2, v_v_3825_);
lean_ctor_set(v_reuseFailAlloc_3835_, 3, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3835_, 4, v_r_3823_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3841_ = lean_unsigned_to_nat(2u);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v___x_3676_);
lean_ctor_set(v___x_3495_, 3, v_r_3823_);
lean_ctor_set(v___x_3495_, 0, v___x_3841_);
v___x_3843_ = v___x_3495_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3844_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3844_, 3, v_r_3823_);
lean_ctor_set(v_reuseFailAlloc_3844_, 4, v___x_3676_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
else
{
lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3845_ = lean_unsigned_to_nat(1u);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 4, v___x_3676_);
lean_ctor_set(v___x_3495_, 3, v___x_3676_);
lean_ctor_set(v___x_3495_, 0, v___x_3845_);
v___x_3847_ = v___x_3495_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3848_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3848_, 3, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3848_, 4, v___x_3676_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
lean_ctor_set(v___x_3851_, 1, v_k_3486_);
lean_ctor_set(v___x_3851_, 2, v_v_3487_);
lean_ctor_set(v___x_3851_, 3, v_t_3488_);
lean_ctor_set(v___x_3851_, 4, v_t_3488_);
return v___x_3851_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(lean_object* v_init_3852_, lean_object* v_x_3853_){
_start:
{
if (lean_obj_tag(v_x_3853_) == 0)
{
lean_object* v_k_3854_; lean_object* v_v_3855_; lean_object* v_l_3856_; lean_object* v_r_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v_k_3854_ = lean_ctor_get(v_x_3853_, 1);
lean_inc(v_k_3854_);
v_v_3855_ = lean_ctor_get(v_x_3853_, 2);
lean_inc(v_v_3855_);
v_l_3856_ = lean_ctor_get(v_x_3853_, 3);
lean_inc(v_l_3856_);
v_r_3857_ = lean_ctor_get(v_x_3853_, 4);
lean_inc(v_r_3857_);
lean_dec_ref_known(v_x_3853_, 5);
v___x_3858_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_3852_, v_l_3856_);
v___x_3859_ = 1;
v___x_3860_ = l_Lean_Name_toString(v_k_3854_, v___x_3859_);
v___x_3861_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3861_, 0, v_v_3855_);
v___x_3862_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v___x_3860_, v___x_3861_, v___x_3858_);
v_init_3852_ = v___x_3862_;
v_x_3853_ = v_r_3857_;
goto _start;
}
else
{
return v_init_3852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_m_3864_){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = lean_box(1);
v___x_3866_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v___x_3865_, v_m_3864_);
v___x_3867_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v___x_3870_, uint8_t v_updateToolchain_3871_, lean_object* v_ws_3872_, lean_object* v_dep_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_baseName_3877_; lean_object* v_name_3878_; lean_object* v_opts_3879_; uint8_t v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; uint8_t v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_baseName_3877_ = lean_ctor_get(v___x_3870_, 1);
v_name_3878_ = lean_ctor_get(v_dep_3873_, 0);
v_opts_3879_ = lean_ctor_get(v_dep_3873_, 4);
v___x_3880_ = 0;
lean_inc(v_baseName_3877_);
v___x_3881_ = l_Lean_Name_toString(v_baseName_3877_, v___x_3880_);
v___x_3882_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3883_ = lean_string_append(v___x_3881_, v___x_3882_);
lean_inc(v_name_3878_);
v___x_3884_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3878_, v_updateToolchain_3871_);
v___x_3885_ = lean_string_append(v___x_3883_, v___x_3884_);
lean_dec_ref(v___x_3884_);
v___x_3886_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3887_ = lean_string_append(v___x_3885_, v___x_3886_);
lean_inc(v_opts_3879_);
v___x_3888_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_opts_3879_);
v___x_3889_ = lean_unsigned_to_nat(80u);
v___x_3890_ = l_Lean_Json_pretty(v___x_3888_, v___x_3889_);
v___x_3891_ = lean_string_append(v___x_3887_, v___x_3890_);
lean_dec_ref(v___x_3890_);
v___x_3892_ = 0;
v___x_3893_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3893_, 0, v___x_3891_);
lean_ctor_set_uint8(v___x_3893_, sizeof(void*)*1, v___x_3892_);
lean_inc_ref(v___y_3875_);
v___x_3894_ = lean_apply_2(v___y_3875_, v___x_3893_, lean_box(0));
v___x_3895_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3872_, v___x_3870_, v_dep_3873_, v___y_3874_, v___y_3875_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v___x_3896_, lean_object* v_updateToolchain_3897_, lean_object* v_ws_3898_, lean_object* v_dep_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
uint8_t v_updateToolchain_boxed_3903_; lean_object* v_res_3904_; 
v_updateToolchain_boxed_3903_ = lean_unbox(v_updateToolchain_3897_);
v_res_3904_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v___x_3896_, v_updateToolchain_boxed_3903_, v_ws_3898_, v_dep_3899_, v___y_3900_, v___y_3901_);
lean_dec_ref(v___y_3901_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_a_3905_, lean_object* v_b_3906_){
_start:
{
lean_object* v_next_3907_; 
v_next_3907_ = lean_ctor_get(v_a_3905_, 0);
lean_inc(v_next_3907_);
if (lean_obj_tag(v_next_3907_) == 0)
{
lean_dec_ref(v_a_3905_);
return v_b_3906_;
}
else
{
lean_object* v_upperBound_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3928_; 
v_upperBound_3908_ = lean_ctor_get(v_a_3905_, 1);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_a_3905_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; 
v_unused_3929_ = lean_ctor_get(v_a_3905_, 0);
lean_dec(v_unused_3929_);
v___x_3910_ = v_a_3905_;
v_isShared_3911_ = v_isSharedCheck_3928_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_upperBound_3908_);
lean_dec(v_a_3905_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3928_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v_val_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3927_; 
v_val_3912_ = lean_ctor_get(v_next_3907_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_next_3907_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3914_ = v_next_3907_;
v_isShared_3915_ = v_isSharedCheck_3927_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_val_3912_);
lean_dec(v_next_3907_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3927_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
uint8_t v___x_3916_; 
v___x_3916_ = lean_nat_dec_lt(v_val_3912_, v_upperBound_3908_);
if (v___x_3916_ == 0)
{
lean_del_object(v___x_3914_);
lean_dec(v_val_3912_);
lean_del_object(v___x_3910_);
lean_dec(v_upperBound_3908_);
return v_b_3906_;
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3917_ = lean_unsigned_to_nat(1u);
v___x_3918_ = lean_nat_add(v_val_3912_, v___x_3917_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v___x_3918_);
v___x_3920_ = v___x_3914_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3922_; 
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 0, v___x_3920_);
v___x_3922_ = v___x_3910_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3920_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_upperBound_3908_);
v___x_3922_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3923_; 
v___x_3923_ = lean_array_push(v_b_3906_, v_val_3912_);
v_a_3905_ = v___x_3922_;
v_b_3906_ = v___x_3923_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_n_3930_, lean_object* v_f_3931_, lean_object* v_xs_3932_, lean_object* v_k_3933_, lean_object* v_acc_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
uint8_t v___x_3938_; 
v___x_3938_ = lean_nat_dec_lt(v_k_3933_, v_n_3930_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_dec(v_k_3933_);
lean_dec_ref(v_f_3931_);
v___x_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3939_, 0, v_acc_3934_);
lean_ctor_set(v___x_3939_, 1, v___y_3935_);
v___x_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
return v___x_3940_;
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = lean_array_fget_borrowed(v_xs_3932_, v_k_3933_);
lean_inc_ref(v_f_3931_);
lean_inc_ref(v___y_3936_);
lean_inc(v___x_3941_);
v___x_3942_ = lean_apply_4(v_f_3931_, v___x_3941_, v___y_3935_, v___y_3936_, lean_box(0));
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v_fst_3944_; lean_object* v_snd_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
v_fst_3944_ = lean_ctor_get(v_a_3943_, 0);
lean_inc(v_fst_3944_);
v_snd_3945_ = lean_ctor_get(v_a_3943_, 1);
lean_inc(v_snd_3945_);
lean_dec(v_a_3943_);
v___x_3946_ = lean_unsigned_to_nat(1u);
v___x_3947_ = lean_nat_add(v_k_3933_, v___x_3946_);
lean_dec(v_k_3933_);
v___x_3948_ = lean_array_push(v_acc_3934_, v_fst_3944_);
v_k_3933_ = v___x_3947_;
v_acc_3934_ = v___x_3948_;
v___y_3935_ = v_snd_3945_;
goto _start;
}
else
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
lean_dec_ref(v_acc_3934_);
lean_dec(v_k_3933_);
lean_dec_ref(v_f_3931_);
v_a_3950_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3952_ = v___x_3942_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3942_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object* v_n_3958_, lean_object* v_f_3959_, lean_object* v_xs_3960_, lean_object* v_k_3961_, lean_object* v_acc_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_3958_, v_f_3959_, v_xs_3960_, v_k_3961_, v_acc_3962_, v___y_3963_, v___y_3964_);
lean_dec_ref(v___y_3964_);
lean_dec_ref(v_xs_3960_);
lean_dec(v_n_3958_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object* v_upperBound_3967_, lean_object* v_fst_3968_, lean_object* v___x_3969_, lean_object* v_leanOpts_3970_, lean_object* v_a_3971_, lean_object* v_b_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
uint8_t v___x_3979_; 
v___x_3979_ = lean_nat_dec_lt(v_a_3971_, v_upperBound_3967_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
lean_dec(v_a_3971_);
lean_dec_ref(v_leanOpts_3970_);
v___x_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3980_, 0, v_b_3972_);
lean_ctor_set(v___x_3980_, 1, v___y_3973_);
v___x_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
return v___x_3981_;
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = lean_array_fget_borrowed(v_fst_3968_, v_a_3971_);
lean_inc(v___x_3982_);
v___x_3983_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_3982_, v___y_3973_, v___y_3974_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4058_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_3986_ = v___x_3983_;
v_isShared_3987_ = v_isSharedCheck_4058_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4058_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v_snd_3988_; lean_object* v___x_3989_; lean_object* v_opts_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v_snd_3988_ = lean_ctor_get(v_a_3984_, 1);
lean_inc(v_snd_3988_);
lean_dec(v_a_3984_);
v___x_3989_ = lean_array_fget_borrowed(v___x_3969_, v_a_3971_);
v_opts_3990_ = lean_ctor_get(v___x_3989_, 4);
v___x_3991_ = lean_unsigned_to_nat(0u);
v___x_3992_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3970_);
lean_inc(v_opts_3990_);
lean_inc(v___x_3982_);
v___x_3993_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_3972_, v___x_3982_, v_opts_3990_, v_leanOpts_3970_, v___x_3979_, v___x_3992_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v_a_3995_; lean_object* v_snd_3997_; lean_object* v___x_4001_; uint8_t v___x_4002_; 
lean_del_object(v___x_3986_);
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
v_a_3995_ = lean_ctor_get(v___x_3993_, 1);
lean_inc(v_a_3995_);
lean_dec_ref_known(v___x_3993_, 2);
v___x_4001_ = lean_array_get_size(v_a_3995_);
v___x_4002_ = lean_nat_dec_lt(v___x_3991_, v___x_4001_);
if (v___x_4002_ == 0)
{
lean_dec(v_a_3995_);
v_snd_3997_ = v_snd_3988_;
goto v___jp_3996_;
}
else
{
lean_object* v___x_4003_; uint8_t v___x_4004_; 
v___x_4003_ = lean_box(0);
v___x_4004_ = lean_nat_dec_le(v___x_4001_, v___x_4001_);
if (v___x_4004_ == 0)
{
if (v___x_4002_ == 0)
{
lean_dec(v_a_3995_);
v_snd_3997_ = v_snd_3988_;
goto v___jp_3996_;
}
else
{
size_t v___x_4005_; size_t v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = ((size_t)0ULL);
v___x_4006_ = lean_usize_of_nat(v___x_4001_);
v___x_4007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3995_, v___x_4005_, v___x_4006_, v___x_4003_, v___y_3974_);
lean_dec(v_a_3995_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_dec_ref_known(v___x_4007_, 1);
v_snd_3997_ = v_snd_3988_;
goto v___jp_3996_;
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec(v_a_3994_);
lean_dec(v_snd_3988_);
lean_dec(v_a_3971_);
lean_dec_ref(v_leanOpts_3970_);
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_4007_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_4007_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
}
else
{
size_t v___x_4016_; size_t v___x_4017_; lean_object* v___x_4018_; 
v___x_4016_ = ((size_t)0ULL);
v___x_4017_ = lean_usize_of_nat(v___x_4001_);
v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3995_, v___x_4016_, v___x_4017_, v___x_4003_, v___y_3974_);
lean_dec(v_a_3995_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_dec_ref_known(v___x_4018_, 1);
v_snd_3997_ = v_snd_3988_;
goto v___jp_3996_;
}
else
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
lean_dec(v_a_3994_);
lean_dec(v_snd_3988_);
lean_dec(v_a_3971_);
lean_dec_ref(v_leanOpts_3970_);
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
}
v___jp_3996_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = lean_unsigned_to_nat(1u);
v___x_3999_ = lean_nat_add(v_a_3971_, v___x_3998_);
lean_dec(v_a_3971_);
v_a_3971_ = v___x_3999_;
v_b_3972_ = v_a_3994_;
v___y_3973_ = v_snd_3997_;
goto _start;
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
lean_dec(v_snd_3988_);
lean_dec(v_a_3971_);
lean_dec_ref(v_leanOpts_3970_);
v_a_4027_ = lean_ctor_get(v___x_3993_, 1);
lean_inc(v_a_4027_);
lean_dec_ref_known(v___x_3993_, 2);
v___x_4028_ = lean_array_get_size(v_a_4027_);
v___x_4029_ = lean_nat_dec_lt(v___x_3991_, v___x_4028_);
if (v___x_4029_ == 0)
{
lean_object* v___x_4030_; lean_object* v___x_4032_; 
lean_dec(v_a_4027_);
v___x_4030_ = lean_box(0);
if (v_isShared_3987_ == 0)
{
lean_ctor_set_tag(v___x_3986_, 1);
lean_ctor_set(v___x_3986_, 0, v___x_4030_);
v___x_4032_ = v___x_3986_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
else
{
lean_object* v___x_4034_; uint8_t v___x_4035_; 
lean_del_object(v___x_3986_);
v___x_4034_ = lean_box(0);
v___x_4035_ = lean_nat_dec_le(v___x_4028_, v___x_4028_);
if (v___x_4035_ == 0)
{
if (v___x_4029_ == 0)
{
lean_dec(v_a_4027_);
goto v___jp_3976_;
}
else
{
size_t v___x_4036_; size_t v___x_4037_; lean_object* v___x_4038_; 
v___x_4036_ = ((size_t)0ULL);
v___x_4037_ = lean_usize_of_nat(v___x_4028_);
v___x_4038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4027_, v___x_4036_, v___x_4037_, v___x_4034_, v___y_3974_);
lean_dec(v_a_4027_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_dec_ref_known(v___x_4038_, 1);
goto v___jp_3976_;
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
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
size_t v___x_4047_; size_t v___x_4048_; lean_object* v___x_4049_; 
v___x_4047_ = ((size_t)0ULL);
v___x_4048_ = lean_usize_of_nat(v___x_4028_);
v___x_4049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4027_, v___x_4047_, v___x_4048_, v___x_4034_, v___y_3974_);
lean_dec(v_a_4027_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_dec_ref_known(v___x_4049_, 1);
goto v___jp_3976_;
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
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
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_dec_ref(v_b_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_leanOpts_3970_);
v_a_4059_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_3983_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_3983_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
v___jp_3976_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = lean_box(0);
v___x_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
return v___x_3978_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object* v_upperBound_4067_, lean_object* v_fst_4068_, lean_object* v___x_4069_, lean_object* v_leanOpts_4070_, lean_object* v_a_4071_, lean_object* v_b_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4067_, v_fst_4068_, v___x_4069_, v_leanOpts_4070_, v_a_4071_, v_b_4072_, v___y_4073_, v___y_4074_);
lean_dec_ref(v___y_4074_);
lean_dec_ref(v___x_4069_);
lean_dec_ref(v_fst_4068_);
lean_dec(v_upperBound_4067_);
return v_res_4076_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(lean_object* v___x_4077_, lean_object* v_x_4078_){
_start:
{
lean_object* v_baseName_4079_; lean_object* v_name_4080_; uint8_t v___x_4081_; 
v_baseName_4079_ = lean_ctor_get(v_x_4078_, 1);
v_name_4080_ = lean_ctor_get(v___x_4077_, 0);
v___x_4081_ = lean_name_eq(v_baseName_4079_, v_name_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___x_4082_, lean_object* v_x_4083_){
_start:
{
uint8_t v_res_4084_; lean_object* v_r_4085_; 
v_res_4084_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(v___x_4082_, v_x_4083_);
lean_dec_ref(v_x_4083_);
lean_dec_ref(v___x_4082_);
v_r_4085_ = lean_box(v_res_4084_);
return v_r_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object* v_pkg_4086_, lean_object* v_leanOpts_4087_, uint8_t v_reconfigure_4088_, lean_object* v_as_4089_, size_t v_i_4090_, size_t v_stop_4091_, lean_object* v_b_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
uint8_t v___x_4099_; 
v___x_4099_ = lean_usize_dec_eq(v_i_4090_, v_stop_4091_);
if (v___x_4099_ == 0)
{
lean_object* v_ws_4100_; lean_object* v_depIdxs_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4216_; 
v_ws_4100_ = lean_ctor_get(v_b_4092_, 0);
v_depIdxs_4101_ = lean_ctor_get(v_b_4092_, 1);
v_isSharedCheck_4216_ = !lean_is_exclusive(v_b_4092_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4103_ = v_b_4092_;
v_isShared_4104_ = v_isSharedCheck_4216_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_depIdxs_4101_);
lean_inc(v_ws_4100_);
lean_dec(v_b_4092_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4216_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v_packages_4105_; size_t v___x_4106_; size_t v___x_4107_; lean_object* v___x_4108_; lean_object* v___f_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v_packages_4105_ = lean_ctor_get(v_ws_4100_, 4);
v___x_4106_ = ((size_t)1ULL);
v___x_4107_ = lean_usize_sub(v_i_4090_, v___x_4106_);
v___x_4108_ = lean_array_uget_borrowed(v_as_4089_, v___x_4107_);
lean_inc(v___x_4108_);
v___f_4109_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4109_, 0, v___x_4108_);
v___x_4110_ = lean_unsigned_to_nat(0u);
v___x_4111_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_4109_, v_packages_4105_, v___x_4110_);
if (lean_obj_tag(v___x_4111_) == 1)
{
lean_object* v_val_4112_; lean_object* v___x_4113_; lean_object* v___x_4115_; 
v_val_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_val_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v___x_4113_ = lean_array_push(v_depIdxs_4101_, v_val_4112_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 1, v___x_4113_);
v___x_4115_ = v___x_4103_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_ws_4100_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
v_i_4090_ = v___x_4107_;
v_b_4092_ = v___x_4115_;
goto _start;
}
}
else
{
lean_object* v_baseName_4118_; lean_object* v_name_4119_; lean_object* v_opts_4120_; uint8_t v___x_4121_; 
lean_inc_ref(v_packages_4105_);
lean_dec(v___x_4111_);
v_baseName_4118_ = lean_ctor_get(v_pkg_4086_, 1);
v_name_4119_ = lean_ctor_get(v___x_4108_, 0);
v_opts_4120_ = lean_ctor_get(v___x_4108_, 4);
v___x_4121_ = lean_name_eq(v_baseName_4118_, v_name_4119_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; 
lean_inc_ref(v___y_4094_);
lean_inc_ref(v_ws_4100_);
lean_inc(v___x_4108_);
lean_inc_ref(v_pkg_4086_);
v___x_4122_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_4086_, v___x_4108_, v_ws_4100_, v___y_4093_, v___y_4094_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4199_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4199_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4199_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v_fst_4127_; lean_object* v_snd_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_fst_4127_ = lean_ctor_get(v_a_4123_, 0);
lean_inc(v_fst_4127_);
v_snd_4128_ = lean_ctor_get(v_a_4123_, 1);
lean_inc(v_snd_4128_);
lean_dec(v_a_4123_);
v___x_4129_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_4087_);
lean_inc(v_opts_4120_);
v___x_4130_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_4100_, v_fst_4127_, v_opts_4120_, v_leanOpts_4087_, v_reconfigure_4088_, v___x_4129_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v_a_4132_; lean_object* v_wsIdx_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
lean_del_object(v___x_4125_);
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
v_a_4132_ = lean_ctor_get(v___x_4130_, 1);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4130_, 2);
v_wsIdx_4133_ = lean_array_get_size(v_packages_4105_);
lean_dec_ref(v_packages_4105_);
v___x_4134_ = lean_array_push(v_depIdxs_4101_, v_wsIdx_4133_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 1, v___x_4134_);
lean_ctor_set(v___x_4103_, 0, v_a_4131_);
v___x_4136_ = v___x_4103_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4131_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4137_; uint8_t v___x_4138_; 
v___x_4137_ = lean_array_get_size(v_a_4132_);
v___x_4138_ = lean_nat_dec_lt(v___x_4110_, v___x_4137_);
if (v___x_4138_ == 0)
{
lean_dec(v_a_4132_);
v_i_4090_ = v___x_4107_;
v_b_4092_ = v___x_4136_;
v___y_4093_ = v_snd_4128_;
goto _start;
}
else
{
lean_object* v___x_4140_; uint8_t v___x_4141_; 
v___x_4140_ = lean_box(0);
v___x_4141_ = lean_nat_dec_le(v___x_4137_, v___x_4137_);
if (v___x_4141_ == 0)
{
if (v___x_4138_ == 0)
{
lean_dec(v_a_4132_);
v_i_4090_ = v___x_4107_;
v_b_4092_ = v___x_4136_;
v___y_4093_ = v_snd_4128_;
goto _start;
}
else
{
size_t v___x_4143_; size_t v___x_4144_; lean_object* v___x_4145_; 
v___x_4143_ = ((size_t)0ULL);
v___x_4144_ = lean_usize_of_nat(v___x_4137_);
v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4132_, v___x_4143_, v___x_4144_, v___x_4140_, v___y_4094_);
lean_dec(v_a_4132_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_dec_ref_known(v___x_4145_, 1);
v_i_4090_ = v___x_4107_;
v_b_4092_ = v___x_4136_;
v___y_4093_ = v_snd_4128_;
goto _start;
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec_ref(v___x_4136_);
lean_dec(v_snd_4128_);
lean_dec_ref(v_leanOpts_4087_);
lean_dec_ref(v_pkg_4086_);
v_a_4147_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4145_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4145_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
else
{
size_t v___x_4155_; size_t v___x_4156_; lean_object* v___x_4157_; 
v___x_4155_ = ((size_t)0ULL);
v___x_4156_ = lean_usize_of_nat(v___x_4137_);
v___x_4157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4132_, v___x_4155_, v___x_4156_, v___x_4140_, v___y_4094_);
lean_dec(v_a_4132_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_dec_ref_known(v___x_4157_, 1);
v_i_4090_ = v___x_4107_;
v_b_4092_ = v___x_4136_;
v___y_4093_ = v_snd_4128_;
goto _start;
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec_ref(v___x_4136_);
lean_dec(v_snd_4128_);
lean_dec_ref(v_leanOpts_4087_);
lean_dec_ref(v_pkg_4086_);
v_a_4159_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4157_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4157_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
lean_dec(v_snd_4128_);
lean_dec_ref(v_packages_4105_);
lean_del_object(v___x_4103_);
lean_dec_ref(v_depIdxs_4101_);
lean_dec_ref(v_leanOpts_4087_);
lean_dec_ref(v_pkg_4086_);
v_a_4168_ = lean_ctor_get(v___x_4130_, 1);
lean_inc(v_a_4168_);
lean_dec_ref_known(v___x_4130_, 2);
v___x_4169_ = lean_array_get_size(v_a_4168_);
v___x_4170_ = lean_nat_dec_lt(v___x_4110_, v___x_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; lean_object* v___x_4173_; 
lean_dec(v_a_4168_);
v___x_4171_ = lean_box(0);
if (v_isShared_4126_ == 0)
{
lean_ctor_set_tag(v___x_4125_, 1);
lean_ctor_set(v___x_4125_, 0, v___x_4171_);
v___x_4173_ = v___x_4125_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
else
{
lean_object* v___x_4175_; uint8_t v___x_4176_; 
lean_del_object(v___x_4125_);
v___x_4175_ = lean_box(0);
v___x_4176_ = lean_nat_dec_le(v___x_4169_, v___x_4169_);
if (v___x_4176_ == 0)
{
if (v___x_4170_ == 0)
{
lean_dec(v_a_4168_);
goto v___jp_4096_;
}
else
{
size_t v___x_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
v___x_4177_ = ((size_t)0ULL);
v___x_4178_ = lean_usize_of_nat(v___x_4169_);
v___x_4179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4168_, v___x_4177_, v___x_4178_, v___x_4175_, v___y_4094_);
lean_dec(v_a_4168_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_dec_ref_known(v___x_4179_, 1);
goto v___jp_4096_;
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
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
size_t v___x_4188_; size_t v___x_4189_; lean_object* v___x_4190_; 
v___x_4188_ = ((size_t)0ULL);
v___x_4189_ = lean_usize_of_nat(v___x_4169_);
v___x_4190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4168_, v___x_4188_, v___x_4189_, v___x_4175_, v___y_4094_);
lean_dec(v_a_4168_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_dec_ref_known(v___x_4190_, 1);
goto v___jp_4096_;
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4190_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4190_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
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
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec_ref(v_packages_4105_);
lean_del_object(v___x_4103_);
lean_dec_ref(v_depIdxs_4101_);
lean_dec_ref(v_ws_4100_);
lean_dec_ref(v_leanOpts_4087_);
lean_dec_ref(v_pkg_4086_);
v_a_4200_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4122_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4122_);
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
else
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; uint8_t v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
lean_inc(v_baseName_4118_);
lean_dec_ref(v_packages_4105_);
lean_del_object(v___x_4103_);
lean_dec_ref(v_depIdxs_4101_);
lean_dec_ref(v_ws_4100_);
lean_dec(v___y_4093_);
lean_dec_ref(v_leanOpts_4087_);
lean_dec_ref(v_pkg_4086_);
v___x_4208_ = l_Lean_Name_toString(v_baseName_4118_, v___x_4099_);
v___x_4209_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_4210_ = lean_string_append(v___x_4208_, v___x_4209_);
v___x_4211_ = 3;
v___x_4212_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4212_, 0, v___x_4210_);
lean_ctor_set_uint8(v___x_4212_, sizeof(void*)*1, v___x_4211_);
lean_inc_ref(v___y_4094_);
v___x_4213_ = lean_apply_2(v___y_4094_, v___x_4212_, lean_box(0));
v___x_4214_ = lean_box(0);
v___x_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
return v___x_4215_;
}
}
}
}
else
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
lean_dec_ref(v_leanOpts_4087_);
lean_dec_ref(v_pkg_4086_);
v___x_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4217_, 0, v_b_4092_);
lean_ctor_set(v___x_4217_, 1, v___y_4093_);
v___x_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4217_);
return v___x_4218_;
}
v___jp_4096_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4097_ = lean_box(0);
v___x_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
return v___x_4098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___boxed(lean_object* v_pkg_4219_, lean_object* v_leanOpts_4220_, lean_object* v_reconfigure_4221_, lean_object* v_as_4222_, lean_object* v_i_4223_, lean_object* v_stop_4224_, lean_object* v_b_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
uint8_t v_reconfigure_boxed_4229_; size_t v_i_boxed_4230_; size_t v_stop_boxed_4231_; lean_object* v_res_4232_; 
v_reconfigure_boxed_4229_ = lean_unbox(v_reconfigure_4221_);
v_i_boxed_4230_ = lean_unbox_usize(v_i_4223_);
lean_dec(v_i_4223_);
v_stop_boxed_4231_ = lean_unbox_usize(v_stop_4224_);
lean_dec(v_stop_4224_);
v_res_4232_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4219_, v_leanOpts_4220_, v_reconfigure_boxed_4229_, v_as_4222_, v_i_boxed_4230_, v_stop_boxed_4231_, v_b_4225_, v___y_4226_, v___y_4227_);
lean_dec_ref(v___y_4227_);
lean_dec_ref(v_as_4222_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object* v_leanOpts_4233_, uint8_t v_reconfigure_4234_, lean_object* v_ws_4235_, lean_object* v_i_4236_, lean_object* v_next_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v_packages_4241_; lean_object* v_pkg_4242_; lean_object* v_ws_4244_; lean_object* v_depIdxs_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v_____x_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v_depConfigs_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v_s_4266_; lean_object* v___x_4267_; uint8_t v___x_4268_; 
v_packages_4241_ = lean_ctor_get(v_ws_4235_, 4);
v_pkg_4242_ = lean_array_fget(v_packages_4241_, v_i_4236_);
lean_dec(v_i_4236_);
v_depConfigs_4263_ = lean_ctor_get(v_pkg_4242_, 12);
v___x_4264_ = lean_array_get_size(v_depConfigs_4263_);
v___x_4265_ = lean_mk_empty_array_with_capacity(v___x_4264_);
lean_inc_ref(v___x_4265_);
lean_inc_ref(v_ws_4235_);
v_s_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_4266_, 0, v_ws_4235_);
lean_ctor_set(v_s_4266_, 1, v___x_4265_);
v___x_4267_ = lean_unsigned_to_nat(0u);
v___x_4268_ = lean_nat_dec_le(v___x_4264_, v___x_4264_);
if (v___x_4268_ == 0)
{
uint8_t v___x_4269_; 
v___x_4269_ = lean_nat_dec_lt(v___x_4267_, v___x_4264_);
if (v___x_4269_ == 0)
{
lean_object* v_ws_4270_; lean_object* v_packages_4271_; lean_object* v___x_4272_; uint8_t v___x_4273_; 
lean_dec_ref_known(v_s_4266_, 2);
v_ws_4270_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4235_, v_pkg_4242_, v___x_4265_);
v_packages_4271_ = lean_ctor_get(v_ws_4270_, 4);
lean_inc_ref(v_packages_4271_);
v___x_4272_ = lean_array_get_size(v_packages_4271_);
lean_dec_ref(v_packages_4271_);
v___x_4273_ = lean_nat_dec_lt(v_next_4237_, v___x_4272_);
if (v___x_4273_ == 0)
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
lean_dec(v_next_4237_);
lean_dec_ref(v_leanOpts_4233_);
v___x_4274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4274_, 0, v_ws_4270_);
lean_ctor_set(v___x_4274_, 1, v___y_4238_);
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
return v___x_4275_;
}
else
{
lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4276_ = lean_unsigned_to_nat(1u);
v___x_4277_ = lean_nat_add(v_next_4237_, v___x_4276_);
v_ws_4235_ = v_ws_4270_;
v_i_4236_ = v_next_4237_;
v_next_4237_ = v___x_4277_;
goto _start;
}
}
else
{
size_t v___x_4279_; size_t v___x_4280_; lean_object* v___x_4281_; 
lean_dec_ref(v___x_4265_);
lean_dec_ref(v_ws_4235_);
v___x_4279_ = lean_usize_of_nat(v___x_4264_);
v___x_4280_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4233_);
lean_inc(v_pkg_4242_);
v___x_4281_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4242_, v_leanOpts_4233_, v_reconfigure_4234_, v_depConfigs_4263_, v___x_4279_, v___x_4280_, v_s_4266_, v___y_4238_, v___y_4239_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_a_4282_; lean_object* v_fst_4283_; lean_object* v_snd_4284_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v___x_4281_, 1);
v_fst_4283_ = lean_ctor_get(v_a_4282_, 0);
lean_inc(v_fst_4283_);
v_snd_4284_ = lean_ctor_get(v_a_4282_, 1);
lean_inc(v_snd_4284_);
lean_dec(v_a_4282_);
v_____x_4258_ = v_fst_4283_;
v___y_4259_ = v_snd_4284_;
v___y_4260_ = v___y_4239_;
goto v___jp_4257_;
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_dec(v_pkg_4242_);
lean_dec(v_next_4237_);
lean_dec_ref(v_leanOpts_4233_);
v_a_4285_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4281_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4281_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
}
else
{
uint8_t v___x_4293_; 
v___x_4293_ = lean_nat_dec_lt(v___x_4267_, v___x_4264_);
if (v___x_4293_ == 0)
{
lean_dec_ref_known(v_s_4266_, 2);
v_ws_4244_ = v_ws_4235_;
v_depIdxs_4245_ = v___x_4265_;
v___y_4246_ = v___y_4238_;
v___y_4247_ = v___y_4239_;
goto v___jp_4243_;
}
else
{
size_t v___x_4294_; size_t v___x_4295_; lean_object* v___x_4296_; 
lean_dec_ref(v___x_4265_);
lean_dec_ref(v_ws_4235_);
v___x_4294_ = lean_usize_of_nat(v___x_4264_);
v___x_4295_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4233_);
lean_inc(v_pkg_4242_);
v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4242_, v_leanOpts_4233_, v_reconfigure_4234_, v_depConfigs_4263_, v___x_4294_, v___x_4295_, v_s_4266_, v___y_4238_, v___y_4239_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v_fst_4298_; lean_object* v_snd_4299_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref_known(v___x_4296_, 1);
v_fst_4298_ = lean_ctor_get(v_a_4297_, 0);
lean_inc(v_fst_4298_);
v_snd_4299_ = lean_ctor_get(v_a_4297_, 1);
lean_inc(v_snd_4299_);
lean_dec(v_a_4297_);
v_____x_4258_ = v_fst_4298_;
v___y_4259_ = v_snd_4299_;
v___y_4260_ = v___y_4239_;
goto v___jp_4257_;
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec(v_pkg_4242_);
lean_dec(v_next_4237_);
lean_dec_ref(v_leanOpts_4233_);
v_a_4300_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4296_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4296_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
}
v___jp_4243_:
{
lean_object* v_ws_4248_; lean_object* v_packages_4249_; lean_object* v___x_4250_; uint8_t v___x_4251_; 
v_ws_4248_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4244_, v_pkg_4242_, v_depIdxs_4245_);
v_packages_4249_ = lean_ctor_get(v_ws_4248_, 4);
lean_inc_ref(v_packages_4249_);
v___x_4250_ = lean_array_get_size(v_packages_4249_);
lean_dec_ref(v_packages_4249_);
v___x_4251_ = lean_nat_dec_lt(v_next_4237_, v___x_4250_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
lean_dec(v_next_4237_);
lean_dec_ref(v_leanOpts_4233_);
v___x_4252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4252_, 0, v_ws_4248_);
lean_ctor_set(v___x_4252_, 1, v___y_4246_);
v___x_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4252_);
return v___x_4253_;
}
else
{
lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4254_ = lean_unsigned_to_nat(1u);
v___x_4255_ = lean_nat_add(v_next_4237_, v___x_4254_);
v_ws_4235_ = v_ws_4248_;
v_i_4236_ = v_next_4237_;
v_next_4237_ = v___x_4255_;
v___y_4238_ = v___y_4246_;
v___y_4239_ = v___y_4247_;
goto _start;
}
}
v___jp_4257_:
{
lean_object* v_ws_4261_; lean_object* v_depIdxs_4262_; 
v_ws_4261_ = lean_ctor_get(v_____x_4258_, 0);
lean_inc_ref(v_ws_4261_);
v_depIdxs_4262_ = lean_ctor_get(v_____x_4258_, 1);
lean_inc_ref(v_depIdxs_4262_);
lean_dec_ref(v_____x_4258_);
v_ws_4244_ = v_ws_4261_;
v_depIdxs_4245_ = v_depIdxs_4262_;
v___y_4246_ = v___y_4259_;
v___y_4247_ = v___y_4260_;
goto v___jp_4243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object* v_leanOpts_4308_, lean_object* v_reconfigure_4309_, lean_object* v_ws_4310_, lean_object* v_i_4311_, lean_object* v_next_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
uint8_t v_reconfigure_boxed_4316_; lean_object* v_res_4317_; 
v_reconfigure_boxed_4316_ = lean_unbox(v_reconfigure_4309_);
v_res_4317_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4308_, v_reconfigure_boxed_4316_, v_ws_4310_, v_i_4311_, v_next_4312_, v___y_4313_, v___y_4314_);
lean_dec_ref(v___y_4314_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4320_, lean_object* v_toUpdate_4321_, lean_object* v_leanOpts_4322_, uint8_t v_updateToolchain_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4326_ = lean_box(1);
v___x_4327_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4324_, v_ws_4320_, v_toUpdate_4321_, v___x_4326_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v_snd_4329_; uint8_t v___x_4330_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4328_);
lean_dec_ref_known(v___x_4327_, 1);
v_snd_4329_ = lean_ctor_get(v_a_4328_, 1);
lean_inc(v_snd_4329_);
lean_dec(v_a_4328_);
v___x_4330_ = 1;
if (v_updateToolchain_4323_ == 0)
{
lean_object* v_packages_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v_wsIdx_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v_packages_4331_ = lean_ctor_get(v_ws_4320_, 4);
v___x_4332_ = lean_unsigned_to_nat(0u);
v___x_4333_ = lean_array_fget_borrowed(v_packages_4331_, v___x_4332_);
v_wsIdx_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_wsIdx_4334_);
v___x_4335_ = lean_array_get_size(v_packages_4331_);
v___x_4336_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4322_, v___x_4330_, v_ws_4320_, v_wsIdx_4334_, v___x_4335_, v_snd_4329_, v_a_4324_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4354_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4339_ = v___x_4336_;
v_isShared_4340_ = v_isSharedCheck_4354_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4336_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4354_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v_fst_4341_; lean_object* v_snd_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4353_; 
v_fst_4341_ = lean_ctor_get(v_a_4337_, 0);
v_snd_4342_ = lean_ctor_get(v_a_4337_, 1);
v_isSharedCheck_4353_ = !lean_is_exclusive(v_a_4337_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4344_ = v_a_4337_;
v_isShared_4345_ = v_isSharedCheck_4353_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_snd_4342_);
lean_inc(v_fst_4341_);
lean_dec(v_a_4337_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4353_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4346_; lean_object* v___x_4348_; 
v___x_4346_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4341_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v___x_4346_);
v___x_4348_ = v___x_4344_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4346_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v_snd_4342_);
v___x_4348_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
lean_object* v___x_4350_; 
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 0, v___x_4348_);
v___x_4350_ = v___x_4339_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
}
else
{
return v___x_4336_;
}
}
else
{
lean_object* v_packages_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v_depConfigs_4358_; lean_object* v___x_4359_; lean_object* v___f_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v_packages_4355_ = lean_ctor_get(v_ws_4320_, 4);
lean_inc_ref(v_packages_4355_);
v___x_4356_ = lean_unsigned_to_nat(0u);
v___x_4357_ = lean_array_fget_borrowed(v_packages_4355_, v___x_4356_);
v_depConfigs_4358_ = lean_ctor_get(v___x_4357_, 12);
v___x_4359_ = lean_box(v_updateToolchain_4323_);
lean_inc_ref(v_ws_4320_);
lean_inc(v___x_4357_);
v___f_4360_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4360_, 0, v___x_4357_);
lean_closure_set(v___f_4360_, 1, v___x_4359_);
lean_closure_set(v___f_4360_, 2, v_ws_4320_);
v___x_4361_ = lean_array_get_size(v_depConfigs_4358_);
lean_inc_ref(v_depConfigs_4358_);
v___x_4362_ = l_Array_reverse___redArg(v_depConfigs_4358_);
v___x_4363_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4364_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4361_, v___f_4360_, v___x_4362_, v___x_4356_, v___x_4363_, v_snd_4329_, v_a_4324_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v_fst_4366_; lean_object* v_snd_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4439_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___x_4364_, 1);
v_fst_4366_ = lean_ctor_get(v_a_4365_, 0);
v_snd_4367_ = lean_ctor_get(v_a_4365_, 1);
v_isSharedCheck_4439_ = !lean_is_exclusive(v_a_4365_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4369_ = v_a_4365_;
v_isShared_4370_ = v_isSharedCheck_4439_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_snd_4367_);
lean_inc(v_fst_4366_);
lean_dec(v_a_4365_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4439_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4371_; 
lean_inc_ref(v_ws_4320_);
v___x_4371_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4324_, v_ws_4320_, v_fst_4366_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v___x_4372_; 
lean_dec_ref_known(v___x_4371_, 1);
lean_inc_ref(v_leanOpts_4322_);
v___x_4372_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4361_, v_fst_4366_, v___x_4362_, v_leanOpts_4322_, v___x_4356_, v_ws_4320_, v_snd_4367_, v_a_4324_);
lean_dec_ref(v___x_4362_);
lean_dec(v_fst_4366_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4422_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4375_ = v___x_4372_;
v_isShared_4376_ = v_isSharedCheck_4422_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4372_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4422_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v_fst_4377_; lean_object* v_snd_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4421_; 
v_fst_4377_ = lean_ctor_get(v_a_4373_, 0);
v_snd_4378_ = lean_ctor_get(v_a_4373_, 1);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_a_4373_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4380_ = v_a_4373_;
v_isShared_4381_ = v_isSharedCheck_4421_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_snd_4378_);
lean_inc(v_fst_4377_);
lean_dec(v_a_4373_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4421_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v_packages_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4388_; 
v_packages_4382_ = lean_ctor_get(v_fst_4377_, 4);
v___x_4383_ = lean_array_get_size(v_packages_4355_);
lean_dec_ref(v_packages_4355_);
v___x_4384_ = lean_array_get_size(v_packages_4382_);
v___x_4385_ = lean_array_fget(v_packages_4382_, v___x_4356_);
v___x_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4383_);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 1, v___x_4384_);
lean_ctor_set(v___x_4369_, 0, v___x_4386_);
v___x_4388_ = v___x_4369_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4386_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v___x_4384_);
v___x_4388_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; uint8_t v___x_4391_; 
v___x_4389_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4388_, v___x_4363_);
v___x_4390_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4377_, v___x_4385_, v___x_4389_);
v___x_4391_ = lean_nat_dec_eq(v___x_4383_, v___x_4384_);
if (v___x_4391_ == 0)
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
lean_del_object(v___x_4380_);
lean_del_object(v___x_4375_);
v___x_4392_ = lean_unsigned_to_nat(1u);
v___x_4393_ = lean_nat_add(v___x_4383_, v___x_4392_);
v___x_4394_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4322_, v___x_4330_, v___x_4390_, v___x_4383_, v___x_4393_, v_snd_4378_, v_a_4324_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4412_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4397_ = v___x_4394_;
v_isShared_4398_ = v_isSharedCheck_4412_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4394_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4412_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v_fst_4399_; lean_object* v_snd_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4411_; 
v_fst_4399_ = lean_ctor_get(v_a_4395_, 0);
v_snd_4400_ = lean_ctor_get(v_a_4395_, 1);
v_isSharedCheck_4411_ = !lean_is_exclusive(v_a_4395_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4402_ = v_a_4395_;
v_isShared_4403_ = v_isSharedCheck_4411_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_snd_4400_);
lean_inc(v_fst_4399_);
lean_dec(v_a_4395_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4411_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; lean_object* v___x_4406_; 
v___x_4404_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4399_);
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 0, v___x_4404_);
v___x_4406_ = v___x_4402_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4404_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v_snd_4400_);
v___x_4406_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4408_; 
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 0, v___x_4406_);
v___x_4408_ = v___x_4397_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
else
{
return v___x_4394_;
}
}
else
{
lean_object* v___x_4413_; lean_object* v___x_4415_; 
lean_dec_ref(v_leanOpts_4322_);
v___x_4413_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4390_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 0, v___x_4413_);
v___x_4415_ = v___x_4380_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_snd_4378_);
v___x_4415_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4417_; 
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 0, v___x_4415_);
v___x_4417_ = v___x_4375_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4415_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_del_object(v___x_4369_);
lean_dec_ref(v_packages_4355_);
lean_dec_ref(v_leanOpts_4322_);
v_a_4423_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4372_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4372_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_del_object(v___x_4369_);
lean_dec(v_snd_4367_);
lean_dec(v_fst_4366_);
lean_dec_ref(v___x_4362_);
lean_dec_ref(v_packages_4355_);
lean_dec_ref(v_leanOpts_4322_);
lean_dec_ref(v_ws_4320_);
v_a_4431_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4371_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4371_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec_ref(v___x_4362_);
lean_dec_ref(v_packages_4355_);
lean_dec_ref(v_leanOpts_4322_);
lean_dec_ref(v_ws_4320_);
v_a_4440_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4364_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4364_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
}
else
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4455_; 
lean_dec_ref(v_leanOpts_4322_);
lean_dec_ref(v_ws_4320_);
v_a_4448_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4450_ = v___x_4327_;
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4327_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4456_, lean_object* v_toUpdate_4457_, lean_object* v_leanOpts_4458_, lean_object* v_updateToolchain_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
uint8_t v_updateToolchain_boxed_4462_; lean_object* v_res_4463_; 
v_updateToolchain_boxed_4462_ = lean_unbox(v_updateToolchain_4459_);
v_res_4463_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4456_, v_toUpdate_4457_, v_leanOpts_4458_, v_updateToolchain_boxed_4462_, v_a_4460_);
lean_dec_ref(v_a_4460_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_leanOpts_4464_, uint8_t v_reconfigure_4465_, lean_object* v_ws_4466_, lean_object* v_i_4467_, lean_object* v_i__lt_4468_, lean_object* v_next_4469_, lean_object* v_lt__next_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v___x_4474_; 
v___x_4474_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4464_, v_reconfigure_4465_, v_ws_4466_, v_i_4467_, v_next_4469_, v___y_4471_, v___y_4472_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_leanOpts_4475_, lean_object* v_reconfigure_4476_, lean_object* v_ws_4477_, lean_object* v_i_4478_, lean_object* v_i__lt_4479_, lean_object* v_next_4480_, lean_object* v_lt__next_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
uint8_t v_reconfigure_boxed_4485_; lean_object* v_res_4486_; 
v_reconfigure_boxed_4485_ = lean_unbox(v_reconfigure_4476_);
v_res_4486_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4475_, v_reconfigure_boxed_4485_, v_ws_4477_, v_i_4478_, v_i__lt_4479_, v_next_4480_, v_lt__next_4481_, v___y_4482_, v___y_4483_);
lean_dec_ref(v___y_4483_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_00_u03b1_4487_, lean_object* v_00_u03b2_4488_, lean_object* v_n_4489_, lean_object* v_f_4490_, lean_object* v_xs_4491_, lean_object* v_k_4492_, lean_object* v_h_4493_, lean_object* v_acc_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4489_, v_f_4490_, v_xs_4491_, v_k_4492_, v_acc_4494_, v___y_4495_, v___y_4496_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_00_u03b1_4499_, lean_object* v_00_u03b2_4500_, lean_object* v_n_4501_, lean_object* v_f_4502_, lean_object* v_xs_4503_, lean_object* v_k_4504_, lean_object* v_h_4505_, lean_object* v_acc_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_00_u03b1_4499_, v_00_u03b2_4500_, v_n_4501_, v_f_4502_, v_xs_4503_, v_k_4504_, v_h_4505_, v_acc_4506_, v___y_4507_, v___y_4508_);
lean_dec_ref(v___y_4508_);
lean_dec_ref(v_xs_4503_);
lean_dec(v_n_4501_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_inst_4511_, lean_object* v_R_4512_, lean_object* v_a_4513_, lean_object* v_b_4514_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_a_4513_, v_b_4514_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_upperBound_4516_, lean_object* v_fst_4517_, lean_object* v___x_4518_, lean_object* v_leanOpts_4519_, lean_object* v_inst_4520_, lean_object* v_R_4521_, lean_object* v_a_4522_, lean_object* v_b_4523_, lean_object* v_c_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v___x_4528_; 
v___x_4528_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4516_, v_fst_4517_, v___x_4518_, v_leanOpts_4519_, v_a_4522_, v_b_4523_, v___y_4525_, v___y_4526_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_upperBound_4529_, lean_object* v_fst_4530_, lean_object* v___x_4531_, lean_object* v_leanOpts_4532_, lean_object* v_inst_4533_, lean_object* v_R_4534_, lean_object* v_a_4535_, lean_object* v_b_4536_, lean_object* v_c_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4529_, v_fst_4530_, v___x_4531_, v_leanOpts_4532_, v_inst_4533_, v_R_4534_, v_a_4535_, v_b_4536_, v_c_4537_, v___y_4538_, v___y_4539_);
lean_dec_ref(v___y_4539_);
lean_dec_ref(v___x_4531_);
lean_dec_ref(v_fst_4530_);
lean_dec(v_upperBound_4529_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_start_4542_, lean_object* v_pkg_4543_, lean_object* v_leanOpts_4544_, uint8_t v_reconfigure_4545_, lean_object* v_as_4546_, size_t v_i_4547_, size_t v_stop_4548_, lean_object* v_b_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4543_, v_leanOpts_4544_, v_reconfigure_4545_, v_as_4546_, v_i_4547_, v_stop_4548_, v_b_4549_, v___y_4550_, v___y_4551_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_start_4554_, lean_object* v_pkg_4555_, lean_object* v_leanOpts_4556_, lean_object* v_reconfigure_4557_, lean_object* v_as_4558_, lean_object* v_i_4559_, lean_object* v_stop_4560_, lean_object* v_b_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
uint8_t v_reconfigure_boxed_4565_; size_t v_i_boxed_4566_; size_t v_stop_boxed_4567_; lean_object* v_res_4568_; 
v_reconfigure_boxed_4565_ = lean_unbox(v_reconfigure_4557_);
v_i_boxed_4566_ = lean_unbox_usize(v_i_4559_);
lean_dec(v_i_4559_);
v_stop_boxed_4567_ = lean_unbox_usize(v_stop_4560_);
lean_dec(v_stop_4560_);
v_res_4568_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_start_4554_, v_pkg_4555_, v_leanOpts_4556_, v_reconfigure_boxed_4565_, v_as_4558_, v_i_boxed_4566_, v_stop_boxed_4567_, v_b_4561_, v___y_4562_, v___y_4563_);
lean_dec_ref(v___y_4563_);
lean_dec_ref(v_as_4558_);
lean_dec(v_start_4554_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_4569_, lean_object* v_msg_4570_){
_start:
{
lean_object* v___x_4571_; 
v___x_4571_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v_msg_4570_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object* v_00_u03b2_4572_, lean_object* v_k_4573_, lean_object* v_v_4574_, lean_object* v_t_4575_){
_start:
{
lean_object* v___x_4576_; 
v___x_4576_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_4573_, v_v_4574_, v_t_4575_);
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object* v_init_4577_, lean_object* v_t_4578_){
_start:
{
lean_object* v___x_4579_; 
v___x_4579_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_4577_, v_t_4578_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4580_, lean_object* v_as_4581_, size_t v_i_4582_, size_t v_stop_4583_, lean_object* v_b_4584_){
_start:
{
lean_object* v___y_4586_; uint8_t v___x_4590_; 
v___x_4590_ = lean_usize_dec_eq(v_i_4582_, v_stop_4583_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; lean_object* v_baseName_4592_; lean_object* v_relConfigFile_4593_; lean_object* v_relManifestFile_4594_; lean_object* v___x_4595_; 
v___x_4591_ = lean_array_uget_borrowed(v_as_4581_, v_i_4582_);
v_baseName_4592_ = lean_ctor_get(v___x_4591_, 1);
v_relConfigFile_4593_ = lean_ctor_get(v___x_4591_, 8);
v_relManifestFile_4594_ = lean_ctor_get(v___x_4591_, 9);
v___x_4595_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4580_, v_baseName_4592_);
if (lean_obj_tag(v___x_4595_) == 0)
{
v___y_4586_ = v_b_4584_;
goto v___jp_4585_;
}
else
{
lean_object* v_val_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4617_; 
v_val_4596_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4598_ = v___x_4595_;
v_isShared_4599_ = v_isSharedCheck_4617_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_val_4596_);
lean_dec(v___x_4595_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4617_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v_name_4600_; lean_object* v_scope_4601_; uint8_t v_inherited_4602_; lean_object* v_src_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4614_; 
v_name_4600_ = lean_ctor_get(v_val_4596_, 0);
v_scope_4601_ = lean_ctor_get(v_val_4596_, 1);
v_inherited_4602_ = lean_ctor_get_uint8(v_val_4596_, sizeof(void*)*5);
v_src_4603_ = lean_ctor_get(v_val_4596_, 4);
v_isSharedCheck_4614_ = !lean_is_exclusive(v_val_4596_);
if (v_isSharedCheck_4614_ == 0)
{
lean_object* v_unused_4615_; lean_object* v_unused_4616_; 
v_unused_4615_ = lean_ctor_get(v_val_4596_, 3);
lean_dec(v_unused_4615_);
v_unused_4616_ = lean_ctor_get(v_val_4596_, 2);
lean_dec(v_unused_4616_);
v___x_4605_ = v_val_4596_;
v_isShared_4606_ = v_isSharedCheck_4614_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_src_4603_);
lean_inc(v_scope_4601_);
lean_inc(v_name_4600_);
lean_dec(v_val_4596_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4614_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
lean_inc_ref(v_relManifestFile_4594_);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 0, v_relManifestFile_4594_);
v___x_4608_ = v___x_4598_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_relManifestFile_4594_);
v___x_4608_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
lean_object* v___x_4610_; 
lean_inc_ref(v_relConfigFile_4593_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 3, v___x_4608_);
lean_ctor_set(v___x_4605_, 2, v_relConfigFile_4593_);
v___x_4610_ = v___x_4605_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_name_4600_);
lean_ctor_set(v_reuseFailAlloc_4612_, 1, v_scope_4601_);
lean_ctor_set(v_reuseFailAlloc_4612_, 2, v_relConfigFile_4593_);
lean_ctor_set(v_reuseFailAlloc_4612_, 3, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4612_, 4, v_src_4603_);
lean_ctor_set_uint8(v_reuseFailAlloc_4612_, sizeof(void*)*5, v_inherited_4602_);
v___x_4610_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
lean_object* v___x_4611_; 
v___x_4611_ = lean_array_push(v_b_4584_, v___x_4610_);
v___y_4586_ = v___x_4611_;
goto v___jp_4585_;
}
}
}
}
}
}
else
{
return v_b_4584_;
}
v___jp_4585_:
{
size_t v___x_4587_; size_t v___x_4588_; 
v___x_4587_ = ((size_t)1ULL);
v___x_4588_ = lean_usize_add(v_i_4582_, v___x_4587_);
v_i_4582_ = v___x_4588_;
v_b_4584_ = v___y_4586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4618_, lean_object* v_as_4619_, lean_object* v_i_4620_, lean_object* v_stop_4621_, lean_object* v_b_4622_){
_start:
{
size_t v_i_boxed_4623_; size_t v_stop_boxed_4624_; lean_object* v_res_4625_; 
v_i_boxed_4623_ = lean_unbox_usize(v_i_4620_);
lean_dec(v_i_4620_);
v_stop_boxed_4624_ = lean_unbox_usize(v_stop_4621_);
lean_dec(v_stop_4621_);
v_res_4625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4618_, v_as_4619_, v_i_boxed_4623_, v_stop_boxed_4624_, v_b_4622_);
lean_dec_ref(v_as_4619_);
lean_dec(v_entries_4618_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4626_, lean_object* v_entries_4627_){
_start:
{
lean_object* v_packages_4629_; lean_object* v___y_4631_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; uint8_t v___x_4649_; 
v_packages_4629_ = lean_ctor_get(v_ws_4626_, 4);
v___x_4646_ = lean_unsigned_to_nat(0u);
v___x_4647_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4648_ = lean_array_get_size(v_packages_4629_);
v___x_4649_ = lean_nat_dec_lt(v___x_4646_, v___x_4648_);
if (v___x_4649_ == 0)
{
v___y_4631_ = v___x_4647_;
goto v___jp_4630_;
}
else
{
uint8_t v___x_4650_; 
v___x_4650_ = lean_nat_dec_le(v___x_4648_, v___x_4648_);
if (v___x_4650_ == 0)
{
if (v___x_4649_ == 0)
{
v___y_4631_ = v___x_4647_;
goto v___jp_4630_;
}
else
{
size_t v___x_4651_; size_t v___x_4652_; lean_object* v___x_4653_; 
v___x_4651_ = ((size_t)0ULL);
v___x_4652_ = lean_usize_of_nat(v___x_4648_);
v___x_4653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4627_, v_packages_4629_, v___x_4651_, v___x_4652_, v___x_4647_);
v___y_4631_ = v___x_4653_;
goto v___jp_4630_;
}
}
else
{
size_t v___x_4654_; size_t v___x_4655_; lean_object* v___x_4656_; 
v___x_4654_ = ((size_t)0ULL);
v___x_4655_ = lean_usize_of_nat(v___x_4648_);
v___x_4656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4627_, v_packages_4629_, v___x_4654_, v___x_4655_, v___x_4647_);
v___y_4631_ = v___x_4656_;
goto v___jp_4630_;
}
}
v___jp_4630_:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v_config_4634_; lean_object* v_baseName_4635_; lean_object* v_dir_4636_; lean_object* v_relManifestFile_4637_; lean_object* v_toWorkspaceConfig_4638_; uint8_t v_fixedToolchain_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v_manifest_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4632_ = lean_unsigned_to_nat(0u);
v___x_4633_ = lean_array_fget_borrowed(v_packages_4629_, v___x_4632_);
v_config_4634_ = lean_ctor_get(v___x_4633_, 6);
v_baseName_4635_ = lean_ctor_get(v___x_4633_, 1);
v_dir_4636_ = lean_ctor_get(v___x_4633_, 4);
v_relManifestFile_4637_ = lean_ctor_get(v___x_4633_, 9);
v_toWorkspaceConfig_4638_ = lean_ctor_get(v_config_4634_, 0);
v_fixedToolchain_4639_ = lean_ctor_get_uint8(v_config_4634_, sizeof(void*)*27 + 6);
v___x_4640_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4638_);
v___x_4641_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4638_);
v___x_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
lean_inc(v_baseName_4635_);
v_manifest_4643_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4643_, 0, v_baseName_4635_);
lean_ctor_set(v_manifest_4643_, 1, v___x_4640_);
lean_ctor_set(v_manifest_4643_, 2, v___x_4642_);
lean_ctor_set(v_manifest_4643_, 3, v___y_4631_);
lean_ctor_set_uint8(v_manifest_4643_, sizeof(void*)*4, v_fixedToolchain_4639_);
lean_inc_ref(v_relManifestFile_4637_);
lean_inc_ref(v_dir_4636_);
v___x_4644_ = l_Lake_joinRelative(v_dir_4636_, v_relManifestFile_4637_);
v___x_4645_ = l_Lake_Manifest_save(v_manifest_4643_, v___x_4644_);
lean_dec_ref(v___x_4644_);
return v___x_4645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4657_, lean_object* v_entries_4658_, lean_object* v_a_4659_){
_start:
{
lean_object* v_res_4660_; 
v_res_4660_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4657_, v_entries_4658_);
lean_dec(v_entries_4658_);
lean_dec_ref(v_ws_4657_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4661_, lean_object* v_as_4662_, size_t v_i_4663_, size_t v_stop_4664_, lean_object* v_b_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v_a_4670_; lean_object* v___y_4675_; uint8_t v___x_4680_; 
v___x_4680_ = lean_usize_dec_eq(v_i_4663_, v_stop_4664_);
if (v___x_4680_ == 0)
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_9317__overap_4683_; lean_object* v___x_4684_; 
v___x_4681_ = lean_unsigned_to_nat(0u);
v___x_4682_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_9317__overap_4683_ = lean_array_uget_borrowed(v_as_4662_, v_i_4663_);
lean_inc(v___x_9317__overap_4683_);
lean_inc(v___y_4666_);
lean_inc_ref(v_pkg_4661_);
v___x_4684_ = lean_apply_4(v___x_9317__overap_4683_, v_pkg_4661_, v___y_4666_, v___x_4682_, lean_box(0));
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v_a_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
v_a_4686_ = lean_ctor_get(v___x_4684_, 1);
lean_inc(v_a_4686_);
lean_dec_ref_known(v___x_4684_, 2);
v___x_4687_ = lean_array_get_size(v_a_4686_);
v___x_4688_ = lean_nat_dec_lt(v___x_4681_, v___x_4687_);
if (v___x_4688_ == 0)
{
lean_dec(v_a_4686_);
v_a_4670_ = v_a_4685_;
goto v___jp_4669_;
}
else
{
lean_object* v___x_4689_; uint8_t v___x_4690_; 
v___x_4689_ = lean_box(0);
v___x_4690_ = lean_nat_dec_le(v___x_4687_, v___x_4687_);
if (v___x_4690_ == 0)
{
if (v___x_4688_ == 0)
{
lean_dec(v_a_4686_);
v_a_4670_ = v_a_4685_;
goto v___jp_4669_;
}
else
{
size_t v___x_4691_; size_t v___x_4692_; lean_object* v___x_4693_; 
v___x_4691_ = ((size_t)0ULL);
v___x_4692_ = lean_usize_of_nat(v___x_4687_);
v___x_4693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4686_, v___x_4691_, v___x_4692_, v___x_4689_, v___y_4667_);
lean_dec(v_a_4686_);
if (lean_obj_tag(v___x_4693_) == 0)
{
lean_dec_ref_known(v___x_4693_, 1);
v_a_4670_ = v_a_4685_;
goto v___jp_4669_;
}
else
{
lean_dec(v_a_4685_);
v___y_4675_ = v___x_4693_;
goto v___jp_4674_;
}
}
}
else
{
size_t v___x_4694_; size_t v___x_4695_; lean_object* v___x_4696_; 
v___x_4694_ = ((size_t)0ULL);
v___x_4695_ = lean_usize_of_nat(v___x_4687_);
v___x_4696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4686_, v___x_4694_, v___x_4695_, v___x_4689_, v___y_4667_);
lean_dec(v_a_4686_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_dec_ref_known(v___x_4696_, 1);
v_a_4670_ = v_a_4685_;
goto v___jp_4669_;
}
else
{
lean_dec(v_a_4685_);
v___y_4675_ = v___x_4696_;
goto v___jp_4674_;
}
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4698_; uint8_t v___x_4699_; 
v_a_4697_ = lean_ctor_get(v___x_4684_, 1);
lean_inc(v_a_4697_);
lean_dec_ref_known(v___x_4684_, 2);
v___x_4698_ = lean_array_get_size(v_a_4697_);
v___x_4699_ = lean_nat_dec_lt(v___x_4681_, v___x_4698_);
if (v___x_4699_ == 0)
{
lean_object* v___x_4700_; lean_object* v___x_4701_; 
lean_dec(v_a_4697_);
lean_dec_ref(v_pkg_4661_);
v___x_4700_ = lean_box(0);
v___x_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4701_, 0, v___x_4700_);
return v___x_4701_;
}
else
{
lean_object* v___x_4702_; uint8_t v___x_4703_; 
v___x_4702_ = lean_box(0);
v___x_4703_ = lean_nat_dec_le(v___x_4698_, v___x_4698_);
if (v___x_4703_ == 0)
{
if (v___x_4699_ == 0)
{
lean_dec(v_a_4697_);
lean_dec_ref(v_pkg_4661_);
goto v___jp_4677_;
}
else
{
size_t v___x_4704_; size_t v___x_4705_; lean_object* v___x_4706_; 
v___x_4704_ = ((size_t)0ULL);
v___x_4705_ = lean_usize_of_nat(v___x_4698_);
v___x_4706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4697_, v___x_4704_, v___x_4705_, v___x_4702_, v___y_4667_);
lean_dec(v_a_4697_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_dec_ref_known(v___x_4706_, 1);
lean_dec_ref(v_pkg_4661_);
goto v___jp_4677_;
}
else
{
v___y_4675_ = v___x_4706_;
goto v___jp_4674_;
}
}
}
else
{
size_t v___x_4707_; size_t v___x_4708_; lean_object* v___x_4709_; 
v___x_4707_ = ((size_t)0ULL);
v___x_4708_ = lean_usize_of_nat(v___x_4698_);
v___x_4709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4697_, v___x_4707_, v___x_4708_, v___x_4702_, v___y_4667_);
lean_dec(v_a_4697_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_dec_ref_known(v___x_4709_, 1);
lean_dec_ref(v_pkg_4661_);
goto v___jp_4677_;
}
else
{
v___y_4675_ = v___x_4709_;
goto v___jp_4674_;
}
}
}
}
}
else
{
lean_object* v___x_4710_; 
lean_dec_ref(v_pkg_4661_);
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v_b_4665_);
return v___x_4710_;
}
v___jp_4669_:
{
size_t v___x_4671_; size_t v___x_4672_; 
v___x_4671_ = ((size_t)1ULL);
v___x_4672_ = lean_usize_add(v_i_4663_, v___x_4671_);
v_i_4663_ = v___x_4672_;
v_b_4665_ = v_a_4670_;
goto _start;
}
v___jp_4674_:
{
if (lean_obj_tag(v___y_4675_) == 0)
{
lean_object* v_a_4676_; 
v_a_4676_ = lean_ctor_get(v___y_4675_, 0);
lean_inc(v_a_4676_);
lean_dec_ref_known(v___y_4675_, 1);
v_a_4670_ = v_a_4676_;
goto v___jp_4669_;
}
else
{
lean_dec_ref(v_pkg_4661_);
return v___y_4675_;
}
}
v___jp_4677_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4678_ = lean_box(0);
v___x_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
return v___x_4679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4711_, lean_object* v_as_4712_, lean_object* v_i_4713_, lean_object* v_stop_4714_, lean_object* v_b_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
size_t v_i_boxed_4719_; size_t v_stop_boxed_4720_; lean_object* v_res_4721_; 
v_i_boxed_4719_ = lean_unbox_usize(v_i_4713_);
lean_dec(v_i_4713_);
v_stop_boxed_4720_ = lean_unbox_usize(v_stop_4714_);
lean_dec(v_stop_4714_);
v_res_4721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4711_, v_as_4712_, v_i_boxed_4719_, v_stop_boxed_4720_, v_b_4715_, v___y_4716_, v___y_4717_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v_as_4712_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v_baseName_4727_; lean_object* v_postUpdateHooks_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; uint8_t v___x_4731_; 
v_baseName_4727_ = lean_ctor_get(v_pkg_4723_, 1);
v_postUpdateHooks_4728_ = lean_ctor_get(v_pkg_4723_, 20);
lean_inc_ref(v_postUpdateHooks_4728_);
v___x_4729_ = lean_array_get_size(v_postUpdateHooks_4728_);
v___x_4730_ = lean_unsigned_to_nat(0u);
v___x_4731_ = lean_nat_dec_eq(v___x_4729_, v___x_4730_);
if (v___x_4731_ == 0)
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; uint8_t v___x_4739_; 
lean_inc(v_baseName_4727_);
v___x_4732_ = l_Lean_Name_toString(v_baseName_4727_, v___x_4731_);
v___x_4733_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4734_ = lean_string_append(v___x_4732_, v___x_4733_);
v___x_4735_ = 1;
v___x_4736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4736_, 0, v___x_4734_);
lean_ctor_set_uint8(v___x_4736_, sizeof(void*)*1, v___x_4735_);
lean_inc_ref(v_a_4725_);
v___x_4737_ = lean_apply_2(v_a_4725_, v___x_4736_, lean_box(0));
v___x_4738_ = lean_box(0);
v___x_4739_ = lean_nat_dec_lt(v___x_4730_, v___x_4729_);
if (v___x_4739_ == 0)
{
lean_object* v___x_4740_; 
lean_dec_ref(v_postUpdateHooks_4728_);
lean_dec_ref(v_pkg_4723_);
v___x_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4738_);
return v___x_4740_;
}
else
{
uint8_t v___x_4741_; 
v___x_4741_ = lean_nat_dec_le(v___x_4729_, v___x_4729_);
if (v___x_4741_ == 0)
{
if (v___x_4739_ == 0)
{
lean_object* v___x_4742_; 
lean_dec_ref(v_postUpdateHooks_4728_);
lean_dec_ref(v_pkg_4723_);
v___x_4742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4738_);
return v___x_4742_;
}
else
{
size_t v___x_4743_; size_t v___x_4744_; lean_object* v___x_4745_; 
v___x_4743_ = ((size_t)0ULL);
v___x_4744_ = lean_usize_of_nat(v___x_4729_);
v___x_4745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4723_, v_postUpdateHooks_4728_, v___x_4743_, v___x_4744_, v___x_4738_, v_a_4724_, v_a_4725_);
lean_dec_ref(v_postUpdateHooks_4728_);
return v___x_4745_;
}
}
else
{
size_t v___x_4746_; size_t v___x_4747_; lean_object* v___x_4748_; 
v___x_4746_ = ((size_t)0ULL);
v___x_4747_ = lean_usize_of_nat(v___x_4729_);
v___x_4748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4723_, v_postUpdateHooks_4728_, v___x_4746_, v___x_4747_, v___x_4738_, v_a_4724_, v_a_4725_);
lean_dec_ref(v_postUpdateHooks_4728_);
return v___x_4748_;
}
}
}
else
{
lean_object* v___x_4749_; lean_object* v___x_4750_; 
lean_dec_ref(v_postUpdateHooks_4728_);
lean_dec_ref(v_pkg_4723_);
v___x_4749_ = lean_box(0);
v___x_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
return v___x_4750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4751_, v_a_4752_, v_a_4753_);
lean_dec_ref(v_a_4753_);
lean_dec(v_a_4752_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4756_, lean_object* v_ws_4757_, lean_object* v_toUpdate_4758_, lean_object* v_leanOpts_4759_, uint8_t v_updateToolchain_4760_){
_start:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4762_ = lean_box(1);
v___x_4763_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4756_, v_ws_4757_, v_toUpdate_4758_, v___x_4762_);
if (lean_obj_tag(v___x_4763_) == 0)
{
lean_object* v_a_4764_; lean_object* v_snd_4765_; uint8_t v___x_4766_; 
v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
lean_inc(v_a_4764_);
lean_dec_ref_known(v___x_4763_, 1);
v_snd_4765_ = lean_ctor_get(v_a_4764_, 1);
lean_inc(v_snd_4765_);
lean_dec(v_a_4764_);
v___x_4766_ = 1;
if (v_updateToolchain_4760_ == 0)
{
lean_object* v_packages_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v_wsIdx_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v_packages_4767_ = lean_ctor_get(v_ws_4757_, 4);
v___x_4768_ = lean_unsigned_to_nat(0u);
v___x_4769_ = lean_array_fget_borrowed(v_packages_4767_, v___x_4768_);
v_wsIdx_4770_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_wsIdx_4770_);
v___x_4771_ = lean_array_get_size(v_packages_4767_);
v___x_4772_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4759_, v___x_4766_, v_ws_4757_, v_wsIdx_4770_, v___x_4771_, v_snd_4765_, v_a_4756_);
if (lean_obj_tag(v___x_4772_) == 0)
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4790_; 
v_a_4773_ = lean_ctor_get(v___x_4772_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4772_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4775_ = v___x_4772_;
v_isShared_4776_ = v_isSharedCheck_4790_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v___x_4772_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4790_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v_fst_4777_; lean_object* v_snd_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4789_; 
v_fst_4777_ = lean_ctor_get(v_a_4773_, 0);
v_snd_4778_ = lean_ctor_get(v_a_4773_, 1);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_a_4773_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4780_ = v_a_4773_;
v_isShared_4781_ = v_isSharedCheck_4789_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_snd_4778_);
lean_inc(v_fst_4777_);
lean_dec(v_a_4773_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4789_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4782_; lean_object* v___x_4784_; 
v___x_4782_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4777_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v___x_4782_);
v___x_4784_ = v___x_4780_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4782_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v_snd_4778_);
v___x_4784_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
lean_object* v___x_4786_; 
if (v_isShared_4776_ == 0)
{
lean_ctor_set(v___x_4775_, 0, v___x_4784_);
v___x_4786_ = v___x_4775_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
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
else
{
return v___x_4772_;
}
}
else
{
lean_object* v_packages_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v_depConfigs_4794_; lean_object* v___x_4795_; lean_object* v___f_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v_packages_4791_ = lean_ctor_get(v_ws_4757_, 4);
lean_inc_ref(v_packages_4791_);
v___x_4792_ = lean_unsigned_to_nat(0u);
v___x_4793_ = lean_array_fget_borrowed(v_packages_4791_, v___x_4792_);
v_depConfigs_4794_ = lean_ctor_get(v___x_4793_, 12);
v___x_4795_ = lean_box(v_updateToolchain_4760_);
lean_inc_ref(v_ws_4757_);
lean_inc(v___x_4793_);
v___f_4796_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4796_, 0, v___x_4793_);
lean_closure_set(v___f_4796_, 1, v___x_4795_);
lean_closure_set(v___f_4796_, 2, v_ws_4757_);
v___x_4797_ = lean_array_get_size(v_depConfigs_4794_);
lean_inc_ref(v_depConfigs_4794_);
v___x_4798_ = l_Array_reverse___redArg(v_depConfigs_4794_);
v___x_4799_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4800_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4797_, v___f_4796_, v___x_4798_, v___x_4792_, v___x_4799_, v_snd_4765_, v_a_4756_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v_fst_4802_; lean_object* v_snd_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4875_; 
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
lean_inc(v_a_4801_);
lean_dec_ref_known(v___x_4800_, 1);
v_fst_4802_ = lean_ctor_get(v_a_4801_, 0);
v_snd_4803_ = lean_ctor_get(v_a_4801_, 1);
v_isSharedCheck_4875_ = !lean_is_exclusive(v_a_4801_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4805_ = v_a_4801_;
v_isShared_4806_ = v_isSharedCheck_4875_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_snd_4803_);
lean_inc(v_fst_4802_);
lean_dec(v_a_4801_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4875_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4807_; 
lean_inc_ref(v_ws_4757_);
v___x_4807_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4756_, v_ws_4757_, v_fst_4802_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v___x_4808_; 
lean_dec_ref_known(v___x_4807_, 1);
lean_inc_ref(v_leanOpts_4759_);
v___x_4808_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4797_, v_fst_4802_, v___x_4798_, v_leanOpts_4759_, v___x_4792_, v_ws_4757_, v_snd_4803_, v_a_4756_);
lean_dec_ref(v___x_4798_);
lean_dec(v_fst_4802_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4858_; 
v_a_4809_ = lean_ctor_get(v___x_4808_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4811_ = v___x_4808_;
v_isShared_4812_ = v_isSharedCheck_4858_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4808_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4858_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v_fst_4813_; lean_object* v_snd_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4857_; 
v_fst_4813_ = lean_ctor_get(v_a_4809_, 0);
v_snd_4814_ = lean_ctor_get(v_a_4809_, 1);
v_isSharedCheck_4857_ = !lean_is_exclusive(v_a_4809_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4816_ = v_a_4809_;
v_isShared_4817_ = v_isSharedCheck_4857_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_snd_4814_);
lean_inc(v_fst_4813_);
lean_dec(v_a_4809_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4857_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v_packages_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4824_; 
v_packages_4818_ = lean_ctor_get(v_fst_4813_, 4);
v___x_4819_ = lean_array_get_size(v_packages_4791_);
lean_dec_ref(v_packages_4791_);
v___x_4820_ = lean_array_get_size(v_packages_4818_);
v___x_4821_ = lean_array_fget(v_packages_4818_, v___x_4792_);
v___x_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4819_);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 1, v___x_4820_);
lean_ctor_set(v___x_4805_, 0, v___x_4822_);
v___x_4824_ = v___x_4805_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v___x_4822_);
lean_ctor_set(v_reuseFailAlloc_4856_, 1, v___x_4820_);
v___x_4824_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
v___x_4825_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4824_, v___x_4799_);
v___x_4826_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4813_, v___x_4821_, v___x_4825_);
v___x_4827_ = lean_nat_dec_eq(v___x_4819_, v___x_4820_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
lean_del_object(v___x_4816_);
lean_del_object(v___x_4811_);
v___x_4828_ = lean_unsigned_to_nat(1u);
v___x_4829_ = lean_nat_add(v___x_4819_, v___x_4828_);
v___x_4830_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4759_, v___x_4766_, v___x_4826_, v___x_4819_, v___x_4829_, v_snd_4814_, v_a_4756_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4848_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4833_ = v___x_4830_;
v_isShared_4834_ = v_isSharedCheck_4848_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4830_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4848_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v_fst_4835_; lean_object* v_snd_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4847_; 
v_fst_4835_ = lean_ctor_get(v_a_4831_, 0);
v_snd_4836_ = lean_ctor_get(v_a_4831_, 1);
v_isSharedCheck_4847_ = !lean_is_exclusive(v_a_4831_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4838_ = v_a_4831_;
v_isShared_4839_ = v_isSharedCheck_4847_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_snd_4836_);
lean_inc(v_fst_4835_);
lean_dec(v_a_4831_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4847_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v___x_4840_; lean_object* v___x_4842_; 
v___x_4840_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4835_);
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 0, v___x_4840_);
v___x_4842_ = v___x_4838_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4840_);
lean_ctor_set(v_reuseFailAlloc_4846_, 1, v_snd_4836_);
v___x_4842_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
lean_object* v___x_4844_; 
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 0, v___x_4842_);
v___x_4844_ = v___x_4833_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4842_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
else
{
return v___x_4830_;
}
}
else
{
lean_object* v___x_4849_; lean_object* v___x_4851_; 
lean_dec_ref(v_leanOpts_4759_);
v___x_4849_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4826_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 0, v___x_4849_);
v___x_4851_ = v___x_4816_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v___x_4849_);
lean_ctor_set(v_reuseFailAlloc_4855_, 1, v_snd_4814_);
v___x_4851_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
lean_object* v___x_4853_; 
if (v_isShared_4812_ == 0)
{
lean_ctor_set(v___x_4811_, 0, v___x_4851_);
v___x_4853_ = v___x_4811_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4851_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4866_; 
lean_del_object(v___x_4805_);
lean_dec_ref(v_packages_4791_);
lean_dec_ref(v_leanOpts_4759_);
v_a_4859_ = lean_ctor_get(v___x_4808_, 0);
v_isSharedCheck_4866_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4866_ == 0)
{
v___x_4861_ = v___x_4808_;
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_a_4859_);
lean_dec(v___x_4808_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4864_; 
if (v_isShared_4862_ == 0)
{
v___x_4864_ = v___x_4861_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_a_4859_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
}
}
else
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4874_; 
lean_del_object(v___x_4805_);
lean_dec(v_snd_4803_);
lean_dec(v_fst_4802_);
lean_dec_ref(v___x_4798_);
lean_dec_ref(v_packages_4791_);
lean_dec_ref(v_leanOpts_4759_);
lean_dec_ref(v_ws_4757_);
v_a_4867_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4869_ = v___x_4807_;
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4807_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4872_; 
if (v_isShared_4870_ == 0)
{
v___x_4872_ = v___x_4869_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
lean_dec_ref(v___x_4798_);
lean_dec_ref(v_packages_4791_);
lean_dec_ref(v_leanOpts_4759_);
lean_dec_ref(v_ws_4757_);
v_a_4876_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4800_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4800_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4879_ == 0)
{
v___x_4881_ = v___x_4878_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4876_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
lean_dec_ref(v_leanOpts_4759_);
lean_dec_ref(v_ws_4757_);
v_a_4884_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4763_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4763_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4892_, lean_object* v_ws_4893_, lean_object* v_toUpdate_4894_, lean_object* v_leanOpts_4895_, lean_object* v_updateToolchain_4896_, lean_object* v_a_4897_){
_start:
{
uint8_t v_updateToolchain_boxed_4898_; lean_object* v_res_4899_; 
v_updateToolchain_boxed_4898_ = lean_unbox(v_updateToolchain_4896_);
v_res_4899_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4892_, v_ws_4893_, v_toUpdate_4894_, v_leanOpts_4895_, v_updateToolchain_boxed_4898_);
lean_dec_ref(v_a_4892_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4900_, size_t v_i_4901_, size_t v_stop_4902_, lean_object* v_b_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
uint8_t v___x_4907_; 
v___x_4907_ = lean_usize_dec_eq(v_i_4901_, v_stop_4902_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = lean_array_uget_borrowed(v_as_4900_, v_i_4901_);
lean_inc(v___x_4908_);
v___x_4909_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4908_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; size_t v___x_4911_; size_t v___x_4912_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_a_4910_);
lean_dec_ref_known(v___x_4909_, 1);
v___x_4911_ = ((size_t)1ULL);
v___x_4912_ = lean_usize_add(v_i_4901_, v___x_4911_);
v_i_4901_ = v___x_4912_;
v_b_4903_ = v_a_4910_;
goto _start;
}
else
{
return v___x_4909_;
}
}
else
{
lean_object* v___x_4914_; 
v___x_4914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4914_, 0, v_b_4903_);
return v___x_4914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4915_, lean_object* v_i_4916_, lean_object* v_stop_4917_, lean_object* v_b_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_){
_start:
{
size_t v_i_boxed_4922_; size_t v_stop_boxed_4923_; lean_object* v_res_4924_; 
v_i_boxed_4922_ = lean_unbox_usize(v_i_4916_);
lean_dec(v_i_4916_);
v_stop_boxed_4923_ = lean_unbox_usize(v_stop_4917_);
lean_dec(v_stop_4917_);
v_res_4924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4915_, v_i_boxed_4922_, v_stop_boxed_4923_, v_b_4918_, v___y_4919_, v___y_4920_);
lean_dec_ref(v___y_4920_);
lean_dec(v___y_4919_);
lean_dec_ref(v_as_4915_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4925_, lean_object* v_toUpdate_4926_, lean_object* v_leanOpts_4927_, uint8_t v_updateToolchain_4928_, lean_object* v_a_4929_){
_start:
{
lean_object* v___x_4931_; 
v___x_4931_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4929_, v_ws_4925_, v_toUpdate_4926_, v_leanOpts_4927_, v_updateToolchain_4928_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v_a_4932_; lean_object* v_fst_4933_; lean_object* v_snd_4934_; lean_object* v___y_4936_; lean_object* v___x_4953_; 
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc(v_a_4932_);
lean_dec_ref_known(v___x_4931_, 1);
v_fst_4933_ = lean_ctor_get(v_a_4932_, 0);
lean_inc(v_fst_4933_);
v_snd_4934_ = lean_ctor_get(v_a_4932_, 1);
lean_inc(v_snd_4934_);
lean_dec(v_a_4932_);
v___x_4953_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4933_, v_snd_4934_);
lean_dec(v_snd_4934_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4975_; 
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4975_ == 0)
{
lean_object* v_unused_4976_; 
v_unused_4976_ = lean_ctor_get(v___x_4953_, 0);
lean_dec(v_unused_4976_);
v___x_4955_ = v___x_4953_;
v_isShared_4956_ = v_isSharedCheck_4975_;
goto v_resetjp_4954_;
}
else
{
lean_dec(v___x_4953_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4975_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v_packages_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; uint8_t v___x_4960_; 
v_packages_4957_ = lean_ctor_get(v_fst_4933_, 4);
v___x_4958_ = lean_unsigned_to_nat(0u);
v___x_4959_ = lean_array_get_size(v_packages_4957_);
v___x_4960_ = lean_nat_dec_lt(v___x_4958_, v___x_4959_);
if (v___x_4960_ == 0)
{
lean_object* v___x_4962_; 
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 0, v_fst_4933_);
v___x_4962_ = v___x_4955_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_fst_4933_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
else
{
lean_object* v___x_4964_; uint8_t v___x_4965_; 
v___x_4964_ = lean_box(0);
v___x_4965_ = lean_nat_dec_le(v___x_4959_, v___x_4959_);
if (v___x_4965_ == 0)
{
if (v___x_4960_ == 0)
{
lean_object* v___x_4967_; 
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 0, v_fst_4933_);
v___x_4967_ = v___x_4955_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_fst_4933_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
return v___x_4967_;
}
}
else
{
size_t v___x_4969_; size_t v___x_4970_; lean_object* v___x_4971_; 
lean_del_object(v___x_4955_);
v___x_4969_ = ((size_t)0ULL);
v___x_4970_ = lean_usize_of_nat(v___x_4959_);
v___x_4971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4957_, v___x_4969_, v___x_4970_, v___x_4964_, v_fst_4933_, v_a_4929_);
v___y_4936_ = v___x_4971_;
goto v___jp_4935_;
}
}
else
{
size_t v___x_4972_; size_t v___x_4973_; lean_object* v___x_4974_; 
lean_del_object(v___x_4955_);
v___x_4972_ = ((size_t)0ULL);
v___x_4973_ = lean_usize_of_nat(v___x_4959_);
v___x_4974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4957_, v___x_4972_, v___x_4973_, v___x_4964_, v_fst_4933_, v_a_4929_);
v___y_4936_ = v___x_4974_;
goto v___jp_4935_;
}
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4989_; 
lean_dec(v_fst_4933_);
v_a_4977_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_4989_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4979_ = v___x_4953_;
v_isShared_4980_ = v_isSharedCheck_4989_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4953_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4989_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4981_; uint8_t v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4987_; 
v___x_4981_ = lean_io_error_to_string(v_a_4977_);
v___x_4982_ = 3;
v___x_4983_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4983_, 0, v___x_4981_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*1, v___x_4982_);
lean_inc_ref(v_a_4929_);
v___x_4984_ = lean_apply_2(v_a_4929_, v___x_4983_, lean_box(0));
v___x_4985_ = lean_box(0);
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 0, v___x_4985_);
v___x_4987_ = v___x_4979_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4985_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
}
v___jp_4935_:
{
if (lean_obj_tag(v___y_4936_) == 0)
{
lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
v_isSharedCheck_4943_ = !lean_is_exclusive(v___y_4936_);
if (v_isSharedCheck_4943_ == 0)
{
lean_object* v_unused_4944_; 
v_unused_4944_ = lean_ctor_get(v___y_4936_, 0);
lean_dec(v_unused_4944_);
v___x_4938_ = v___y_4936_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_dec(v___y_4936_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 0, v_fst_4933_);
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_fst_4933_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
else
{
lean_object* v_a_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4952_; 
lean_dec(v_fst_4933_);
v_a_4945_ = lean_ctor_get(v___y_4936_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___y_4936_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4947_ = v___y_4936_;
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___y_4936_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4950_; 
if (v_isShared_4948_ == 0)
{
v___x_4950_ = v___x_4947_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_a_4945_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
return v___x_4950_;
}
}
}
}
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
v_a_4990_ = lean_ctor_get(v___x_4931_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4992_ = v___x_4931_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4931_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4998_, lean_object* v_toUpdate_4999_, lean_object* v_leanOpts_5000_, lean_object* v_updateToolchain_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_){
_start:
{
uint8_t v_updateToolchain_boxed_5004_; lean_object* v_res_5005_; 
v_updateToolchain_boxed_5004_ = lean_unbox(v_updateToolchain_5001_);
v_res_5005_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4998_, v_toUpdate_4999_, v_leanOpts_5000_, v_updateToolchain_boxed_5004_, v_a_5002_);
lean_dec_ref(v_a_5002_);
return v_res_5005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_5010_, lean_object* v_what_5011_, lean_object* v___y_5012_){
_start:
{
lean_object* v_name_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; uint8_t v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; uint8_t v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v_name_5014_ = lean_ctor_get(v___x_5010_, 0);
lean_inc(v_name_5014_);
lean_dec_ref(v___x_5010_);
v___x_5015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_5016_ = lean_string_append(v___x_5015_, v_what_5011_);
v___x_5017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_5018_ = lean_string_append(v___x_5016_, v___x_5017_);
v___x_5019_ = 1;
v___x_5020_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5014_, v___x_5019_);
v___x_5021_ = lean_string_append(v___x_5018_, v___x_5020_);
v___x_5022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_5023_ = lean_string_append(v___x_5021_, v___x_5022_);
v___x_5024_ = lean_string_append(v___x_5023_, v___x_5020_);
lean_dec_ref(v___x_5020_);
v___x_5025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_5026_ = lean_string_append(v___x_5024_, v___x_5025_);
v___x_5027_ = 2;
v___x_5028_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5028_, 0, v___x_5026_);
lean_ctor_set_uint8(v___x_5028_, sizeof(void*)*1, v___x_5027_);
lean_inc_ref(v___y_5012_);
v___x_5029_ = lean_apply_2(v___y_5012_, v___x_5028_, lean_box(0));
v___x_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5029_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_5031_, lean_object* v_what_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5031_, v_what_5032_, v___y_5033_);
lean_dec_ref(v___y_5033_);
lean_dec_ref(v_what_5032_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_5039_, lean_object* v_as_5040_, size_t v_i_5041_, size_t v_stop_5042_, lean_object* v_b_5043_, lean_object* v___y_5044_){
_start:
{
lean_object* v_a_5047_; lean_object* v___y_5052_; uint8_t v___x_5054_; 
v___x_5054_ = lean_usize_dec_eq(v_i_5041_, v_stop_5042_);
if (v___x_5054_ == 0)
{
lean_object* v___x_5055_; lean_object* v_src_x3f_5056_; 
v___x_5055_ = lean_array_uget_borrowed(v_as_5040_, v_i_5041_);
v_src_x3f_5056_ = lean_ctor_get(v___x_5055_, 3);
if (lean_obj_tag(v_src_x3f_5056_) == 1)
{
lean_object* v_name_5057_; lean_object* v_val_5058_; lean_object* v___x_5059_; 
v_name_5057_ = lean_ctor_get(v___x_5055_, 0);
v_val_5058_ = lean_ctor_get(v_src_x3f_5056_, 0);
v___x_5059_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_5039_, v_name_5057_);
if (lean_obj_tag(v___x_5059_) == 1)
{
lean_object* v_val_5060_; lean_object* v___y_5062_; lean_object* v___y_5066_; 
v_val_5060_ = lean_ctor_get(v___x_5059_, 0);
lean_inc(v_val_5060_);
lean_dec_ref_known(v___x_5059_, 1);
if (lean_obj_tag(v_val_5058_) == 0)
{
lean_object* v_src_5069_; 
v_src_5069_ = lean_ctor_get(v_val_5060_, 4);
lean_inc_ref(v_src_5069_);
lean_dec(v_val_5060_);
if (lean_obj_tag(v_src_5069_) == 0)
{
lean_object* v___x_5070_; 
lean_dec_ref_known(v_src_5069_, 1);
v___x_5070_ = lean_box(0);
v_a_5047_ = v___x_5070_;
goto v___jp_5046_;
}
else
{
lean_dec_ref(v_src_5069_);
v___y_5066_ = v___y_5044_;
goto v___jp_5065_;
}
}
else
{
lean_object* v_src_5071_; 
v_src_5071_ = lean_ctor_get(v_val_5060_, 4);
lean_inc_ref(v_src_5071_);
lean_dec(v_val_5060_);
if (lean_obj_tag(v_src_5071_) == 1)
{
lean_object* v_url_5072_; lean_object* v_rev_5073_; lean_object* v_url_5074_; lean_object* v_inputRev_x3f_5075_; lean_object* v___y_5077_; uint8_t v___x_5084_; 
v_url_5072_ = lean_ctor_get(v_val_5058_, 0);
v_rev_5073_ = lean_ctor_get(v_val_5058_, 1);
v_url_5074_ = lean_ctor_get(v_src_5071_, 0);
lean_inc_ref(v_url_5074_);
v_inputRev_x3f_5075_ = lean_ctor_get(v_src_5071_, 2);
lean_inc(v_inputRev_x3f_5075_);
lean_dec_ref_known(v_src_5071_, 4);
v___x_5084_ = lean_string_dec_eq(v_url_5072_, v_url_5074_);
lean_dec_ref(v_url_5074_);
if (v___x_5084_ == 0)
{
goto v___jp_5081_;
}
else
{
if (v___x_5054_ == 0)
{
v___y_5077_ = v___y_5044_;
goto v___jp_5076_;
}
else
{
goto v___jp_5081_;
}
}
v___jp_5076_:
{
lean_object* v___x_5078_; uint8_t v___x_5079_; 
v___x_5078_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_5073_);
v___x_5079_ = l_Option_instDecidableEq___redArg(v___x_5078_, v_rev_5073_, v_inputRev_x3f_5075_);
if (v___x_5079_ == 0)
{
v___y_5062_ = v___y_5077_;
goto v___jp_5061_;
}
else
{
if (v___x_5054_ == 0)
{
lean_object* v___x_5080_; 
v___x_5080_ = lean_box(0);
v_a_5047_ = v___x_5080_;
goto v___jp_5046_;
}
else
{
v___y_5062_ = v___y_5077_;
goto v___jp_5061_;
}
}
}
v___jp_5081_:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_5055_);
v___x_5083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5055_, v___x_5082_, v___y_5044_);
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_dec_ref_known(v___x_5083_, 1);
v___y_5077_ = v___y_5044_;
goto v___jp_5076_;
}
else
{
lean_dec(v_inputRev_x3f_5075_);
return v___x_5083_;
}
}
}
else
{
lean_dec_ref(v_src_5071_);
v___y_5066_ = v___y_5044_;
goto v___jp_5065_;
}
}
v___jp_5061_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_5055_);
v___x_5064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5055_, v___x_5063_, v___y_5062_);
v___y_5052_ = v___x_5064_;
goto v___jp_5051_;
}
v___jp_5065_:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_5055_);
v___x_5068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5055_, v___x_5067_, v___y_5066_);
v___y_5052_ = v___x_5068_;
goto v___jp_5051_;
}
}
else
{
lean_object* v___x_5085_; 
lean_dec(v___x_5059_);
v___x_5085_ = lean_box(0);
v_a_5047_ = v___x_5085_;
goto v___jp_5046_;
}
}
else
{
lean_object* v___x_5086_; 
v___x_5086_ = lean_box(0);
v_a_5047_ = v___x_5086_;
goto v___jp_5046_;
}
}
else
{
lean_object* v___x_5087_; 
v___x_5087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5087_, 0, v_b_5043_);
return v___x_5087_;
}
v___jp_5046_:
{
size_t v___x_5048_; size_t v___x_5049_; 
v___x_5048_ = ((size_t)1ULL);
v___x_5049_ = lean_usize_add(v_i_5041_, v___x_5048_);
v_i_5041_ = v___x_5049_;
v_b_5043_ = v_a_5047_;
goto _start;
}
v___jp_5051_:
{
if (lean_obj_tag(v___y_5052_) == 0)
{
lean_object* v_a_5053_; 
v_a_5053_ = lean_ctor_get(v___y_5052_, 0);
lean_inc(v_a_5053_);
lean_dec_ref_known(v___y_5052_, 1);
v_a_5047_ = v_a_5053_;
goto v___jp_5046_;
}
else
{
return v___y_5052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_5088_, lean_object* v_as_5089_, lean_object* v_i_5090_, lean_object* v_stop_5091_, lean_object* v_b_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
size_t v_i_boxed_5095_; size_t v_stop_boxed_5096_; lean_object* v_res_5097_; 
v_i_boxed_5095_ = lean_unbox_usize(v_i_5090_);
lean_dec(v_i_5090_);
v_stop_boxed_5096_ = lean_unbox_usize(v_stop_5091_);
lean_dec(v_stop_5091_);
v_res_5097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5088_, v_as_5089_, v_i_boxed_5095_, v_stop_boxed_5096_, v_b_5092_, v___y_5093_);
lean_dec_ref(v___y_5093_);
lean_dec_ref(v_as_5089_);
lean_dec(v_pkgEntries_5088_);
return v_res_5097_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_5098_, lean_object* v_deps_5099_, lean_object* v_a_5100_){
_start:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; uint8_t v___x_5105_; 
v___x_5102_ = lean_unsigned_to_nat(0u);
v___x_5103_ = lean_array_get_size(v_deps_5099_);
v___x_5104_ = lean_box(0);
v___x_5105_ = lean_nat_dec_lt(v___x_5102_, v___x_5103_);
if (v___x_5105_ == 0)
{
lean_object* v___x_5106_; 
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5104_);
return v___x_5106_;
}
else
{
uint8_t v___x_5107_; 
v___x_5107_ = lean_nat_dec_le(v___x_5103_, v___x_5103_);
if (v___x_5107_ == 0)
{
if (v___x_5105_ == 0)
{
lean_object* v___x_5108_; 
v___x_5108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5104_);
return v___x_5108_;
}
else
{
size_t v___x_5109_; size_t v___x_5110_; lean_object* v___x_5111_; 
v___x_5109_ = ((size_t)0ULL);
v___x_5110_ = lean_usize_of_nat(v___x_5103_);
v___x_5111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5098_, v_deps_5099_, v___x_5109_, v___x_5110_, v___x_5104_, v_a_5100_);
return v___x_5111_;
}
}
else
{
size_t v___x_5112_; size_t v___x_5113_; lean_object* v___x_5114_; 
v___x_5112_ = ((size_t)0ULL);
v___x_5113_ = lean_usize_of_nat(v___x_5103_);
v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5098_, v_deps_5099_, v___x_5112_, v___x_5113_, v___x_5104_, v_a_5100_);
return v___x_5114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_5115_, lean_object* v_deps_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_5115_, v_deps_5116_, v_a_5117_);
lean_dec_ref(v_a_5117_);
lean_dec_ref(v_deps_5116_);
lean_dec(v_pkgEntries_5115_);
return v_res_5119_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_5120_, lean_object* v_x_5121_){
_start:
{
if (lean_obj_tag(v_x_5120_) == 0)
{
if (lean_obj_tag(v_x_5121_) == 0)
{
uint8_t v___x_5122_; 
v___x_5122_ = 1;
return v___x_5122_;
}
else
{
uint8_t v___x_5123_; 
v___x_5123_ = 0;
return v___x_5123_;
}
}
else
{
if (lean_obj_tag(v_x_5121_) == 0)
{
uint8_t v___x_5124_; 
v___x_5124_ = 0;
return v___x_5124_;
}
else
{
lean_object* v_val_5125_; lean_object* v_val_5126_; uint8_t v___x_5127_; 
v_val_5125_ = lean_ctor_get(v_x_5120_, 0);
v_val_5126_ = lean_ctor_get(v_x_5121_, 0);
v___x_5127_ = lean_string_dec_eq(v_val_5125_, v_val_5126_);
return v___x_5127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_5128_, lean_object* v_x_5129_){
_start:
{
uint8_t v_res_5130_; lean_object* v_r_5131_; 
v_res_5130_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_5128_, v_x_5129_);
lean_dec(v_x_5129_);
lean_dec(v_x_5128_);
v_r_5131_ = lean_box(v_res_5130_);
return v_r_5131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_pkg_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v_leanOpts_5140_, uint8_t v_reconfigure_5141_, lean_object* v_as_5142_, size_t v_i_5143_, size_t v_stop_5144_, lean_object* v_b_5145_, lean_object* v___y_5146_){
_start:
{
uint8_t v___x_5151_; 
v___x_5151_ = lean_usize_dec_eq(v_i_5143_, v_stop_5144_);
if (v___x_5151_ == 0)
{
lean_object* v_ws_5152_; lean_object* v_depIdxs_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5301_; 
v_ws_5152_ = lean_ctor_get(v_b_5145_, 0);
v_depIdxs_5153_ = lean_ctor_get(v_b_5145_, 1);
v_isSharedCheck_5301_ = !lean_is_exclusive(v_b_5145_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5155_ = v_b_5145_;
v_isShared_5156_ = v_isSharedCheck_5301_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_depIdxs_5153_);
lean_inc(v_ws_5152_);
lean_dec(v_b_5145_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5301_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v_lakeEnv_5157_; lean_object* v_packages_5158_; size_t v___x_5159_; size_t v___x_5160_; lean_object* v___x_5161_; lean_object* v___f_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; 
v_lakeEnv_5157_ = lean_ctor_get(v_ws_5152_, 0);
v_packages_5158_ = lean_ctor_get(v_ws_5152_, 4);
v___x_5159_ = ((size_t)1ULL);
v___x_5160_ = lean_usize_sub(v_i_5143_, v___x_5159_);
v___x_5161_ = lean_array_uget_borrowed(v_as_5142_, v___x_5160_);
lean_inc(v___x_5161_);
v___f_5162_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5162_, 0, v___x_5161_);
v___x_5163_ = lean_unsigned_to_nat(0u);
v___x_5164_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5162_, v_packages_5158_, v___x_5163_);
if (lean_obj_tag(v___x_5164_) == 1)
{
lean_object* v_val_5165_; lean_object* v___x_5166_; lean_object* v___x_5168_; 
v_val_5165_ = lean_ctor_get(v___x_5164_, 0);
lean_inc(v_val_5165_);
lean_dec_ref_known(v___x_5164_, 1);
v___x_5166_ = lean_array_push(v_depIdxs_5153_, v_val_5165_);
if (v_isShared_5156_ == 0)
{
lean_ctor_set(v___x_5155_, 1, v___x_5166_);
v___x_5168_ = v___x_5155_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_ws_5152_);
lean_ctor_set(v_reuseFailAlloc_5170_, 1, v___x_5166_);
v___x_5168_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
v_i_5143_ = v___x_5160_;
v_b_5145_ = v___x_5168_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_5171_; lean_object* v_baseName_5172_; lean_object* v_name_5173_; lean_object* v_opts_5174_; uint8_t v___x_5175_; 
lean_inc_ref(v_packages_5158_);
lean_dec(v___x_5164_);
v_wsIdx_5171_ = lean_ctor_get(v_pkg_5137_, 0);
v_baseName_5172_ = lean_ctor_get(v_pkg_5137_, 1);
v_name_5173_ = lean_ctor_get(v___x_5161_, 0);
v_opts_5174_ = lean_ctor_get(v___x_5161_, 4);
v___x_5175_ = lean_name_eq(v_baseName_5172_, v_name_5173_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; 
v___x_5176_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5138_, v_name_5173_);
if (lean_obj_tag(v___x_5176_) == 1)
{
lean_object* v_val_5177_; lean_object* v___x_5178_; lean_object* v_dir_5179_; lean_object* v___x_5180_; 
v_val_5177_ = lean_ctor_get(v___x_5176_, 0);
lean_inc(v_val_5177_);
lean_dec_ref_known(v___x_5176_, 1);
v___x_5178_ = lean_array_fget_borrowed(v_packages_5158_, v___x_5163_);
v_dir_5179_ = lean_ctor_get(v___x_5178_, 4);
lean_inc_ref(v___y_5139_);
lean_inc_ref(v_dir_5179_);
v___x_5180_ = l_Lake_PackageEntry_materialize(v_val_5177_, v_lakeEnv_5157_, v_dir_5179_, v___y_5139_, v___y_5146_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_object* v_a_5181_; lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5255_; 
v_a_5181_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5183_ = v___x_5180_;
v_isShared_5184_ = v_isSharedCheck_5255_;
goto v_resetjp_5182_;
}
else
{
lean_inc(v_a_5181_);
lean_dec(v___x_5180_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5255_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v___x_5185_; lean_object* v___x_5186_; 
v___x_5185_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_5140_);
lean_inc(v_opts_5174_);
v___x_5186_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5152_, v_a_5181_, v_opts_5174_, v_leanOpts_5140_, v_reconfigure_5141_, v___x_5185_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_a_5187_; lean_object* v_a_5188_; lean_object* v_wsIdx_5189_; lean_object* v___x_5190_; lean_object* v___x_5192_; 
lean_del_object(v___x_5183_);
v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_a_5187_);
v_a_5188_ = lean_ctor_get(v___x_5186_, 1);
lean_inc(v_a_5188_);
lean_dec_ref_known(v___x_5186_, 2);
v_wsIdx_5189_ = lean_array_get_size(v_packages_5158_);
lean_dec_ref(v_packages_5158_);
v___x_5190_ = lean_array_push(v_depIdxs_5153_, v_wsIdx_5189_);
if (v_isShared_5156_ == 0)
{
lean_ctor_set(v___x_5155_, 1, v___x_5190_);
lean_ctor_set(v___x_5155_, 0, v_a_5187_);
v___x_5192_ = v___x_5155_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5187_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v___x_5190_);
v___x_5192_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
lean_object* v___x_5193_; uint8_t v___x_5194_; 
v___x_5193_ = lean_array_get_size(v_a_5188_);
v___x_5194_ = lean_nat_dec_lt(v___x_5163_, v___x_5193_);
if (v___x_5194_ == 0)
{
lean_dec(v_a_5188_);
v_i_5143_ = v___x_5160_;
v_b_5145_ = v___x_5192_;
goto _start;
}
else
{
lean_object* v___x_5196_; uint8_t v___x_5197_; 
v___x_5196_ = lean_box(0);
v___x_5197_ = lean_nat_dec_le(v___x_5193_, v___x_5193_);
if (v___x_5197_ == 0)
{
if (v___x_5194_ == 0)
{
lean_dec(v_a_5188_);
v_i_5143_ = v___x_5160_;
v_b_5145_ = v___x_5192_;
goto _start;
}
else
{
size_t v___x_5199_; size_t v___x_5200_; lean_object* v___x_5201_; 
v___x_5199_ = ((size_t)0ULL);
v___x_5200_ = lean_usize_of_nat(v___x_5193_);
v___x_5201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5188_, v___x_5199_, v___x_5200_, v___x_5196_, v___y_5146_);
lean_dec(v_a_5188_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_dec_ref_known(v___x_5201_, 1);
v_i_5143_ = v___x_5160_;
v_b_5145_ = v___x_5192_;
goto _start;
}
else
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5210_; 
lean_dec_ref(v___x_5192_);
lean_dec_ref(v_leanOpts_5140_);
lean_dec_ref(v___y_5139_);
lean_dec_ref(v_pkg_5137_);
v_a_5203_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5205_ = v___x_5201_;
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___x_5201_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v___x_5208_; 
if (v_isShared_5206_ == 0)
{
v___x_5208_ = v___x_5205_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_a_5203_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
}
}
else
{
size_t v___x_5211_; size_t v___x_5212_; lean_object* v___x_5213_; 
v___x_5211_ = ((size_t)0ULL);
v___x_5212_ = lean_usize_of_nat(v___x_5193_);
v___x_5213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5188_, v___x_5211_, v___x_5212_, v___x_5196_, v___y_5146_);
lean_dec(v_a_5188_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_dec_ref_known(v___x_5213_, 1);
v_i_5143_ = v___x_5160_;
v_b_5145_ = v___x_5192_;
goto _start;
}
else
{
lean_object* v_a_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5222_; 
lean_dec_ref(v___x_5192_);
lean_dec_ref(v_leanOpts_5140_);
lean_dec_ref(v___y_5139_);
lean_dec_ref(v_pkg_5137_);
v_a_5215_ = lean_ctor_get(v___x_5213_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v___x_5213_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5217_ = v___x_5213_;
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_a_5215_);
lean_dec(v___x_5213_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5220_; 
if (v_isShared_5218_ == 0)
{
v___x_5220_ = v___x_5217_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
return v___x_5220_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5224_; lean_object* v___x_5225_; uint8_t v___x_5226_; 
lean_dec_ref(v_packages_5158_);
lean_del_object(v___x_5155_);
lean_dec_ref(v_depIdxs_5153_);
lean_dec_ref(v_leanOpts_5140_);
lean_dec_ref(v___y_5139_);
lean_dec_ref(v_pkg_5137_);
v_a_5224_ = lean_ctor_get(v___x_5186_, 1);
lean_inc(v_a_5224_);
lean_dec_ref_known(v___x_5186_, 2);
v___x_5225_ = lean_array_get_size(v_a_5224_);
v___x_5226_ = lean_nat_dec_lt(v___x_5163_, v___x_5225_);
if (v___x_5226_ == 0)
{
lean_object* v___x_5227_; lean_object* v___x_5229_; 
lean_dec(v_a_5224_);
v___x_5227_ = lean_box(0);
if (v_isShared_5184_ == 0)
{
lean_ctor_set_tag(v___x_5183_, 1);
lean_ctor_set(v___x_5183_, 0, v___x_5227_);
v___x_5229_ = v___x_5183_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v___x_5227_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
else
{
lean_object* v___x_5231_; uint8_t v___x_5232_; 
lean_del_object(v___x_5183_);
v___x_5231_ = lean_box(0);
v___x_5232_ = lean_nat_dec_le(v___x_5225_, v___x_5225_);
if (v___x_5232_ == 0)
{
if (v___x_5226_ == 0)
{
lean_dec(v_a_5224_);
goto v___jp_5148_;
}
else
{
size_t v___x_5233_; size_t v___x_5234_; lean_object* v___x_5235_; 
v___x_5233_ = ((size_t)0ULL);
v___x_5234_ = lean_usize_of_nat(v___x_5225_);
v___x_5235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5224_, v___x_5233_, v___x_5234_, v___x_5231_, v___y_5146_);
lean_dec(v_a_5224_);
if (lean_obj_tag(v___x_5235_) == 0)
{
lean_dec_ref_known(v___x_5235_, 1);
goto v___jp_5148_;
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
v_a_5236_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5235_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5235_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
}
else
{
size_t v___x_5244_; size_t v___x_5245_; lean_object* v___x_5246_; 
v___x_5244_ = ((size_t)0ULL);
v___x_5245_ = lean_usize_of_nat(v___x_5225_);
v___x_5246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5224_, v___x_5244_, v___x_5245_, v___x_5231_, v___y_5146_);
lean_dec(v_a_5224_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_dec_ref_known(v___x_5246_, 1);
goto v___jp_5148_;
}
else
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5254_; 
v_a_5247_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5249_ = v___x_5246_;
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5246_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5252_; 
if (v_isShared_5250_ == 0)
{
v___x_5252_ = v___x_5249_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
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
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5263_; 
lean_dec_ref(v_packages_5158_);
lean_del_object(v___x_5155_);
lean_dec_ref(v_depIdxs_5153_);
lean_dec_ref(v_ws_5152_);
lean_dec_ref(v_leanOpts_5140_);
lean_dec_ref(v___y_5139_);
lean_dec_ref(v_pkg_5137_);
v_a_5256_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5258_ = v___x_5180_;
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5180_);
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
else
{
uint8_t v___x_5264_; 
lean_inc(v_baseName_5172_);
lean_inc(v_wsIdx_5171_);
lean_dec(v___x_5176_);
lean_dec_ref(v_packages_5158_);
lean_del_object(v___x_5155_);
lean_dec_ref(v_depIdxs_5153_);
lean_dec_ref(v_ws_5152_);
lean_dec_ref(v_leanOpts_5140_);
lean_dec_ref(v___y_5139_);
lean_dec_ref(v_pkg_5137_);
v___x_5264_ = lean_nat_dec_eq(v_wsIdx_5171_, v___x_5163_);
lean_dec(v_wsIdx_5171_);
if (v___x_5264_ == 0)
{
lean_object* v___x_5265_; uint8_t v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; uint8_t v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
v___x_5265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5266_ = 1;
lean_inc(v_name_5173_);
v___x_5267_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5173_, v___x_5266_);
v___x_5268_ = lean_string_append(v___x_5265_, v___x_5267_);
lean_dec_ref(v___x_5267_);
v___x_5269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5270_ = lean_string_append(v___x_5268_, v___x_5269_);
v___x_5271_ = l_Lean_Name_toString(v_baseName_5172_, v___x_5264_);
v___x_5272_ = lean_string_append(v___x_5270_, v___x_5271_);
lean_dec_ref(v___x_5271_);
v___x_5273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5274_ = lean_string_append(v___x_5272_, v___x_5273_);
v___x_5275_ = 3;
v___x_5276_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5276_, 0, v___x_5274_);
lean_ctor_set_uint8(v___x_5276_, sizeof(void*)*1, v___x_5275_);
lean_inc_ref(v___y_5146_);
v___x_5277_ = lean_apply_2(v___y_5146_, v___x_5276_, lean_box(0));
v___x_5278_ = lean_box(0);
v___x_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5278_);
return v___x_5279_;
}
else
{
lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; uint8_t v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; 
lean_dec(v_baseName_5172_);
v___x_5280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5173_);
v___x_5281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5173_, v___x_5264_);
v___x_5282_ = lean_string_append(v___x_5280_, v___x_5281_);
v___x_5283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5284_ = lean_string_append(v___x_5282_, v___x_5283_);
v___x_5285_ = lean_string_append(v___x_5284_, v___x_5281_);
lean_dec_ref(v___x_5281_);
v___x_5286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5287_ = lean_string_append(v___x_5285_, v___x_5286_);
v___x_5288_ = 3;
v___x_5289_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5289_, 0, v___x_5287_);
lean_ctor_set_uint8(v___x_5289_, sizeof(void*)*1, v___x_5288_);
lean_inc_ref(v___y_5146_);
v___x_5290_ = lean_apply_2(v___y_5146_, v___x_5289_, lean_box(0));
v___x_5291_ = lean_box(0);
v___x_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5291_);
return v___x_5292_;
}
}
}
else
{
lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; uint8_t v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; 
lean_inc(v_baseName_5172_);
lean_dec_ref(v_packages_5158_);
lean_del_object(v___x_5155_);
lean_dec_ref(v_depIdxs_5153_);
lean_dec_ref(v_ws_5152_);
lean_dec_ref(v_leanOpts_5140_);
lean_dec_ref(v___y_5139_);
lean_dec_ref(v_pkg_5137_);
v___x_5293_ = l_Lean_Name_toString(v_baseName_5172_, v___x_5151_);
v___x_5294_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5295_ = lean_string_append(v___x_5293_, v___x_5294_);
v___x_5296_ = 3;
v___x_5297_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5297_, 0, v___x_5295_);
lean_ctor_set_uint8(v___x_5297_, sizeof(void*)*1, v___x_5296_);
lean_inc_ref(v___y_5146_);
v___x_5298_ = lean_apply_2(v___y_5146_, v___x_5297_, lean_box(0));
v___x_5299_ = lean_box(0);
v___x_5300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5300_, 0, v___x_5299_);
return v___x_5300_;
}
}
}
}
else
{
lean_object* v___x_5302_; 
lean_dec_ref(v_leanOpts_5140_);
lean_dec_ref(v___y_5139_);
lean_dec_ref(v_pkg_5137_);
v___x_5302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5302_, 0, v_b_5145_);
return v___x_5302_;
}
v___jp_5148_:
{
lean_object* v___x_5149_; lean_object* v___x_5150_; 
v___x_5149_ = lean_box(0);
v___x_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5150_, 0, v___x_5149_);
return v___x_5150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_pkg_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v_leanOpts_5306_, lean_object* v_reconfigure_5307_, lean_object* v_as_5308_, lean_object* v_i_5309_, lean_object* v_stop_5310_, lean_object* v_b_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_){
_start:
{
uint8_t v_reconfigure_boxed_5314_; size_t v_i_boxed_5315_; size_t v_stop_boxed_5316_; lean_object* v_res_5317_; 
v_reconfigure_boxed_5314_ = lean_unbox(v_reconfigure_5307_);
v_i_boxed_5315_ = lean_unbox_usize(v_i_5309_);
lean_dec(v_i_5309_);
v_stop_boxed_5316_ = lean_unbox_usize(v_stop_5310_);
lean_dec(v_stop_5310_);
v_res_5317_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5303_, v___y_5304_, v___y_5305_, v_leanOpts_5306_, v_reconfigure_boxed_5314_, v_as_5308_, v_i_boxed_5315_, v_stop_boxed_5316_, v_b_5311_, v___y_5312_);
lean_dec_ref(v___y_5312_);
lean_dec_ref(v_as_5308_);
lean_dec(v___y_5304_);
return v_res_5317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_start_5318_, lean_object* v_pkg_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v_leanOpts_5322_, uint8_t v_reconfigure_5323_, lean_object* v_as_5324_, size_t v_i_5325_, size_t v_stop_5326_, lean_object* v_b_5327_, lean_object* v___y_5328_){
_start:
{
uint8_t v___x_5333_; 
v___x_5333_ = lean_usize_dec_eq(v_i_5325_, v_stop_5326_);
if (v___x_5333_ == 0)
{
lean_object* v_ws_5334_; lean_object* v_depIdxs_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5483_; 
v_ws_5334_ = lean_ctor_get(v_b_5327_, 0);
v_depIdxs_5335_ = lean_ctor_get(v_b_5327_, 1);
v_isSharedCheck_5483_ = !lean_is_exclusive(v_b_5327_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5337_ = v_b_5327_;
v_isShared_5338_ = v_isSharedCheck_5483_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_depIdxs_5335_);
lean_inc(v_ws_5334_);
lean_dec(v_b_5327_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5483_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v_lakeEnv_5339_; lean_object* v_packages_5340_; size_t v___x_5341_; size_t v___x_5342_; lean_object* v___x_5343_; lean_object* v___f_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; 
v_lakeEnv_5339_ = lean_ctor_get(v_ws_5334_, 0);
v_packages_5340_ = lean_ctor_get(v_ws_5334_, 4);
v___x_5341_ = ((size_t)1ULL);
v___x_5342_ = lean_usize_sub(v_i_5325_, v___x_5341_);
v___x_5343_ = lean_array_uget_borrowed(v_as_5324_, v___x_5342_);
lean_inc(v___x_5343_);
v___f_5344_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5344_, 0, v___x_5343_);
v___x_5345_ = lean_unsigned_to_nat(0u);
v___x_5346_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5344_, v_packages_5340_, v___x_5345_);
if (lean_obj_tag(v___x_5346_) == 1)
{
lean_object* v_val_5347_; lean_object* v___x_5348_; lean_object* v___x_5350_; 
v_val_5347_ = lean_ctor_get(v___x_5346_, 0);
lean_inc(v_val_5347_);
lean_dec_ref_known(v___x_5346_, 1);
v___x_5348_ = lean_array_push(v_depIdxs_5335_, v_val_5347_);
if (v_isShared_5338_ == 0)
{
lean_ctor_set(v___x_5337_, 1, v___x_5348_);
v___x_5350_ = v___x_5337_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_ws_5334_);
lean_ctor_set(v_reuseFailAlloc_5352_, 1, v___x_5348_);
v___x_5350_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
lean_object* v___x_5351_; 
v___x_5351_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5319_, v___y_5320_, v___y_5321_, v_leanOpts_5322_, v_reconfigure_5323_, v_as_5324_, v___x_5342_, v_stop_5326_, v___x_5350_, v___y_5328_);
return v___x_5351_;
}
}
else
{
lean_object* v_wsIdx_5353_; lean_object* v_baseName_5354_; lean_object* v_name_5355_; lean_object* v_opts_5356_; uint8_t v___x_5357_; 
lean_inc_ref(v_packages_5340_);
lean_dec(v___x_5346_);
v_wsIdx_5353_ = lean_ctor_get(v_pkg_5319_, 0);
v_baseName_5354_ = lean_ctor_get(v_pkg_5319_, 1);
v_name_5355_ = lean_ctor_get(v___x_5343_, 0);
v_opts_5356_ = lean_ctor_get(v___x_5343_, 4);
v___x_5357_ = lean_name_eq(v_baseName_5354_, v_name_5355_);
if (v___x_5357_ == 0)
{
lean_object* v___x_5358_; 
v___x_5358_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5320_, v_name_5355_);
if (lean_obj_tag(v___x_5358_) == 1)
{
lean_object* v_val_5359_; lean_object* v___x_5360_; lean_object* v_dir_5361_; lean_object* v___x_5362_; 
v_val_5359_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_val_5359_);
lean_dec_ref_known(v___x_5358_, 1);
v___x_5360_ = lean_array_fget_borrowed(v_packages_5340_, v___x_5345_);
v_dir_5361_ = lean_ctor_get(v___x_5360_, 4);
lean_inc_ref(v___y_5321_);
lean_inc_ref(v_dir_5361_);
v___x_5362_ = l_Lake_PackageEntry_materialize(v_val_5359_, v_lakeEnv_5339_, v_dir_5361_, v___y_5321_, v___y_5328_);
if (lean_obj_tag(v___x_5362_) == 0)
{
lean_object* v_a_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5437_; 
v_a_5363_ = lean_ctor_get(v___x_5362_, 0);
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5437_ == 0)
{
v___x_5365_ = v___x_5362_;
v_isShared_5366_ = v_isSharedCheck_5437_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_a_5363_);
lean_dec(v___x_5362_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5437_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___x_5367_; lean_object* v___x_5368_; 
v___x_5367_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_5322_);
lean_inc(v_opts_5356_);
v___x_5368_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5334_, v_a_5363_, v_opts_5356_, v_leanOpts_5322_, v_reconfigure_5323_, v___x_5367_);
if (lean_obj_tag(v___x_5368_) == 0)
{
lean_object* v_a_5369_; lean_object* v_a_5370_; lean_object* v_wsIdx_5371_; lean_object* v___x_5372_; lean_object* v___x_5374_; 
lean_del_object(v___x_5365_);
v_a_5369_ = lean_ctor_get(v___x_5368_, 0);
lean_inc(v_a_5369_);
v_a_5370_ = lean_ctor_get(v___x_5368_, 1);
lean_inc(v_a_5370_);
lean_dec_ref_known(v___x_5368_, 2);
v_wsIdx_5371_ = lean_array_get_size(v_packages_5340_);
lean_dec_ref(v_packages_5340_);
v___x_5372_ = lean_array_push(v_depIdxs_5335_, v_wsIdx_5371_);
if (v_isShared_5338_ == 0)
{
lean_ctor_set(v___x_5337_, 1, v___x_5372_);
lean_ctor_set(v___x_5337_, 0, v_a_5369_);
v___x_5374_ = v___x_5337_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_a_5369_);
lean_ctor_set(v_reuseFailAlloc_5405_, 1, v___x_5372_);
v___x_5374_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
lean_object* v___x_5375_; uint8_t v___x_5376_; 
v___x_5375_ = lean_array_get_size(v_a_5370_);
v___x_5376_ = lean_nat_dec_lt(v___x_5345_, v___x_5375_);
if (v___x_5376_ == 0)
{
lean_object* v___x_5377_; 
lean_dec(v_a_5370_);
v___x_5377_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5319_, v___y_5320_, v___y_5321_, v_leanOpts_5322_, v_reconfigure_5323_, v_as_5324_, v___x_5342_, v_stop_5326_, v___x_5374_, v___y_5328_);
return v___x_5377_;
}
else
{
lean_object* v___x_5378_; uint8_t v___x_5379_; 
v___x_5378_ = lean_box(0);
v___x_5379_ = lean_nat_dec_le(v___x_5375_, v___x_5375_);
if (v___x_5379_ == 0)
{
if (v___x_5376_ == 0)
{
lean_object* v___x_5380_; 
lean_dec(v_a_5370_);
v___x_5380_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5319_, v___y_5320_, v___y_5321_, v_leanOpts_5322_, v_reconfigure_5323_, v_as_5324_, v___x_5342_, v_stop_5326_, v___x_5374_, v___y_5328_);
return v___x_5380_;
}
else
{
size_t v___x_5381_; size_t v___x_5382_; lean_object* v___x_5383_; 
v___x_5381_ = ((size_t)0ULL);
v___x_5382_ = lean_usize_of_nat(v___x_5375_);
v___x_5383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5370_, v___x_5381_, v___x_5382_, v___x_5378_, v___y_5328_);
lean_dec(v_a_5370_);
if (lean_obj_tag(v___x_5383_) == 0)
{
lean_object* v___x_5384_; 
lean_dec_ref_known(v___x_5383_, 1);
v___x_5384_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5319_, v___y_5320_, v___y_5321_, v_leanOpts_5322_, v_reconfigure_5323_, v_as_5324_, v___x_5342_, v_stop_5326_, v___x_5374_, v___y_5328_);
return v___x_5384_;
}
else
{
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5392_; 
lean_dec_ref(v___x_5374_);
lean_dec_ref(v_leanOpts_5322_);
lean_dec_ref(v___y_5321_);
lean_dec_ref(v_pkg_5319_);
v_a_5385_ = lean_ctor_get(v___x_5383_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5383_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5387_ = v___x_5383_;
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5383_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v___x_5390_; 
if (v_isShared_5388_ == 0)
{
v___x_5390_ = v___x_5387_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
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
}
else
{
size_t v___x_5393_; size_t v___x_5394_; lean_object* v___x_5395_; 
v___x_5393_ = ((size_t)0ULL);
v___x_5394_ = lean_usize_of_nat(v___x_5375_);
v___x_5395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5370_, v___x_5393_, v___x_5394_, v___x_5378_, v___y_5328_);
lean_dec(v_a_5370_);
if (lean_obj_tag(v___x_5395_) == 0)
{
lean_object* v___x_5396_; 
lean_dec_ref_known(v___x_5395_, 1);
v___x_5396_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5319_, v___y_5320_, v___y_5321_, v_leanOpts_5322_, v_reconfigure_5323_, v_as_5324_, v___x_5342_, v_stop_5326_, v___x_5374_, v___y_5328_);
return v___x_5396_;
}
else
{
lean_object* v_a_5397_; lean_object* v___x_5399_; uint8_t v_isShared_5400_; uint8_t v_isSharedCheck_5404_; 
lean_dec_ref(v___x_5374_);
lean_dec_ref(v_leanOpts_5322_);
lean_dec_ref(v___y_5321_);
lean_dec_ref(v_pkg_5319_);
v_a_5397_ = lean_ctor_get(v___x_5395_, 0);
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5395_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5399_ = v___x_5395_;
v_isShared_5400_ = v_isSharedCheck_5404_;
goto v_resetjp_5398_;
}
else
{
lean_inc(v_a_5397_);
lean_dec(v___x_5395_);
v___x_5399_ = lean_box(0);
v_isShared_5400_ = v_isSharedCheck_5404_;
goto v_resetjp_5398_;
}
v_resetjp_5398_:
{
lean_object* v___x_5402_; 
if (v_isShared_5400_ == 0)
{
v___x_5402_ = v___x_5399_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_a_5397_);
v___x_5402_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
return v___x_5402_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5406_; lean_object* v___x_5407_; uint8_t v___x_5408_; 
lean_dec_ref(v_packages_5340_);
lean_del_object(v___x_5337_);
lean_dec_ref(v_depIdxs_5335_);
lean_dec_ref(v_leanOpts_5322_);
lean_dec_ref(v___y_5321_);
lean_dec_ref(v_pkg_5319_);
v_a_5406_ = lean_ctor_get(v___x_5368_, 1);
lean_inc(v_a_5406_);
lean_dec_ref_known(v___x_5368_, 2);
v___x_5407_ = lean_array_get_size(v_a_5406_);
v___x_5408_ = lean_nat_dec_lt(v___x_5345_, v___x_5407_);
if (v___x_5408_ == 0)
{
lean_object* v___x_5409_; lean_object* v___x_5411_; 
lean_dec(v_a_5406_);
v___x_5409_ = lean_box(0);
if (v_isShared_5366_ == 0)
{
lean_ctor_set_tag(v___x_5365_, 1);
lean_ctor_set(v___x_5365_, 0, v___x_5409_);
v___x_5411_ = v___x_5365_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v___x_5409_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
return v___x_5411_;
}
}
else
{
lean_object* v___x_5413_; uint8_t v___x_5414_; 
lean_del_object(v___x_5365_);
v___x_5413_ = lean_box(0);
v___x_5414_ = lean_nat_dec_le(v___x_5407_, v___x_5407_);
if (v___x_5414_ == 0)
{
if (v___x_5408_ == 0)
{
lean_dec(v_a_5406_);
goto v___jp_5330_;
}
else
{
size_t v___x_5415_; size_t v___x_5416_; lean_object* v___x_5417_; 
v___x_5415_ = ((size_t)0ULL);
v___x_5416_ = lean_usize_of_nat(v___x_5407_);
v___x_5417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5406_, v___x_5415_, v___x_5416_, v___x_5413_, v___y_5328_);
lean_dec(v_a_5406_);
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_dec_ref_known(v___x_5417_, 1);
goto v___jp_5330_;
}
else
{
lean_object* v_a_5418_; lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5425_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5425_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5420_ = v___x_5417_;
v_isShared_5421_ = v_isSharedCheck_5425_;
goto v_resetjp_5419_;
}
else
{
lean_inc(v_a_5418_);
lean_dec(v___x_5417_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5425_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v___x_5423_; 
if (v_isShared_5421_ == 0)
{
v___x_5423_ = v___x_5420_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_a_5418_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
return v___x_5423_;
}
}
}
}
}
else
{
size_t v___x_5426_; size_t v___x_5427_; lean_object* v___x_5428_; 
v___x_5426_ = ((size_t)0ULL);
v___x_5427_ = lean_usize_of_nat(v___x_5407_);
v___x_5428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5406_, v___x_5426_, v___x_5427_, v___x_5413_, v___y_5328_);
lean_dec(v_a_5406_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_dec_ref_known(v___x_5428_, 1);
goto v___jp_5330_;
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5428_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5428_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
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
lean_object* v_a_5438_; lean_object* v___x_5440_; uint8_t v_isShared_5441_; uint8_t v_isSharedCheck_5445_; 
lean_dec_ref(v_packages_5340_);
lean_del_object(v___x_5337_);
lean_dec_ref(v_depIdxs_5335_);
lean_dec_ref(v_ws_5334_);
lean_dec_ref(v_leanOpts_5322_);
lean_dec_ref(v___y_5321_);
lean_dec_ref(v_pkg_5319_);
v_a_5438_ = lean_ctor_get(v___x_5362_, 0);
v_isSharedCheck_5445_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5445_ == 0)
{
v___x_5440_ = v___x_5362_;
v_isShared_5441_ = v_isSharedCheck_5445_;
goto v_resetjp_5439_;
}
else
{
lean_inc(v_a_5438_);
lean_dec(v___x_5362_);
v___x_5440_ = lean_box(0);
v_isShared_5441_ = v_isSharedCheck_5445_;
goto v_resetjp_5439_;
}
v_resetjp_5439_:
{
lean_object* v___x_5443_; 
if (v_isShared_5441_ == 0)
{
v___x_5443_ = v___x_5440_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5438_);
v___x_5443_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
return v___x_5443_;
}
}
}
}
else
{
uint8_t v___x_5446_; 
lean_inc(v_baseName_5354_);
lean_inc(v_wsIdx_5353_);
lean_dec(v___x_5358_);
lean_dec_ref(v_packages_5340_);
lean_del_object(v___x_5337_);
lean_dec_ref(v_depIdxs_5335_);
lean_dec_ref(v_ws_5334_);
lean_dec_ref(v_leanOpts_5322_);
lean_dec_ref(v___y_5321_);
lean_dec_ref(v_pkg_5319_);
v___x_5446_ = lean_nat_dec_eq(v_wsIdx_5353_, v___x_5345_);
lean_dec(v_wsIdx_5353_);
if (v___x_5446_ == 0)
{
lean_object* v___x_5447_; uint8_t v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; uint8_t v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___x_5447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5448_ = 1;
lean_inc(v_name_5355_);
v___x_5449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5355_, v___x_5448_);
v___x_5450_ = lean_string_append(v___x_5447_, v___x_5449_);
lean_dec_ref(v___x_5449_);
v___x_5451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5452_ = lean_string_append(v___x_5450_, v___x_5451_);
v___x_5453_ = l_Lean_Name_toString(v_baseName_5354_, v___x_5446_);
v___x_5454_ = lean_string_append(v___x_5452_, v___x_5453_);
lean_dec_ref(v___x_5453_);
v___x_5455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5456_ = lean_string_append(v___x_5454_, v___x_5455_);
v___x_5457_ = 3;
v___x_5458_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5458_, 0, v___x_5456_);
lean_ctor_set_uint8(v___x_5458_, sizeof(void*)*1, v___x_5457_);
lean_inc_ref(v___y_5328_);
v___x_5459_ = lean_apply_2(v___y_5328_, v___x_5458_, lean_box(0));
v___x_5460_ = lean_box(0);
v___x_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5461_, 0, v___x_5460_);
return v___x_5461_;
}
else
{
lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; uint8_t v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; 
lean_dec(v_baseName_5354_);
v___x_5462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5355_);
v___x_5463_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5355_, v___x_5446_);
v___x_5464_ = lean_string_append(v___x_5462_, v___x_5463_);
v___x_5465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5466_ = lean_string_append(v___x_5464_, v___x_5465_);
v___x_5467_ = lean_string_append(v___x_5466_, v___x_5463_);
lean_dec_ref(v___x_5463_);
v___x_5468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5469_ = lean_string_append(v___x_5467_, v___x_5468_);
v___x_5470_ = 3;
v___x_5471_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5471_, 0, v___x_5469_);
lean_ctor_set_uint8(v___x_5471_, sizeof(void*)*1, v___x_5470_);
lean_inc_ref(v___y_5328_);
v___x_5472_ = lean_apply_2(v___y_5328_, v___x_5471_, lean_box(0));
v___x_5473_ = lean_box(0);
v___x_5474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5474_, 0, v___x_5473_);
return v___x_5474_;
}
}
}
else
{
lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; uint8_t v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; 
lean_inc(v_baseName_5354_);
lean_dec_ref(v_packages_5340_);
lean_del_object(v___x_5337_);
lean_dec_ref(v_depIdxs_5335_);
lean_dec_ref(v_ws_5334_);
lean_dec_ref(v_leanOpts_5322_);
lean_dec_ref(v___y_5321_);
lean_dec_ref(v_pkg_5319_);
v___x_5475_ = l_Lean_Name_toString(v_baseName_5354_, v___x_5333_);
v___x_5476_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5477_ = lean_string_append(v___x_5475_, v___x_5476_);
v___x_5478_ = 3;
v___x_5479_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5479_, 0, v___x_5477_);
lean_ctor_set_uint8(v___x_5479_, sizeof(void*)*1, v___x_5478_);
lean_inc_ref(v___y_5328_);
v___x_5480_ = lean_apply_2(v___y_5328_, v___x_5479_, lean_box(0));
v___x_5481_ = lean_box(0);
v___x_5482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5481_);
return v___x_5482_;
}
}
}
}
else
{
lean_object* v___x_5484_; 
lean_dec_ref(v_leanOpts_5322_);
lean_dec_ref(v___y_5321_);
lean_dec_ref(v_pkg_5319_);
v___x_5484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5484_, 0, v_b_5327_);
return v___x_5484_;
}
v___jp_5330_:
{
lean_object* v___x_5331_; lean_object* v___x_5332_; 
v___x_5331_ = lean_box(0);
v___x_5332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5332_, 0, v___x_5331_);
return v___x_5332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_start_5485_, lean_object* v_pkg_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v_leanOpts_5489_, lean_object* v_reconfigure_5490_, lean_object* v_as_5491_, lean_object* v_i_5492_, lean_object* v_stop_5493_, lean_object* v_b_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_){
_start:
{
uint8_t v_reconfigure_boxed_5497_; size_t v_i_boxed_5498_; size_t v_stop_boxed_5499_; lean_object* v_res_5500_; 
v_reconfigure_boxed_5497_ = lean_unbox(v_reconfigure_5490_);
v_i_boxed_5498_ = lean_unbox_usize(v_i_5492_);
lean_dec(v_i_5492_);
v_stop_boxed_5499_ = lean_unbox_usize(v_stop_5493_);
lean_dec(v_stop_5493_);
v_res_5500_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5485_, v_pkg_5486_, v___y_5487_, v___y_5488_, v_leanOpts_5489_, v_reconfigure_boxed_5497_, v_as_5491_, v_i_boxed_5498_, v_stop_boxed_5499_, v_b_5494_, v___y_5495_);
lean_dec_ref(v___y_5495_);
lean_dec_ref(v_as_5491_);
lean_dec(v___y_5487_);
lean_dec(v_start_5485_);
return v_res_5500_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v_leanOpts_5503_, uint8_t v_reconfigure_5504_, lean_object* v_ws_5505_, lean_object* v_i_5506_, lean_object* v_next_5507_, lean_object* v___y_5508_){
_start:
{
lean_object* v_packages_5510_; lean_object* v_pkg_5511_; lean_object* v_ws_5513_; lean_object* v_depIdxs_5514_; lean_object* v___y_5515_; lean_object* v_____x_5525_; lean_object* v___y_5526_; lean_object* v_depConfigs_5529_; lean_object* v_start_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v_s_5533_; lean_object* v___x_5534_; uint8_t v___x_5535_; 
v_packages_5510_ = lean_ctor_get(v_ws_5505_, 4);
v_pkg_5511_ = lean_array_fget(v_packages_5510_, v_i_5506_);
lean_dec(v_i_5506_);
v_depConfigs_5529_ = lean_ctor_get(v_pkg_5511_, 12);
v_start_5530_ = lean_array_get_size(v_packages_5510_);
v___x_5531_ = lean_array_get_size(v_depConfigs_5529_);
v___x_5532_ = lean_mk_empty_array_with_capacity(v___x_5531_);
lean_inc_ref(v___x_5532_);
lean_inc_ref(v_ws_5505_);
v_s_5533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5533_, 0, v_ws_5505_);
lean_ctor_set(v_s_5533_, 1, v___x_5532_);
v___x_5534_ = lean_unsigned_to_nat(0u);
v___x_5535_ = lean_nat_dec_le(v___x_5531_, v___x_5531_);
if (v___x_5535_ == 0)
{
uint8_t v___x_5536_; 
v___x_5536_ = lean_nat_dec_lt(v___x_5534_, v___x_5531_);
if (v___x_5536_ == 0)
{
lean_object* v_ws_5537_; lean_object* v_packages_5538_; lean_object* v___x_5539_; uint8_t v___x_5540_; 
lean_dec_ref_known(v_s_5533_, 2);
v_ws_5537_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5505_, v_pkg_5511_, v___x_5532_);
v_packages_5538_ = lean_ctor_get(v_ws_5537_, 4);
lean_inc_ref(v_packages_5538_);
v___x_5539_ = lean_array_get_size(v_packages_5538_);
lean_dec_ref(v_packages_5538_);
v___x_5540_ = lean_nat_dec_lt(v_next_5507_, v___x_5539_);
if (v___x_5540_ == 0)
{
lean_object* v___x_5541_; 
lean_dec(v_next_5507_);
lean_dec_ref(v_leanOpts_5503_);
lean_dec_ref(v___y_5502_);
v___x_5541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5541_, 0, v_ws_5537_);
return v___x_5541_;
}
else
{
lean_object* v___x_5542_; lean_object* v___x_5543_; 
v___x_5542_ = lean_unsigned_to_nat(1u);
v___x_5543_ = lean_nat_add(v_next_5507_, v___x_5542_);
v_ws_5505_ = v_ws_5537_;
v_i_5506_ = v_next_5507_;
v_next_5507_ = v___x_5543_;
goto _start;
}
}
else
{
size_t v___x_5545_; size_t v___x_5546_; lean_object* v___x_5547_; 
lean_dec_ref(v___x_5532_);
lean_dec_ref(v_ws_5505_);
v___x_5545_ = lean_usize_of_nat(v___x_5531_);
v___x_5546_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5503_);
lean_inc_ref(v___y_5502_);
lean_inc(v_pkg_5511_);
v___x_5547_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5530_, v_pkg_5511_, v___y_5501_, v___y_5502_, v_leanOpts_5503_, v_reconfigure_5504_, v_depConfigs_5529_, v___x_5545_, v___x_5546_, v_s_5533_, v___y_5508_);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_object* v_a_5548_; 
v_a_5548_ = lean_ctor_get(v___x_5547_, 0);
lean_inc(v_a_5548_);
lean_dec_ref_known(v___x_5547_, 1);
v_____x_5525_ = v_a_5548_;
v___y_5526_ = v___y_5508_;
goto v___jp_5524_;
}
else
{
lean_object* v_a_5549_; lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5556_; 
lean_dec(v_pkg_5511_);
lean_dec(v_next_5507_);
lean_dec_ref(v_leanOpts_5503_);
lean_dec_ref(v___y_5502_);
v_a_5549_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5556_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5556_ == 0)
{
v___x_5551_ = v___x_5547_;
v_isShared_5552_ = v_isSharedCheck_5556_;
goto v_resetjp_5550_;
}
else
{
lean_inc(v_a_5549_);
lean_dec(v___x_5547_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5556_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v___x_5554_; 
if (v_isShared_5552_ == 0)
{
v___x_5554_ = v___x_5551_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v_a_5549_);
v___x_5554_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
return v___x_5554_;
}
}
}
}
}
else
{
uint8_t v___x_5557_; 
v___x_5557_ = lean_nat_dec_lt(v___x_5534_, v___x_5531_);
if (v___x_5557_ == 0)
{
lean_dec_ref_known(v_s_5533_, 2);
v_ws_5513_ = v_ws_5505_;
v_depIdxs_5514_ = v___x_5532_;
v___y_5515_ = v___y_5508_;
goto v___jp_5512_;
}
else
{
size_t v___x_5558_; size_t v___x_5559_; lean_object* v___x_5560_; 
lean_dec_ref(v___x_5532_);
lean_dec_ref(v_ws_5505_);
v___x_5558_ = lean_usize_of_nat(v___x_5531_);
v___x_5559_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5503_);
lean_inc_ref(v___y_5502_);
lean_inc(v_pkg_5511_);
v___x_5560_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5530_, v_pkg_5511_, v___y_5501_, v___y_5502_, v_leanOpts_5503_, v_reconfigure_5504_, v_depConfigs_5529_, v___x_5558_, v___x_5559_, v_s_5533_, v___y_5508_);
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v_a_5561_; 
v_a_5561_ = lean_ctor_get(v___x_5560_, 0);
lean_inc(v_a_5561_);
lean_dec_ref_known(v___x_5560_, 1);
v_____x_5525_ = v_a_5561_;
v___y_5526_ = v___y_5508_;
goto v___jp_5524_;
}
else
{
lean_object* v_a_5562_; lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5569_; 
lean_dec(v_pkg_5511_);
lean_dec(v_next_5507_);
lean_dec_ref(v_leanOpts_5503_);
lean_dec_ref(v___y_5502_);
v_a_5562_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5569_ == 0)
{
v___x_5564_ = v___x_5560_;
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
else
{
lean_inc(v_a_5562_);
lean_dec(v___x_5560_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5567_; 
if (v_isShared_5565_ == 0)
{
v___x_5567_ = v___x_5564_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5562_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
}
}
v___jp_5512_:
{
lean_object* v_ws_5516_; lean_object* v_packages_5517_; lean_object* v___x_5518_; uint8_t v___x_5519_; 
v_ws_5516_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5513_, v_pkg_5511_, v_depIdxs_5514_);
v_packages_5517_ = lean_ctor_get(v_ws_5516_, 4);
lean_inc_ref(v_packages_5517_);
v___x_5518_ = lean_array_get_size(v_packages_5517_);
lean_dec_ref(v_packages_5517_);
v___x_5519_ = lean_nat_dec_lt(v_next_5507_, v___x_5518_);
if (v___x_5519_ == 0)
{
lean_object* v___x_5520_; 
lean_dec(v_next_5507_);
lean_dec_ref(v_leanOpts_5503_);
lean_dec_ref(v___y_5502_);
v___x_5520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5520_, 0, v_ws_5516_);
return v___x_5520_;
}
else
{
lean_object* v___x_5521_; lean_object* v___x_5522_; 
v___x_5521_ = lean_unsigned_to_nat(1u);
v___x_5522_ = lean_nat_add(v_next_5507_, v___x_5521_);
v_ws_5505_ = v_ws_5516_;
v_i_5506_ = v_next_5507_;
v_next_5507_ = v___x_5522_;
v___y_5508_ = v___y_5515_;
goto _start;
}
}
v___jp_5524_:
{
lean_object* v_ws_5527_; lean_object* v_depIdxs_5528_; 
v_ws_5527_ = lean_ctor_get(v_____x_5525_, 0);
lean_inc_ref(v_ws_5527_);
v_depIdxs_5528_ = lean_ctor_get(v_____x_5525_, 1);
lean_inc_ref(v_depIdxs_5528_);
lean_dec_ref(v_____x_5525_);
v_ws_5513_ = v_ws_5527_;
v_depIdxs_5514_ = v_depIdxs_5528_;
v___y_5515_ = v___y_5526_;
goto v___jp_5512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v_leanOpts_5572_, lean_object* v_reconfigure_5573_, lean_object* v_ws_5574_, lean_object* v_i_5575_, lean_object* v_next_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_){
_start:
{
uint8_t v_reconfigure_boxed_5579_; lean_object* v_res_5580_; 
v_reconfigure_boxed_5579_ = lean_unbox(v_reconfigure_5573_);
v_res_5580_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5570_, v___y_5571_, v_leanOpts_5572_, v_reconfigure_boxed_5579_, v_ws_5574_, v_i_5575_, v_next_5576_, v___y_5577_);
lean_dec_ref(v___y_5577_);
lean_dec(v___y_5570_);
return v_res_5580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(lean_object* v_as_5581_, size_t v_i_5582_, size_t v_stop_5583_, lean_object* v_b_5584_){
_start:
{
uint8_t v___x_5585_; 
v___x_5585_ = lean_usize_dec_eq(v_i_5582_, v_stop_5583_);
if (v___x_5585_ == 0)
{
lean_object* v___x_5586_; lean_object* v_name_5587_; lean_object* v___x_5588_; size_t v___x_5589_; size_t v___x_5590_; 
v___x_5586_ = lean_array_uget_borrowed(v_as_5581_, v_i_5582_);
v_name_5587_ = lean_ctor_get(v___x_5586_, 0);
lean_inc(v___x_5586_);
lean_inc(v_name_5587_);
v___x_5588_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5587_, v___x_5586_, v_b_5584_);
v___x_5589_ = ((size_t)1ULL);
v___x_5590_ = lean_usize_add(v_i_5582_, v___x_5589_);
v_i_5582_ = v___x_5590_;
v_b_5584_ = v___x_5588_;
goto _start;
}
else
{
return v_b_5584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2___boxed(lean_object* v_as_5592_, lean_object* v_i_5593_, lean_object* v_stop_5594_, lean_object* v_b_5595_){
_start:
{
size_t v_i_boxed_5596_; size_t v_stop_boxed_5597_; lean_object* v_res_5598_; 
v_i_boxed_5596_ = lean_unbox_usize(v_i_5593_);
lean_dec(v_i_5593_);
v_stop_boxed_5597_ = lean_unbox_usize(v_stop_5594_);
lean_dec(v_stop_5594_);
v_res_5598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5592_, v_i_boxed_5596_, v_stop_boxed_5597_, v_b_5595_);
lean_dec_ref(v_as_5592_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5599_, size_t v_i_5600_, size_t v_stop_5601_, lean_object* v_b_5602_){
_start:
{
uint8_t v___x_5603_; 
v___x_5603_ = lean_usize_dec_eq(v_i_5600_, v_stop_5601_);
if (v___x_5603_ == 0)
{
lean_object* v___x_5604_; lean_object* v_name_5605_; lean_object* v___x_5606_; size_t v___x_5607_; size_t v___x_5608_; lean_object* v___x_5609_; 
v___x_5604_ = lean_array_uget_borrowed(v_as_5599_, v_i_5600_);
v_name_5605_ = lean_ctor_get(v___x_5604_, 0);
lean_inc(v___x_5604_);
lean_inc(v_name_5605_);
v___x_5606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5605_, v___x_5604_, v_b_5602_);
v___x_5607_ = ((size_t)1ULL);
v___x_5608_ = lean_usize_add(v_i_5600_, v___x_5607_);
v___x_5609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5599_, v___x_5608_, v_stop_5601_, v___x_5606_);
return v___x_5609_;
}
else
{
return v_b_5602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5610_, lean_object* v_i_5611_, lean_object* v_stop_5612_, lean_object* v_b_5613_){
_start:
{
size_t v_i_boxed_5614_; size_t v_stop_boxed_5615_; lean_object* v_res_5616_; 
v_i_boxed_5614_ = lean_unbox_usize(v_i_5611_);
lean_dec(v_i_5611_);
v_stop_boxed_5615_ = lean_unbox_usize(v_stop_5612_);
lean_dec(v_stop_5612_);
v_res_5616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5610_, v_i_boxed_5614_, v_stop_boxed_5615_, v_b_5613_);
lean_dec_ref(v_as_5610_);
return v_res_5616_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5626_, lean_object* v_manifest_5627_, lean_object* v_leanOpts_5628_, uint8_t v_reconfigure_5629_, lean_object* v_overrides_5630_, lean_object* v_a_5631_){
_start:
{
lean_object* v___y_5634_; lean_object* v___y_5635_; lean_object* v___y_5636_; lean_object* v___y_5637_; lean_object* v___y_5638_; lean_object* v___y_5651_; lean_object* v___y_5652_; lean_object* v___y_5653_; lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v___y_5657_; lean_object* v___y_5665_; lean_object* v___y_5666_; lean_object* v___y_5667_; lean_object* v___y_5668_; lean_object* v___y_5669_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v___y_5682_; lean_object* v___y_5683_; lean_object* v___y_5684_; lean_object* v___y_5685_; lean_object* v_packagesDir_x3f_5728_; lean_object* v_packages_5729_; lean_object* v___y_5731_; lean_object* v___y_5732_; lean_object* v___y_5745_; lean_object* v___x_5753_; lean_object* v___x_5754_; uint8_t v___x_5755_; 
v_packagesDir_x3f_5728_ = lean_ctor_get(v_manifest_5627_, 2);
lean_inc(v_packagesDir_x3f_5728_);
v_packages_5729_ = lean_ctor_get(v_manifest_5627_, 3);
lean_inc_ref(v_packages_5729_);
lean_dec_ref(v_manifest_5627_);
v___x_5753_ = lean_array_get_size(v_packages_5729_);
v___x_5754_ = lean_unsigned_to_nat(0u);
v___x_5755_ = lean_nat_dec_eq(v___x_5753_, v___x_5754_);
if (v___x_5755_ == 0)
{
lean_object* v_packages_5756_; lean_object* v___x_5757_; lean_object* v_config_5758_; lean_object* v_toWorkspaceConfig_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; uint8_t v___x_5763_; 
v_packages_5756_ = lean_ctor_get(v_ws_5626_, 4);
v___x_5757_ = lean_array_fget_borrowed(v_packages_5756_, v___x_5754_);
v_config_5758_ = lean_ctor_get(v___x_5757_, 6);
v_toWorkspaceConfig_5759_ = lean_ctor_get(v_config_5758_, 0);
lean_inc_ref(v_toWorkspaceConfig_5759_);
v___x_5760_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5759_);
v___x_5761_ = l_Lake_mkRelPathString(v___x_5760_);
v___x_5762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5761_);
v___x_5763_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5728_, v___x_5762_);
lean_dec_ref_known(v___x_5762_, 1);
if (v___x_5763_ == 0)
{
lean_object* v___x_5764_; lean_object* v___x_5765_; 
v___x_5764_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5631_);
v___x_5765_ = lean_apply_2(v_a_5631_, v___x_5764_, lean_box(0));
v___y_5745_ = v_a_5631_;
goto v___jp_5744_;
}
else
{
v___y_5745_ = v_a_5631_;
goto v___jp_5744_;
}
}
else
{
v___y_5745_ = v_a_5631_;
goto v___jp_5744_;
}
v___jp_5633_:
{
lean_object* v___x_5639_; lean_object* v___x_5640_; 
v___x_5639_ = lean_array_get_size(v___y_5638_);
lean_dec_ref(v___y_5638_);
v___x_5640_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5635_, v___y_5636_, v_leanOpts_5628_, v_reconfigure_5629_, v_ws_5626_, v___y_5634_, v___x_5639_, v___y_5637_);
lean_dec(v___y_5635_);
if (lean_obj_tag(v___x_5640_) == 0)
{
lean_object* v_a_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5649_; 
v_a_5641_ = lean_ctor_get(v___x_5640_, 0);
v_isSharedCheck_5649_ = !lean_is_exclusive(v___x_5640_);
if (v_isSharedCheck_5649_ == 0)
{
v___x_5643_ = v___x_5640_;
v_isShared_5644_ = v_isSharedCheck_5649_;
goto v_resetjp_5642_;
}
else
{
lean_inc(v_a_5641_);
lean_dec(v___x_5640_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5649_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v___x_5645_; lean_object* v___x_5647_; 
v___x_5645_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_a_5641_);
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 0, v___x_5645_);
v___x_5647_ = v___x_5643_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v___x_5645_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
}
else
{
return v___x_5640_;
}
}
v___jp_5650_:
{
if (lean_obj_tag(v___y_5657_) == 0)
{
lean_dec_ref(v___y_5653_);
v___y_5634_ = v___y_5652_;
v___y_5635_ = v___y_5657_;
v___y_5636_ = v___y_5654_;
v___y_5637_ = v___y_5655_;
v___y_5638_ = v___y_5656_;
goto v___jp_5633_;
}
else
{
lean_object* v___x_5658_; uint8_t v___x_5659_; 
v___x_5658_ = lean_array_get_size(v___y_5653_);
lean_dec_ref(v___y_5653_);
v___x_5659_ = lean_nat_dec_eq(v___x_5658_, v___y_5651_);
if (v___x_5659_ == 0)
{
lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; 
lean_dec_ref(v___y_5656_);
lean_dec_ref(v___y_5654_);
lean_dec(v___y_5652_);
lean_dec_ref(v_leanOpts_5628_);
lean_dec_ref(v_ws_5626_);
v___x_5660_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5655_);
v___x_5661_ = lean_apply_2(v___y_5655_, v___x_5660_, lean_box(0));
v___x_5662_ = lean_box(0);
v___x_5663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
return v___x_5663_;
}
else
{
v___y_5634_ = v___y_5652_;
v___y_5635_ = v___y_5657_;
v___y_5636_ = v___y_5654_;
v___y_5637_ = v___y_5655_;
v___y_5638_ = v___y_5656_;
goto v___jp_5633_;
}
}
}
v___jp_5664_:
{
lean_object* v___x_5672_; uint8_t v___x_5673_; 
v___x_5672_ = lean_array_get_size(v_overrides_5630_);
v___x_5673_ = lean_nat_dec_lt(v___y_5665_, v___x_5672_);
if (v___x_5673_ == 0)
{
v___y_5651_ = v___y_5665_;
v___y_5652_ = v___y_5666_;
v___y_5653_ = v___y_5667_;
v___y_5654_ = v___y_5668_;
v___y_5655_ = v___y_5669_;
v___y_5656_ = v___y_5670_;
v___y_5657_ = v___y_5671_;
goto v___jp_5650_;
}
else
{
uint8_t v___x_5674_; 
v___x_5674_ = lean_nat_dec_le(v___x_5672_, v___x_5672_);
if (v___x_5674_ == 0)
{
if (v___x_5673_ == 0)
{
v___y_5651_ = v___y_5665_;
v___y_5652_ = v___y_5666_;
v___y_5653_ = v___y_5667_;
v___y_5654_ = v___y_5668_;
v___y_5655_ = v___y_5669_;
v___y_5656_ = v___y_5670_;
v___y_5657_ = v___y_5671_;
goto v___jp_5650_;
}
else
{
size_t v___x_5675_; size_t v___x_5676_; lean_object* v___x_5677_; 
v___x_5675_ = ((size_t)0ULL);
v___x_5676_ = lean_usize_of_nat(v___x_5672_);
v___x_5677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5630_, v___x_5675_, v___x_5676_, v___y_5671_);
v___y_5651_ = v___y_5665_;
v___y_5652_ = v___y_5666_;
v___y_5653_ = v___y_5667_;
v___y_5654_ = v___y_5668_;
v___y_5655_ = v___y_5669_;
v___y_5656_ = v___y_5670_;
v___y_5657_ = v___x_5677_;
goto v___jp_5650_;
}
}
else
{
size_t v___x_5678_; size_t v___x_5679_; lean_object* v___x_5680_; 
v___x_5678_ = ((size_t)0ULL);
v___x_5679_ = lean_usize_of_nat(v___x_5672_);
v___x_5680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5630_, v___x_5678_, v___x_5679_, v___y_5671_);
v___y_5651_ = v___y_5665_;
v___y_5652_ = v___y_5666_;
v___y_5653_ = v___y_5667_;
v___y_5654_ = v___y_5668_;
v___y_5655_ = v___y_5669_;
v___y_5656_ = v___y_5670_;
v___y_5657_ = v___x_5680_;
goto v___jp_5650_;
}
}
}
v___jp_5681_:
{
lean_object* v_packages_5686_; lean_object* v___x_5687_; lean_object* v_wsIdx_5688_; lean_object* v_dir_5689_; lean_object* v_depConfigs_5690_; lean_object* v___x_5691_; 
v_packages_5686_ = lean_ctor_get(v_ws_5626_, 4);
v___x_5687_ = lean_array_fget_borrowed(v_packages_5686_, v___y_5682_);
v_wsIdx_5688_ = lean_ctor_get(v___x_5687_, 0);
v_dir_5689_ = lean_ctor_get(v___x_5687_, 4);
v_depConfigs_5690_ = lean_ctor_get(v___x_5687_, 12);
v___x_5691_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5685_, v_depConfigs_5690_, v___y_5684_);
if (lean_obj_tag(v___x_5691_) == 0)
{
lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; 
lean_dec_ref_known(v___x_5691_, 1);
v___x_5692_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5689_);
v___x_5693_ = l_Lake_joinRelative(v_dir_5689_, v___x_5692_);
v___x_5694_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5695_ = l_Lake_joinRelative(v___x_5693_, v___x_5694_);
v___x_5696_ = l_Lake_Manifest_tryLoadEntries(v___x_5695_);
if (lean_obj_tag(v___x_5696_) == 0)
{
lean_object* v_a_5697_; lean_object* v___x_5698_; uint8_t v___x_5699_; 
v_a_5697_ = lean_ctor_get(v___x_5696_, 0);
lean_inc(v_a_5697_);
lean_dec_ref_known(v___x_5696_, 1);
v___x_5698_ = lean_array_get_size(v_a_5697_);
v___x_5699_ = lean_nat_dec_lt(v___y_5682_, v___x_5698_);
if (v___x_5699_ == 0)
{
lean_dec(v_a_5697_);
lean_inc_ref(v_packages_5686_);
lean_inc_ref(v_depConfigs_5690_);
lean_inc(v_wsIdx_5688_);
v___y_5665_ = v___y_5682_;
v___y_5666_ = v_wsIdx_5688_;
v___y_5667_ = v_depConfigs_5690_;
v___y_5668_ = v___y_5683_;
v___y_5669_ = v___y_5684_;
v___y_5670_ = v_packages_5686_;
v___y_5671_ = v___y_5685_;
goto v___jp_5664_;
}
else
{
uint8_t v___x_5700_; 
v___x_5700_ = lean_nat_dec_le(v___x_5698_, v___x_5698_);
if (v___x_5700_ == 0)
{
if (v___x_5699_ == 0)
{
lean_dec(v_a_5697_);
lean_inc_ref(v_packages_5686_);
lean_inc_ref(v_depConfigs_5690_);
lean_inc(v_wsIdx_5688_);
v___y_5665_ = v___y_5682_;
v___y_5666_ = v_wsIdx_5688_;
v___y_5667_ = v_depConfigs_5690_;
v___y_5668_ = v___y_5683_;
v___y_5669_ = v___y_5684_;
v___y_5670_ = v_packages_5686_;
v___y_5671_ = v___y_5685_;
goto v___jp_5664_;
}
else
{
size_t v___x_5701_; size_t v___x_5702_; lean_object* v___x_5703_; 
v___x_5701_ = ((size_t)0ULL);
v___x_5702_ = lean_usize_of_nat(v___x_5698_);
v___x_5703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5697_, v___x_5701_, v___x_5702_, v___y_5685_);
lean_dec(v_a_5697_);
lean_inc_ref(v_packages_5686_);
lean_inc_ref(v_depConfigs_5690_);
lean_inc(v_wsIdx_5688_);
v___y_5665_ = v___y_5682_;
v___y_5666_ = v_wsIdx_5688_;
v___y_5667_ = v_depConfigs_5690_;
v___y_5668_ = v___y_5683_;
v___y_5669_ = v___y_5684_;
v___y_5670_ = v_packages_5686_;
v___y_5671_ = v___x_5703_;
goto v___jp_5664_;
}
}
else
{
size_t v___x_5704_; size_t v___x_5705_; lean_object* v___x_5706_; 
v___x_5704_ = ((size_t)0ULL);
v___x_5705_ = lean_usize_of_nat(v___x_5698_);
v___x_5706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5697_, v___x_5704_, v___x_5705_, v___y_5685_);
lean_dec(v_a_5697_);
lean_inc_ref(v_packages_5686_);
lean_inc_ref(v_depConfigs_5690_);
lean_inc(v_wsIdx_5688_);
v___y_5665_ = v___y_5682_;
v___y_5666_ = v_wsIdx_5688_;
v___y_5667_ = v_depConfigs_5690_;
v___y_5668_ = v___y_5683_;
v___y_5669_ = v___y_5684_;
v___y_5670_ = v_packages_5686_;
v___y_5671_ = v___x_5706_;
goto v___jp_5664_;
}
}
}
else
{
lean_object* v_a_5707_; lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5719_; 
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5683_);
lean_dec_ref(v_leanOpts_5628_);
lean_dec_ref(v_ws_5626_);
v_a_5707_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_5719_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5719_ == 0)
{
v___x_5709_ = v___x_5696_;
v_isShared_5710_ = v_isSharedCheck_5719_;
goto v_resetjp_5708_;
}
else
{
lean_inc(v_a_5707_);
lean_dec(v___x_5696_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5719_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
lean_object* v___x_5711_; uint8_t v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5717_; 
v___x_5711_ = lean_io_error_to_string(v_a_5707_);
v___x_5712_ = 3;
v___x_5713_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5713_, 0, v___x_5711_);
lean_ctor_set_uint8(v___x_5713_, sizeof(void*)*1, v___x_5712_);
lean_inc_ref(v___y_5684_);
v___x_5714_ = lean_apply_2(v___y_5684_, v___x_5713_, lean_box(0));
v___x_5715_ = lean_box(0);
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 0, v___x_5715_);
v___x_5717_ = v___x_5709_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v___x_5715_);
v___x_5717_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
return v___x_5717_;
}
}
}
}
else
{
lean_object* v_a_5720_; lean_object* v___x_5722_; uint8_t v_isShared_5723_; uint8_t v_isSharedCheck_5727_; 
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5683_);
lean_dec_ref(v_leanOpts_5628_);
lean_dec_ref(v_ws_5626_);
v_a_5720_ = lean_ctor_get(v___x_5691_, 0);
v_isSharedCheck_5727_ = !lean_is_exclusive(v___x_5691_);
if (v_isSharedCheck_5727_ == 0)
{
v___x_5722_ = v___x_5691_;
v_isShared_5723_ = v_isSharedCheck_5727_;
goto v_resetjp_5721_;
}
else
{
lean_inc(v_a_5720_);
lean_dec(v___x_5691_);
v___x_5722_ = lean_box(0);
v_isShared_5723_ = v_isSharedCheck_5727_;
goto v_resetjp_5721_;
}
v_resetjp_5721_:
{
lean_object* v___x_5725_; 
if (v_isShared_5723_ == 0)
{
v___x_5725_ = v___x_5722_;
goto v_reusejp_5724_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_a_5720_);
v___x_5725_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5724_;
}
v_reusejp_5724_:
{
return v___x_5725_;
}
}
}
}
v___jp_5730_:
{
lean_object* v_pkgEntries_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; uint8_t v___x_5736_; 
v_pkgEntries_5733_ = lean_box(1);
v___x_5734_ = lean_unsigned_to_nat(0u);
v___x_5735_ = lean_array_get_size(v_packages_5729_);
v___x_5736_ = lean_nat_dec_lt(v___x_5734_, v___x_5735_);
if (v___x_5736_ == 0)
{
lean_dec_ref(v_packages_5729_);
v___y_5682_ = v___x_5734_;
v___y_5683_ = v___y_5732_;
v___y_5684_ = v___y_5731_;
v___y_5685_ = v_pkgEntries_5733_;
goto v___jp_5681_;
}
else
{
uint8_t v___x_5737_; 
v___x_5737_ = lean_nat_dec_le(v___x_5735_, v___x_5735_);
if (v___x_5737_ == 0)
{
if (v___x_5736_ == 0)
{
lean_dec_ref(v_packages_5729_);
v___y_5682_ = v___x_5734_;
v___y_5683_ = v___y_5732_;
v___y_5684_ = v___y_5731_;
v___y_5685_ = v_pkgEntries_5733_;
goto v___jp_5681_;
}
else
{
size_t v___x_5738_; size_t v___x_5739_; lean_object* v___x_5740_; 
v___x_5738_ = ((size_t)0ULL);
v___x_5739_ = lean_usize_of_nat(v___x_5735_);
v___x_5740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5729_, v___x_5738_, v___x_5739_, v_pkgEntries_5733_);
lean_dec_ref(v_packages_5729_);
v___y_5682_ = v___x_5734_;
v___y_5683_ = v___y_5732_;
v___y_5684_ = v___y_5731_;
v___y_5685_ = v___x_5740_;
goto v___jp_5681_;
}
}
else
{
size_t v___x_5741_; size_t v___x_5742_; lean_object* v___x_5743_; 
v___x_5741_ = ((size_t)0ULL);
v___x_5742_ = lean_usize_of_nat(v___x_5735_);
v___x_5743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5729_, v___x_5741_, v___x_5742_, v_pkgEntries_5733_);
lean_dec_ref(v_packages_5729_);
v___y_5682_ = v___x_5734_;
v___y_5683_ = v___y_5732_;
v___y_5684_ = v___y_5731_;
v___y_5685_ = v___x_5743_;
goto v___jp_5681_;
}
}
}
v___jp_5744_:
{
if (lean_obj_tag(v_packagesDir_x3f_5728_) == 0)
{
lean_object* v_packages_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v_config_5749_; lean_object* v_toWorkspaceConfig_5750_; lean_object* v___x_5751_; 
v_packages_5746_ = lean_ctor_get(v_ws_5626_, 4);
v___x_5747_ = lean_unsigned_to_nat(0u);
v___x_5748_ = lean_array_fget_borrowed(v_packages_5746_, v___x_5747_);
v_config_5749_ = lean_ctor_get(v___x_5748_, 6);
v_toWorkspaceConfig_5750_ = lean_ctor_get(v_config_5749_, 0);
lean_inc_ref(v_toWorkspaceConfig_5750_);
v___x_5751_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5750_);
v___y_5731_ = v___y_5745_;
v___y_5732_ = v___x_5751_;
goto v___jp_5730_;
}
else
{
lean_object* v_val_5752_; 
v_val_5752_ = lean_ctor_get(v_packagesDir_x3f_5728_, 0);
lean_inc(v_val_5752_);
lean_dec_ref_known(v_packagesDir_x3f_5728_, 1);
v___y_5731_ = v___y_5745_;
v___y_5732_ = v_val_5752_;
goto v___jp_5730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5766_, lean_object* v_manifest_5767_, lean_object* v_leanOpts_5768_, lean_object* v_reconfigure_5769_, lean_object* v_overrides_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_){
_start:
{
uint8_t v_reconfigure_boxed_5773_; lean_object* v_res_5774_; 
v_reconfigure_boxed_5773_ = lean_unbox(v_reconfigure_5769_);
v_res_5774_ = l_Lake_Workspace_materializeDeps(v_ws_5766_, v_manifest_5767_, v_leanOpts_5768_, v_reconfigure_boxed_5773_, v_overrides_5770_, v_a_5771_);
lean_dec_ref(v_a_5771_);
lean_dec_ref(v_overrides_5770_);
return v_res_5774_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v_leanOpts_5777_, uint8_t v_reconfigure_5778_, lean_object* v_ws_5779_, lean_object* v_i_5780_, lean_object* v_i__lt_5781_, lean_object* v_next_5782_, lean_object* v_lt__next_5783_, lean_object* v___y_5784_){
_start:
{
lean_object* v___x_5786_; 
v___x_5786_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5775_, v___y_5776_, v_leanOpts_5777_, v_reconfigure_5778_, v_ws_5779_, v_i_5780_, v_next_5782_, v___y_5784_);
return v___x_5786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v_leanOpts_5789_, lean_object* v_reconfigure_5790_, lean_object* v_ws_5791_, lean_object* v_i_5792_, lean_object* v_i__lt_5793_, lean_object* v_next_5794_, lean_object* v_lt__next_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_){
_start:
{
uint8_t v_reconfigure_boxed_5798_; lean_object* v_res_5799_; 
v_reconfigure_boxed_5798_ = lean_unbox(v_reconfigure_5790_);
v_res_5799_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5787_, v___y_5788_, v_leanOpts_5789_, v_reconfigure_boxed_5798_, v_ws_5791_, v_i_5792_, v_i__lt_5793_, v_next_5794_, v_lt__next_5795_, v___y_5796_);
lean_dec_ref(v___y_5796_);
lean_dec(v___y_5787_);
return v_res_5799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(lean_object* v_start_5800_, lean_object* v_pkg_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v_leanOpts_5804_, uint8_t v_reconfigure_5805_, lean_object* v_as_5806_, size_t v_i_5807_, size_t v_stop_5808_, lean_object* v_b_5809_, lean_object* v___y_5810_){
_start:
{
lean_object* v___x_5812_; 
v___x_5812_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5801_, v___y_5802_, v___y_5803_, v_leanOpts_5804_, v_reconfigure_5805_, v_as_5806_, v_i_5807_, v_stop_5808_, v_b_5809_, v___y_5810_);
return v___x_5812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_start_5813_, lean_object* v_pkg_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v_leanOpts_5817_, lean_object* v_reconfigure_5818_, lean_object* v_as_5819_, lean_object* v_i_5820_, lean_object* v_stop_5821_, lean_object* v_b_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_){
_start:
{
uint8_t v_reconfigure_boxed_5825_; size_t v_i_boxed_5826_; size_t v_stop_boxed_5827_; lean_object* v_res_5828_; 
v_reconfigure_boxed_5825_ = lean_unbox(v_reconfigure_5818_);
v_i_boxed_5826_ = lean_unbox_usize(v_i_5820_);
lean_dec(v_i_5820_);
v_stop_boxed_5827_ = lean_unbox_usize(v_stop_5821_);
lean_dec(v_stop_5821_);
v_res_5828_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(v_start_5813_, v_pkg_5814_, v___y_5815_, v___y_5816_, v_leanOpts_5817_, v_reconfigure_boxed_5825_, v_as_5819_, v_i_boxed_5826_, v_stop_boxed_5827_, v_b_5822_, v___y_5823_);
lean_dec_ref(v___y_5823_);
lean_dec_ref(v_as_5819_);
lean_dec(v___y_5815_);
lean_dec(v_start_5813_);
return v_res_5828_;
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

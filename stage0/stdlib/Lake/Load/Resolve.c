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
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "cannot auto-restart; you will need to manually restart Lake"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "updating toolchain to '"};
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
lean_inc_ref(v_packages_964_);
v___x_965_ = lean_array_get_size(v_packages_964_);
lean_dec_ref(v_packages_964_);
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
v___x_1451_ = lean_array_get_size(v___y_1447_);
v___x_1452_ = lean_nat_dec_lt(v___x_1445_, v___x_1451_);
if (v___x_1452_ == 0)
{
v___y_1423_ = v___y_1448_;
v_fst_1424_ = v_val_1450_;
v_snd_1425_ = v___y_1449_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1453_; size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
v___x_1453_ = lean_box(0);
v___x_1454_ = ((size_t)0ULL);
v___x_1455_ = lean_usize_of_nat(v___x_1451_);
v___x_1456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1447_, v___x_1454_, v___x_1455_, v___x_1453_, v___y_1448_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_dec_ref_known(v___x_1456_, 1);
v___y_1423_ = v___y_1448_;
v_fst_1424_ = v_val_1450_;
v_snd_1425_ = v___y_1449_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_val_1450_);
lean_dec(v___y_1449_);
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
v___y_1466_ = v___x_1513_;
v___y_1467_ = v___y_1493_;
v___y_1468_ = v_snd_1496_;
v___y_1469_ = v___x_1515_;
goto v___jp_1465_;
}
else
{
lean_dec_ref(v___x_1506_);
lean_dec_ref(v___y_1494_);
v___y_1466_ = v___x_1513_;
v___y_1467_ = v___y_1493_;
v___y_1468_ = v_snd_1496_;
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
lean_object* v___x_1713_; lean_object* v_name_1714_; lean_object* v_scope_1715_; lean_object* v_configFile_1716_; lean_object* v_manifestFile_x3f_1717_; lean_object* v_src_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1741_; 
v___x_1713_ = lean_array_uget(v_as_1695_, v_i_1696_);
v_name_1714_ = lean_ctor_get(v___x_1713_, 0);
v_scope_1715_ = lean_ctor_get(v___x_1713_, 1);
v_configFile_1716_ = lean_ctor_get(v___x_1713_, 2);
v_manifestFile_x3f_1717_ = lean_ctor_get(v___x_1713_, 3);
v_src_1718_ = lean_ctor_get(v___x_1713_, 4);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1720_ = v___x_1713_;
v_isShared_1721_ = v_isSharedCheck_1741_;
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
v_isShared_1721_ = v_isSharedCheck_1741_;
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
lean_object* v_dir_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1736_; 
v_dir_1724_ = lean_ctor_get(v_src_1718_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_src_1718_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1726_ = v_src_1718_;
v_isShared_1727_ = v_isSharedCheck_1736_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_dir_1724_);
lean_dec(v_src_1718_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1736_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_relPkgDir_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v_relPkgDir_1728_ = lean_ctor_get(v_dep_1694_, 1);
lean_inc_ref(v_relPkgDir_1728_);
v___x_1729_ = l_Lake_joinRelative(v_relPkgDir_1728_, v_dir_1724_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1729_);
v___x_1731_ = v___x_1726_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1733_; 
lean_inc(v_name_1714_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v___x_1731_);
v___x_1733_ = v___x_1720_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_name_1714_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_scope_1715_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_configFile_1716_);
lean_ctor_set(v_reuseFailAlloc_1734_, 3, v_manifestFile_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1734_, 4, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*5, v___x_1723_);
v___y_1708_ = v___x_1733_;
v_name_1709_ = v_name_1714_;
goto v___jp_1707_;
}
}
}
}
else
{
lean_object* v___x_1738_; 
lean_inc(v_name_1714_);
if (v_isShared_1721_ == 0)
{
v___x_1738_ = v___x_1720_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_name_1714_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_scope_1715_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_configFile_1716_);
lean_ctor_set(v_reuseFailAlloc_1739_, 3, v_manifestFile_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_src_1718_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*5, v___x_1723_);
v___y_1708_ = v___x_1738_;
v_name_1709_ = v_name_1714_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v___x_1740_; 
lean_del_object(v___x_1720_);
lean_dec_ref(v_src_1718_);
lean_dec(v_manifestFile_x3f_1717_);
lean_dec_ref(v_configFile_1716_);
lean_dec_ref(v_scope_1715_);
lean_dec(v_name_1714_);
v___x_1740_ = lean_box(0);
v_fst_1702_ = v___x_1740_;
v_snd_1703_ = v___y_1699_;
goto v___jp_1701_;
}
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec_ref(v_dep_1694_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v_b_1698_);
lean_ctor_set(v___x_1742_, 1, v___y_1699_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1744_, lean_object* v_as_1745_, lean_object* v_i_1746_, lean_object* v_stop_1747_, lean_object* v_b_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
size_t v_i_boxed_1751_; size_t v_stop_boxed_1752_; lean_object* v_res_1753_; 
v_i_boxed_1751_ = lean_unbox_usize(v_i_1746_);
lean_dec(v_i_1746_);
v_stop_boxed_1752_ = lean_unbox_usize(v_stop_1747_);
lean_dec(v_stop_1747_);
v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1744_, v_as_1745_, v_i_boxed_1751_, v_stop_boxed_1752_, v_b_1748_, v___y_1749_);
lean_dec_ref(v_as_1745_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_manifestEntry_1760_; lean_object* v_pkgDir_1761_; lean_object* v_name_1762_; lean_object* v_manifestFile_x3f_1763_; lean_object* v___y_1765_; lean_object* v_fst_1766_; lean_object* v_snd_1767_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v_val_1827_; lean_object* v___y_1843_; 
v_manifestEntry_1760_ = lean_ctor_get(v_dep_1756_, 4);
v_pkgDir_1761_ = lean_ctor_get(v_dep_1756_, 0);
v_name_1762_ = lean_ctor_get(v_manifestEntry_1760_, 0);
v_manifestFile_x3f_1763_ = lean_ctor_get(v_manifestEntry_1760_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1763_) == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1761_);
v___x_1864_ = l_Lake_joinRelative(v_pkgDir_1761_, v___x_1863_);
v___y_1843_ = v___x_1864_;
goto v___jp_1842_;
}
else
{
lean_object* v_val_1865_; lean_object* v___x_1866_; 
v_val_1865_ = lean_ctor_get(v_manifestFile_x3f_1763_, 0);
lean_inc(v_val_1865_);
lean_inc_ref(v_pkgDir_1761_);
v___x_1866_ = l_Lake_joinRelative(v_pkgDir_1761_, v_val_1865_);
v___y_1843_ = v___x_1866_;
goto v___jp_1842_;
}
v___jp_1764_:
{
if (lean_obj_tag(v_fst_1766_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1797_; 
lean_inc(v_name_1762_);
lean_dec_ref(v_dep_1756_);
v_a_1768_ = lean_ctor_get(v_fst_1766_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_fst_1766_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1770_ = v_fst_1766_;
v_isShared_1771_ = v_isSharedCheck_1797_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v_fst_1766_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1797_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
if (lean_obj_tag(v_a_1768_) == 11)
{
uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
lean_dec_ref_known(v_a_1768_, 2);
v___x_1772_ = 0;
v___x_1773_ = l_Lean_Name_toString(v_name_1762_, v___x_1772_);
v___x_1774_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1775_ = lean_string_append(v___x_1773_, v___x_1774_);
v___x_1776_ = lean_string_append(v___x_1775_, v___y_1765_);
lean_dec_ref(v___y_1765_);
v___x_1777_ = 2;
v___x_1778_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*1, v___x_1777_);
lean_inc_ref(v_a_1758_);
v___x_1779_ = lean_apply_2(v_a_1758_, v___x_1778_, lean_box(0));
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
lean_ctor_set(v___x_1780_, 1, v_snd_1767_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1780_);
v___x_1782_ = v___x_1770_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
else
{
uint8_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_dec_ref(v___y_1765_);
v___x_1784_ = 0;
v___x_1785_ = l_Lean_Name_toString(v_name_1762_, v___x_1784_);
v___x_1786_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1787_ = lean_string_append(v___x_1785_, v___x_1786_);
v___x_1788_ = lean_io_error_to_string(v_a_1768_);
v___x_1789_ = lean_string_append(v___x_1787_, v___x_1788_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = 2;
v___x_1791_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*1, v___x_1790_);
lean_inc_ref(v_a_1758_);
v___x_1792_ = lean_apply_2(v_a_1758_, v___x_1791_, lean_box(0));
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
lean_ctor_set(v___x_1793_, 1, v_snd_1767_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1793_);
v___x_1795_ = v___x_1770_;
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
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1822_; 
lean_dec_ref(v___y_1765_);
v_a_1798_ = lean_ctor_get(v_fst_1766_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_fst_1766_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1800_ = v_fst_1766_;
v_isShared_1801_ = v_isSharedCheck_1822_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v_fst_1766_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1822_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_packages_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_packages_1802_ = lean_ctor_get(v_a_1798_, 3);
lean_inc_ref(v_packages_1802_);
lean_dec(v_a_1798_);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_array_get_size(v_packages_1802_);
v___x_1805_ = lean_box(0);
v___x_1806_ = lean_nat_dec_lt(v___x_1803_, v___x_1804_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
lean_dec_ref(v_packages_1802_);
lean_dec_ref(v_dep_1756_);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v_snd_1767_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1807_);
v___x_1809_ = v___x_1800_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_nat_dec_le(v___x_1804_, v___x_1804_);
if (v___x_1811_ == 0)
{
if (v___x_1806_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
lean_dec_ref(v_packages_1802_);
lean_dec_ref(v_dep_1756_);
v___x_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1805_);
lean_ctor_set(v___x_1812_, 1, v_snd_1767_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1812_);
v___x_1814_ = v___x_1800_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
else
{
size_t v___x_1816_; size_t v___x_1817_; lean_object* v___x_1818_; 
lean_del_object(v___x_1800_);
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = lean_usize_of_nat(v___x_1804_);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1756_, v_packages_1802_, v___x_1816_, v___x_1817_, v___x_1805_, v_snd_1767_);
lean_dec_ref(v_packages_1802_);
return v___x_1818_;
}
}
else
{
size_t v___x_1819_; size_t v___x_1820_; lean_object* v___x_1821_; 
lean_del_object(v___x_1800_);
v___x_1819_ = ((size_t)0ULL);
v___x_1820_ = lean_usize_of_nat(v___x_1804_);
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1756_, v_packages_1802_, v___x_1819_, v___x_1820_, v___x_1805_, v_snd_1767_);
lean_dec_ref(v_packages_1802_);
return v___x_1821_;
}
}
}
}
}
v___jp_1823_:
{
lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = lean_array_get_size(v___y_1826_);
v___x_1829_ = lean_nat_dec_lt(v___y_1825_, v___x_1828_);
if (v___x_1829_ == 0)
{
v___y_1765_ = v___y_1824_;
v_fst_1766_ = v_val_1827_;
v_snd_1767_ = v_a_1757_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1830_; size_t v___x_1831_; size_t v___x_1832_; lean_object* v___x_1833_; 
v___x_1830_ = lean_box(0);
v___x_1831_ = ((size_t)0ULL);
v___x_1832_ = lean_usize_of_nat(v___x_1828_);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1826_, v___x_1831_, v___x_1832_, v___x_1830_, v_a_1758_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_dec_ref_known(v___x_1833_, 1);
v___y_1765_ = v___y_1824_;
v_fst_1766_ = v_val_1827_;
v_snd_1767_ = v_a_1757_;
goto v___jp_1764_;
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v_val_1827_);
lean_dec_ref(v___y_1824_);
lean_dec(v_a_1757_);
lean_dec_ref(v_dep_1756_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
v___jp_1842_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1843_);
v___x_1846_ = l_Lake_Manifest_load(v___y_1843_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set_tag(v___x_1849_, 1);
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v___y_1824_ = v___y_1843_;
v___y_1825_ = v___x_1844_;
v___y_1826_ = v___x_1845_;
v_val_1827_ = v___x_1852_;
goto v___jp_1823_;
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_a_1855_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1846_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1846_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 0);
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
v___y_1824_ = v___y_1843_;
v___y_1825_ = v___x_1844_;
v___y_1826_ = v___x_1845_;
v_val_1827_ = v___x_1860_;
goto v___jp_1823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1867_, v_a_1868_, v_a_1869_);
lean_dec_ref(v_a_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1872_, lean_object* v_as_1873_, size_t v_i_1874_, size_t v_stop_1875_, lean_object* v_b_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1872_, v_as_1873_, v_i_1874_, v_stop_1875_, v_b_1876_, v___y_1877_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1881_, lean_object* v_as_1882_, lean_object* v_i_1883_, lean_object* v_stop_1884_, lean_object* v_b_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
size_t v_i_boxed_1889_; size_t v_stop_boxed_1890_; lean_object* v_res_1891_; 
v_i_boxed_1889_ = lean_unbox_usize(v_i_1883_);
lean_dec(v_i_1883_);
v_stop_boxed_1890_ = lean_unbox_usize(v_stop_1884_);
lean_dec(v_stop_1884_);
v_res_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1881_, v_as_1882_, v_i_boxed_1889_, v_stop_boxed_1890_, v_b_1885_, v___y_1886_, v___y_1887_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_as_1882_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1893_, lean_object* v_pkg_1894_, lean_object* v_dep_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
uint8_t v___y_1900_; lean_object* v___y_1901_; lean_object* v_name_1931_; lean_object* v___x_1932_; 
v_name_1931_ = lean_ctor_get(v_dep_1895_, 0);
v___x_1932_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1896_, v_name_1931_);
if (lean_obj_tag(v___x_1932_) == 1)
{
lean_object* v_val_1933_; lean_object* v_lakeEnv_1934_; lean_object* v_packages_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_config_1938_; lean_object* v_dir_1939_; lean_object* v_toWorkspaceConfig_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec_ref(v_dep_1895_);
lean_dec_ref(v_pkg_1894_);
v_val_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_val_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v_lakeEnv_1934_ = lean_ctor_get(v_ws_1893_, 0);
lean_inc_ref(v_lakeEnv_1934_);
v_packages_1935_ = lean_ctor_get(v_ws_1893_, 4);
lean_inc_ref(v_packages_1935_);
lean_dec_ref(v_ws_1893_);
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_array_fget(v_packages_1935_, v___x_1936_);
lean_dec_ref(v_packages_1935_);
v_config_1938_ = lean_ctor_get(v___x_1937_, 6);
lean_inc_ref(v_config_1938_);
v_dir_1939_ = lean_ctor_get(v___x_1937_, 4);
lean_inc_ref(v_dir_1939_);
lean_dec(v___x_1937_);
v_toWorkspaceConfig_1940_ = lean_ctor_get(v_config_1938_, 0);
lean_inc_ref(v_toWorkspaceConfig_1940_);
lean_dec_ref(v_config_1938_);
v___x_1941_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1940_);
v___x_1942_ = l_Lake_PackageEntry_materialize(v_val_1933_, v_lakeEnv_1934_, v_dir_1939_, v___x_1941_, v_a_1897_);
lean_dec_ref(v_lakeEnv_1934_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1951_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v_a_1943_);
lean_ctor_set(v___x_1947_, 1, v_a_1896_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1947_);
v___x_1949_ = v___x_1945_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_a_1896_);
v_a_1952_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1942_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1942_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_wsIdx_1960_; lean_object* v_relDir_1961_; uint8_t v___y_1963_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
lean_dec(v___x_1932_);
v_wsIdx_1960_ = lean_ctor_get(v_pkg_1894_, 0);
lean_inc(v_wsIdx_1960_);
v_relDir_1961_ = lean_ctor_get(v_pkg_1894_, 5);
lean_inc_ref(v_relDir_1961_);
lean_dec_ref(v_pkg_1894_);
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = lean_nat_dec_eq(v_wsIdx_1960_, v___x_1967_);
lean_dec(v_wsIdx_1960_);
if (v___x_1968_ == 0)
{
uint8_t v___x_1969_; 
v___x_1969_ = 1;
v___y_1963_ = v___x_1969_;
goto v___jp_1962_;
}
else
{
uint8_t v___x_1970_; 
v___x_1970_ = 0;
v___y_1963_ = v___x_1970_;
goto v___jp_1962_;
}
v___jp_1962_:
{
lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1965_ = lean_string_dec_eq(v_relDir_1961_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lake_joinRelative(v_relDir_1961_, v___x_1964_);
v___y_1900_ = v___y_1963_;
v___y_1901_ = v___x_1966_;
goto v___jp_1899_;
}
else
{
v___y_1900_ = v___y_1963_;
v___y_1901_ = v_relDir_1961_;
goto v___jp_1899_;
}
}
}
v___jp_1899_:
{
lean_object* v_lakeEnv_1902_; lean_object* v_packages_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v_config_1906_; lean_object* v_dir_1907_; lean_object* v_toWorkspaceConfig_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_lakeEnv_1902_ = lean_ctor_get(v_ws_1893_, 0);
lean_inc_ref(v_lakeEnv_1902_);
v_packages_1903_ = lean_ctor_get(v_ws_1893_, 4);
lean_inc_ref(v_packages_1903_);
lean_dec_ref(v_ws_1893_);
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = lean_array_fget(v_packages_1903_, v___x_1904_);
lean_dec_ref(v_packages_1903_);
v_config_1906_ = lean_ctor_get(v___x_1905_, 6);
lean_inc_ref(v_config_1906_);
v_dir_1907_ = lean_ctor_get(v___x_1905_, 4);
lean_inc_ref(v_dir_1907_);
lean_dec(v___x_1905_);
v_toWorkspaceConfig_1908_ = lean_ctor_get(v_config_1906_, 0);
lean_inc_ref(v_toWorkspaceConfig_1908_);
lean_dec_ref(v_config_1906_);
v___x_1909_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1908_);
v___x_1910_ = l_Lake_Dependency_materialize(v_dep_1895_, v___y_1900_, v_lakeEnv_1902_, v_dir_1907_, v___x_1909_, v___y_1901_, v_a_1897_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1922_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1922_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1922_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_manifestEntry_1915_; lean_object* v_name_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v_manifestEntry_1915_ = lean_ctor_get(v_a_1911_, 4);
v_name_1916_ = lean_ctor_get(v_manifestEntry_1915_, 0);
lean_inc_ref(v_manifestEntry_1915_);
lean_inc(v_name_1916_);
v___x_1917_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1916_, v_manifestEntry_1915_, v_a_1896_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_a_1911_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1918_);
v___x_1920_ = v___x_1913_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v_a_1896_);
v_a_1923_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1910_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1910_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_1971_, lean_object* v_pkg_1972_, lean_object* v_dep_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1971_, v_pkg_1972_, v_dep_1973_, v_a_1974_, v_a_1975_);
lean_dec_ref(v_a_1975_);
return v_res_1977_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_1978_; 
v___x_1978_ = 4;
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_1979_, lean_object* v_tc_x3f_1980_, uint8_t v_fixed_1981_, lean_object* v_self_1982_){
_start:
{
lean_object* v_clashes_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
v_clashes_1983_ = lean_ctor_get(v_self_1982_, 2);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_self_1982_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; lean_object* v_unused_1992_; 
v_unused_1991_ = lean_ctor_get(v_self_1982_, 1);
lean_dec(v_unused_1991_);
v_unused_1992_ = lean_ctor_get(v_self_1982_, 0);
lean_dec(v_unused_1992_);
v___x_1985_ = v_self_1982_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_clashes_1983_);
lean_dec(v_self_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v_tc_x3f_1980_);
lean_ctor_set(v___x_1985_, 0, v_src_1979_);
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_src_1979_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_tc_x3f_1980_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_clashes_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*3, v_fixed_1981_);
return v___x_1988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_1993_, lean_object* v_tc_x3f_1994_, lean_object* v_fixed_1995_, lean_object* v_self_1996_){
_start:
{
uint8_t v_fixed_boxed_1997_; lean_object* v_res_1998_; 
v_fixed_boxed_1997_ = lean_unbox(v_fixed_1995_);
v_res_1998_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_1993_, v_tc_x3f_1994_, v_fixed_boxed_1997_, v_self_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_1999_, lean_object* v_ver_2000_, uint8_t v_fixed_2001_, lean_object* v_self_2002_){
_start:
{
lean_object* v_src_2003_; lean_object* v_tc_x3f_2004_; lean_object* v_clashes_2005_; uint8_t v_fixed_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2015_; 
v_src_2003_ = lean_ctor_get(v_self_2002_, 0);
v_tc_x3f_2004_ = lean_ctor_get(v_self_2002_, 1);
v_clashes_2005_ = lean_ctor_get(v_self_2002_, 2);
v_fixed_2006_ = lean_ctor_get_uint8(v_self_2002_, sizeof(void*)*3);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_self_2002_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2008_ = v_self_2002_;
v_isShared_2009_ = v_isSharedCheck_2015_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_clashes_2005_);
lean_inc(v_tc_x3f_2004_);
lean_inc(v_src_2003_);
lean_dec(v_self_2002_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2015_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2010_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2010_, 0, v_src_1999_);
lean_ctor_set(v___x_2010_, 1, v_ver_2000_);
lean_ctor_set_uint8(v___x_2010_, sizeof(void*)*2, v_fixed_2001_);
v___x_2011_ = lean_array_push(v_clashes_2005_, v___x_2010_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 2, v___x_2011_);
v___x_2013_ = v___x_2008_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_src_2003_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_tc_x3f_2004_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v___x_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*3, v_fixed_2006_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_2016_, lean_object* v_ver_2017_, lean_object* v_fixed_2018_, lean_object* v_self_2019_){
_start:
{
uint8_t v_fixed_boxed_2020_; lean_object* v_res_2021_; 
v_fixed_boxed_2020_ = lean_unbox(v_fixed_2018_);
v_res_2021_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_2016_, v_ver_2017_, v_fixed_boxed_2020_, v_self_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v___x_2026_, lean_object* v_as_2027_, size_t v_i_2028_, size_t v_stop_2029_, lean_object* v_b_2030_){
_start:
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_usize_dec_eq(v_i_2028_, v_stop_2029_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v_src_2033_; lean_object* v_ver_2034_; uint8_t v_fixed_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2052_; 
v___x_2032_ = lean_array_uget_borrowed(v_as_2027_, v_i_2028_);
v_src_2033_ = lean_ctor_get(v___x_2032_, 0);
v_ver_2034_ = lean_ctor_get(v___x_2032_, 1);
v_fixed_2035_ = lean_ctor_get_uint8(v___x_2032_, sizeof(void*)*2);
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = lean_nat_dec_lt(v___x_2036_, v___x_2026_);
if (v_fixed_2035_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2052_ = v___x_2056_;
goto v___jp_2051_;
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2052_ = v___x_2057_;
goto v___jp_2051_;
}
v___jp_2038_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; size_t v___x_2048_; size_t v___x_2049_; 
v___x_2042_ = lean_string_append(v___y_2040_, v___y_2041_);
lean_dec_ref(v___y_2041_);
v___x_2043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2044_ = lean_string_append(v___x_2042_, v___x_2043_);
lean_inc(v_src_2033_);
v___x_2045_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2033_, v___x_2037_);
v___x_2046_ = lean_string_append(v___x_2044_, v___x_2045_);
lean_dec_ref(v___x_2045_);
v___x_2047_ = lean_string_append(v___x_2046_, v___y_2039_);
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2028_, v___x_2048_);
v_i_2028_ = v___x_2049_;
v_b_2030_ = v___x_2047_;
goto _start;
}
v___jp_2051_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v_toString_2055_; 
v___x_2053_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2054_ = lean_string_append(v_b_2030_, v___x_2053_);
v_toString_2055_ = lean_ctor_get(v_ver_2034_, 0);
lean_inc_ref(v_toString_2055_);
v___y_2039_ = v___y_2052_;
v___y_2040_ = v___x_2054_;
v___y_2041_ = v_toString_2055_;
goto v___jp_2038_;
}
}
else
{
return v_b_2030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v___x_2058_, lean_object* v_as_2059_, lean_object* v_i_2060_, lean_object* v_stop_2061_, lean_object* v_b_2062_){
_start:
{
size_t v_i_boxed_2063_; size_t v_stop_boxed_2064_; lean_object* v_res_2065_; 
v_i_boxed_2063_ = lean_unbox_usize(v_i_2060_);
lean_dec(v_i_2060_);
v_stop_boxed_2064_ = lean_unbox_usize(v_stop_2061_);
lean_dec(v_stop_2061_);
v_res_2065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2058_, v_as_2059_, v_i_boxed_2063_, v_stop_boxed_2064_, v_b_2062_);
lean_dec_ref(v_as_2059_);
lean_dec(v___x_2058_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v___x_2066_, lean_object* v_as_2067_, size_t v_i_2068_, size_t v_stop_2069_, lean_object* v_b_2070_){
_start:
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_usize_dec_eq(v_i_2068_, v_stop_2069_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v_src_2073_; lean_object* v_ver_2074_; uint8_t v_fixed_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2092_; 
v___x_2072_ = lean_array_uget_borrowed(v_as_2067_, v_i_2068_);
v_src_2073_ = lean_ctor_get(v___x_2072_, 0);
v_ver_2074_ = lean_ctor_get(v___x_2072_, 1);
v_fixed_2075_ = lean_ctor_get_uint8(v___x_2072_, sizeof(void*)*2);
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = lean_nat_dec_lt(v___x_2076_, v___x_2066_);
if (v_fixed_2075_ == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2092_ = v___x_2096_;
goto v___jp_2091_;
}
else
{
lean_object* v___x_2097_; 
v___x_2097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2092_ = v___x_2097_;
goto v___jp_2091_;
}
v___jp_2078_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; lean_object* v___x_2090_; 
v___x_2082_ = lean_string_append(v___y_2079_, v___y_2081_);
lean_dec_ref(v___y_2081_);
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2084_ = lean_string_append(v___x_2082_, v___x_2083_);
lean_inc(v_src_2073_);
v___x_2085_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2073_, v___x_2077_);
v___x_2086_ = lean_string_append(v___x_2084_, v___x_2085_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = lean_string_append(v___x_2086_, v___y_2080_);
v___x_2088_ = ((size_t)1ULL);
v___x_2089_ = lean_usize_add(v_i_2068_, v___x_2088_);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2066_, v_as_2067_, v___x_2089_, v_stop_2069_, v___x_2087_);
return v___x_2090_;
}
v___jp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v_toString_2095_; 
v___x_2093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2094_ = lean_string_append(v_b_2070_, v___x_2093_);
v_toString_2095_ = lean_ctor_get(v_ver_2074_, 0);
lean_inc_ref(v_toString_2095_);
v___y_2079_ = v___x_2094_;
v___y_2080_ = v___y_2092_;
v___y_2081_ = v_toString_2095_;
goto v___jp_2078_;
}
}
else
{
return v_b_2070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v___x_2098_, lean_object* v_as_2099_, lean_object* v_i_2100_, lean_object* v_stop_2101_, lean_object* v_b_2102_){
_start:
{
size_t v_i_boxed_2103_; size_t v_stop_boxed_2104_; lean_object* v_res_2105_; 
v_i_boxed_2103_ = lean_unbox_usize(v_i_2100_);
lean_dec(v_i_2100_);
v_stop_boxed_2104_ = lean_unbox_usize(v_stop_2101_);
lean_dec(v_stop_2101_);
v_res_2105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___x_2098_, v_as_2099_, v_i_boxed_2103_, v_stop_boxed_2104_, v_b_2102_);
lean_dec_ref(v_as_2099_);
lean_dec(v___x_2098_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_2106_, lean_object* v_as_2107_, size_t v_i_2108_, size_t v_stop_2109_, lean_object* v_b_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_a_2114_; uint8_t v___x_2118_; 
v___x_2118_ = lean_usize_dec_eq(v_i_2108_, v_stop_2109_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v_relPkgDir_2120_; lean_object* v_manifestEntry_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2119_ = lean_array_uget_borrowed(v_as_2107_, v_i_2108_);
v_relPkgDir_2120_ = lean_ctor_get(v___x_2119_, 1);
v_manifestEntry_2121_ = lean_ctor_get(v___x_2119_, 4);
lean_inc_ref(v_relPkgDir_2120_);
lean_inc_ref(v___x_2106_);
v___x_2122_ = l_Lake_joinRelative(v___x_2106_, v_relPkgDir_2120_);
v___x_2123_ = l_Lake_toolchainFileName;
v___x_2124_ = l_System_FilePath_join(v___x_2122_, v___x_2123_);
v___x_2125_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2124_);
lean_dec_ref(v___x_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
if (lean_obj_tag(v_a_2126_) == 1)
{
lean_object* v_tc_x3f_2127_; 
v_tc_x3f_2127_ = lean_ctor_get(v_b_2110_, 1);
if (lean_obj_tag(v_tc_x3f_2127_) == 1)
{
lean_object* v_val_2128_; lean_object* v_src_2129_; lean_object* v_clashes_2130_; uint8_t v_fixed_2131_; lean_object* v_val_2132_; uint8_t v___x_2133_; uint8_t v___y_2135_; 
v_val_2128_ = lean_ctor_get(v_a_2126_, 0);
v_src_2129_ = lean_ctor_get(v_b_2110_, 0);
v_clashes_2130_ = lean_ctor_get(v_b_2110_, 2);
v_fixed_2131_ = lean_ctor_get_uint8(v_b_2110_, sizeof(void*)*3);
v_val_2132_ = lean_ctor_get(v_tc_x3f_2127_, 0);
v___x_2133_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2119_);
if (v___x_2133_ == 0)
{
uint8_t v___x_2144_; 
v___x_2144_ = l_Lake_ToolchainVer_ble(v_val_2128_, v_val_2132_);
if (v___x_2144_ == 0)
{
lean_inc_ref(v_clashes_2130_);
lean_inc(v_src_2129_);
lean_inc_ref(v_tc_x3f_2127_);
lean_dec_ref(v_b_2110_);
if (v_fixed_2131_ == 0)
{
goto v___jp_2142_;
}
else
{
if (v___x_2144_ == 0)
{
v___y_2135_ = v___x_2144_;
goto v___jp_2134_;
}
else
{
goto v___jp_2142_;
}
}
}
else
{
lean_dec_ref_known(v_a_2126_, 1);
v_a_2114_ = v_b_2110_;
goto v___jp_2113_;
}
}
else
{
if (v_fixed_2131_ == 0)
{
lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2159_; 
lean_inc_ref(v_clashes_2130_);
lean_inc(v_src_2129_);
lean_inc_ref(v_tc_x3f_2127_);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_b_2110_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; lean_object* v_unused_2161_; lean_object* v_unused_2162_; 
v_unused_2160_ = lean_ctor_get(v_b_2110_, 2);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_b_2110_, 1);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_b_2110_, 0);
lean_dec(v_unused_2162_);
v___x_2146_ = v_b_2110_;
v_isShared_2147_ = v_isSharedCheck_2159_;
goto v_resetjp_2145_;
}
else
{
lean_dec(v_b_2110_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2159_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
uint8_t v___x_2148_; 
v___x_2148_ = l_Lake_ToolchainVer_ble(v_val_2132_, v_val_2128_);
if (v___x_2148_ == 0)
{
lean_object* v_name_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
lean_inc(v_val_2128_);
lean_dec_ref_known(v_a_2126_, 1);
v_name_2149_ = lean_ctor_get(v_manifestEntry_2121_, 0);
lean_inc(v_name_2149_);
v___x_2150_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2150_, 0, v_name_2149_);
lean_ctor_set(v___x_2150_, 1, v_val_2128_);
lean_ctor_set_uint8(v___x_2150_, sizeof(void*)*2, v___x_2133_);
v___x_2151_ = lean_array_push(v_clashes_2130_, v___x_2150_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 2, v___x_2151_);
v___x_2153_ = v___x_2146_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_src_2129_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_tc_x3f_2127_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v___x_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*3, v_fixed_2131_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
v_a_2114_ = v___x_2153_;
goto v___jp_2113_;
}
}
else
{
lean_object* v_name_2155_; lean_object* v___x_2157_; 
lean_dec(v_src_2129_);
lean_dec_ref_known(v_tc_x3f_2127_, 1);
v_name_2155_ = lean_ctor_get(v_manifestEntry_2121_, 0);
lean_inc(v_name_2155_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v_a_2126_);
lean_ctor_set(v___x_2146_, 0, v_name_2155_);
v___x_2157_ = v___x_2146_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_name_2155_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_a_2126_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_clashes_2130_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*3, v___x_2133_);
v_a_2114_ = v___x_2157_;
goto v___jp_2113_;
}
}
}
}
else
{
uint8_t v___x_2163_; 
lean_inc_n(v_val_2128_, 2);
lean_dec_ref_known(v_a_2126_, 1);
lean_inc(v_val_2132_);
v___x_2163_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2132_, v_val_2128_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2173_; 
lean_inc_ref(v_clashes_2130_);
lean_inc(v_src_2129_);
lean_inc_ref(v_tc_x3f_2127_);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_b_2110_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; lean_object* v_unused_2175_; lean_object* v_unused_2176_; 
v_unused_2174_ = lean_ctor_get(v_b_2110_, 2);
lean_dec(v_unused_2174_);
v_unused_2175_ = lean_ctor_get(v_b_2110_, 1);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_b_2110_, 0);
lean_dec(v_unused_2176_);
v___x_2165_ = v_b_2110_;
v_isShared_2166_ = v_isSharedCheck_2173_;
goto v_resetjp_2164_;
}
else
{
lean_dec(v_b_2110_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2173_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v_name_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v_name_2167_ = lean_ctor_get(v_manifestEntry_2121_, 0);
lean_inc(v_name_2167_);
v___x_2168_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2168_, 0, v_name_2167_);
lean_ctor_set(v___x_2168_, 1, v_val_2128_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*2, v___x_2133_);
v___x_2169_ = lean_array_push(v_clashes_2130_, v___x_2168_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 2, v___x_2169_);
v___x_2171_ = v___x_2165_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_src_2129_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_tc_x3f_2127_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v___x_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*3, v_fixed_2131_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
v_a_2114_ = v___x_2171_;
goto v___jp_2113_;
}
}
}
else
{
lean_dec(v_val_2128_);
v_a_2114_ = v_b_2110_;
goto v___jp_2113_;
}
}
}
v___jp_2134_:
{
if (v___y_2135_ == 0)
{
lean_object* v_name_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_inc(v_val_2128_);
lean_dec_ref_known(v_a_2126_, 1);
v_name_2136_ = lean_ctor_get(v_manifestEntry_2121_, 0);
lean_inc(v_name_2136_);
v___x_2137_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2137_, 0, v_name_2136_);
lean_ctor_set(v___x_2137_, 1, v_val_2128_);
lean_ctor_set_uint8(v___x_2137_, sizeof(void*)*2, v___x_2133_);
v___x_2138_ = lean_array_push(v_clashes_2130_, v___x_2137_);
v___x_2139_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2139_, 0, v_src_2129_);
lean_ctor_set(v___x_2139_, 1, v_tc_x3f_2127_);
lean_ctor_set(v___x_2139_, 2, v___x_2138_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*3, v_fixed_2131_);
v_a_2114_ = v___x_2139_;
goto v___jp_2113_;
}
else
{
lean_object* v_name_2140_; lean_object* v___x_2141_; 
lean_dec(v_src_2129_);
lean_dec_ref_known(v_tc_x3f_2127_, 1);
v_name_2140_ = lean_ctor_get(v_manifestEntry_2121_, 0);
lean_inc(v_name_2140_);
v___x_2141_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2141_, 0, v_name_2140_);
lean_ctor_set(v___x_2141_, 1, v_a_2126_);
lean_ctor_set(v___x_2141_, 2, v_clashes_2130_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*3, v___x_2133_);
v_a_2114_ = v___x_2141_;
goto v___jp_2113_;
}
}
v___jp_2142_:
{
uint8_t v___x_2143_; 
v___x_2143_ = l_Lake_ToolchainVer_blt(v_val_2132_, v_val_2128_);
v___y_2135_ = v___x_2143_;
goto v___jp_2134_;
}
}
else
{
lean_object* v_clashes_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2186_; 
v_clashes_2177_ = lean_ctor_get(v_b_2110_, 2);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_b_2110_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; lean_object* v_unused_2188_; 
v_unused_2187_ = lean_ctor_get(v_b_2110_, 1);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_b_2110_, 0);
lean_dec(v_unused_2188_);
v___x_2179_ = v_b_2110_;
v_isShared_2180_ = v_isSharedCheck_2186_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_clashes_2177_);
lean_dec(v_b_2110_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2186_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_name_2181_; uint8_t v___x_2182_; lean_object* v___x_2184_; 
v_name_2181_ = lean_ctor_get(v_manifestEntry_2121_, 0);
v___x_2182_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2119_);
lean_inc(v_name_2181_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v_a_2126_);
lean_ctor_set(v___x_2179_, 0, v_name_2181_);
v___x_2184_ = v___x_2179_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_name_2181_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_a_2126_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_clashes_2177_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*3, v___x_2182_);
v_a_2114_ = v___x_2184_;
goto v___jp_2113_;
}
}
}
}
else
{
lean_dec(v_a_2126_);
v_a_2114_ = v_b_2110_;
goto v___jp_2113_;
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2201_; 
lean_dec_ref(v_b_2110_);
lean_dec_ref(v___x_2106_);
v_a_2189_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2191_ = v___x_2125_;
v_isShared_2192_ = v_isSharedCheck_2201_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2125_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2201_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; uint8_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2193_ = lean_io_error_to_string(v_a_2189_);
v___x_2194_ = 3;
v___x_2195_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2195_, 0, v___x_2193_);
lean_ctor_set_uint8(v___x_2195_, sizeof(void*)*1, v___x_2194_);
lean_inc_ref(v___y_2111_);
v___x_2196_ = lean_apply_2(v___y_2111_, v___x_2195_, lean_box(0));
v___x_2197_ = lean_box(0);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2197_);
v___x_2199_ = v___x_2191_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v___x_2202_; 
lean_dec_ref(v___x_2106_);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v_b_2110_);
return v___x_2202_;
}
v___jp_2113_:
{
size_t v___x_2115_; size_t v___x_2116_; 
v___x_2115_ = ((size_t)1ULL);
v___x_2116_ = lean_usize_add(v_i_2108_, v___x_2115_);
v_i_2108_ = v___x_2116_;
v_b_2110_ = v_a_2114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2203_, lean_object* v_as_2204_, lean_object* v_i_2205_, lean_object* v_stop_2206_, lean_object* v_b_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
size_t v_i_boxed_2210_; size_t v_stop_boxed_2211_; lean_object* v_res_2212_; 
v_i_boxed_2210_ = lean_unbox_usize(v_i_2205_);
lean_dec(v_i_2205_);
v_stop_boxed_2211_ = lean_unbox_usize(v_stop_2206_);
lean_dec(v_stop_2206_);
v_res_2212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2203_, v_as_2204_, v_i_boxed_2210_, v_stop_boxed_2211_, v_b_2207_, v___y_2208_);
lean_dec_ref(v___y_2208_);
lean_dec_ref(v_as_2204_);
return v_res_2212_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2223_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2224_ = lean_unsigned_to_nat(4u);
v___x_2225_ = lean_mk_empty_array_with_capacity(v___x_2224_);
v___x_2226_ = lean_array_push(v___x_2225_, v___x_2223_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2228_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2229_ = lean_array_push(v___x_2228_, v___x_2227_);
return v___x_2229_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11(void){
_start:
{
uint32_t v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = 4;
v___x_2235_ = lean_uint32_to_uint8(v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2252_, lean_object* v_rootDeps_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v___y_2257_; lean_object* v___y_2263_; uint8_t v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2271_; uint8_t v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; uint8_t v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v_lakeEnv_2293_; lean_object* v_lakeArgs_x3f_2294_; lean_object* v_packages_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v_baseName_2298_; lean_object* v_dir_2299_; lean_object* v_config_2300_; lean_object* v___x_2301_; lean_object* v_rootToolchainFile_2302_; uint8_t v___y_2304_; uint8_t v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2448_; uint8_t v___y_2449_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_lakeEnv_2293_ = lean_ctor_get(v_ws_2252_, 0);
lean_inc_ref(v_lakeEnv_2293_);
v_lakeArgs_x3f_2294_ = lean_ctor_get(v_ws_2252_, 3);
lean_inc(v_lakeArgs_x3f_2294_);
v_packages_2295_ = lean_ctor_get(v_ws_2252_, 4);
lean_inc_ref(v_packages_2295_);
lean_dec_ref(v_ws_2252_);
v___x_2296_ = lean_unsigned_to_nat(0u);
v___x_2297_ = lean_array_fget(v_packages_2295_, v___x_2296_);
lean_dec_ref(v_packages_2295_);
v_baseName_2298_ = lean_ctor_get(v___x_2297_, 1);
lean_inc(v_baseName_2298_);
v_dir_2299_ = lean_ctor_get(v___x_2297_, 4);
lean_inc_ref_n(v_dir_2299_, 3);
v_config_2300_ = lean_ctor_get(v___x_2297_, 6);
lean_inc_ref(v_config_2300_);
lean_dec(v___x_2297_);
v___x_2301_ = l_Lake_toolchainFileName;
v_rootToolchainFile_2302_ = l_Lake_joinRelative(v_dir_2299_, v___x_2301_);
v___x_2453_ = l_System_FilePath_join(v_dir_2299_, v___x_2301_);
v___x_2454_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2453_);
lean_dec_ref(v___x_2453_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2513_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2513_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2513_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v_src_2460_; lean_object* v_tc_x3f_2461_; lean_object* v_clashes_2462_; uint8_t v_fixed_2463_; lean_object* v___y_2487_; uint8_t v_fixedToolchain_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
v_fixedToolchain_2501_ = lean_ctor_get_uint8(v_config_2300_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_2300_);
v___x_2502_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_2503_ = lean_array_get_size(v_rootDeps_2253_);
v___x_2504_ = lean_nat_dec_lt(v___x_2296_, v___x_2503_);
if (v___x_2504_ == 0)
{
lean_dec_ref(v_dir_2299_);
lean_inc(v_a_2455_);
v_src_2460_ = v_baseName_2298_;
v_tc_x3f_2461_ = v_a_2455_;
v_clashes_2462_ = v___x_2502_;
v_fixed_2463_ = v_fixedToolchain_2501_;
goto v___jp_2459_;
}
else
{
lean_object* v___x_2505_; uint8_t v___x_2506_; 
lean_inc(v_a_2455_);
lean_inc(v_baseName_2298_);
v___x_2505_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2505_, 0, v_baseName_2298_);
lean_ctor_set(v___x_2505_, 1, v_a_2455_);
lean_ctor_set(v___x_2505_, 2, v___x_2502_);
lean_ctor_set_uint8(v___x_2505_, sizeof(void*)*3, v_fixedToolchain_2501_);
v___x_2506_ = lean_nat_dec_le(v___x_2503_, v___x_2503_);
if (v___x_2506_ == 0)
{
if (v___x_2504_ == 0)
{
lean_dec_ref_known(v___x_2505_, 3);
lean_dec_ref(v_dir_2299_);
lean_inc(v_a_2455_);
v_src_2460_ = v_baseName_2298_;
v_tc_x3f_2461_ = v_a_2455_;
v_clashes_2462_ = v___x_2502_;
v_fixed_2463_ = v_fixedToolchain_2501_;
goto v___jp_2459_;
}
else
{
size_t v___x_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
lean_dec(v_baseName_2298_);
v___x_2507_ = ((size_t)0ULL);
v___x_2508_ = lean_usize_of_nat(v___x_2503_);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2299_, v_rootDeps_2253_, v___x_2507_, v___x_2508_, v___x_2505_, v_a_2254_);
v___y_2487_ = v___x_2509_;
goto v___jp_2486_;
}
}
else
{
size_t v___x_2510_; size_t v___x_2511_; lean_object* v___x_2512_; 
lean_dec(v_baseName_2298_);
v___x_2510_ = ((size_t)0ULL);
v___x_2511_ = lean_usize_of_nat(v___x_2503_);
v___x_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2299_, v_rootDeps_2253_, v___x_2510_, v___x_2511_, v___x_2505_, v_a_2254_);
v___y_2487_ = v___x_2512_;
goto v___jp_2486_;
}
}
v___jp_2459_:
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = lean_array_get_size(v_clashes_2462_);
v___x_2465_ = lean_nat_dec_lt(v___x_2296_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_dec_ref(v_clashes_2462_);
lean_dec(v_src_2460_);
if (lean_obj_tag(v_tc_x3f_2461_) == 1)
{
if (lean_obj_tag(v_a_2455_) == 0)
{
lean_object* v_val_2466_; 
lean_del_object(v___x_2457_);
v_val_2466_ = lean_ctor_get(v_tc_x3f_2461_, 0);
lean_inc(v_val_2466_);
lean_dec_ref_known(v_tc_x3f_2461_, 1);
v___y_2448_ = v_val_2466_;
v___y_2449_ = v___x_2465_;
goto v___jp_2447_;
}
else
{
lean_object* v_val_2467_; lean_object* v_val_2468_; uint8_t v___x_2469_; 
v_val_2467_ = lean_ctor_get(v_tc_x3f_2461_, 0);
lean_inc_n(v_val_2467_, 2);
lean_dec_ref_known(v_tc_x3f_2461_, 1);
v_val_2468_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v_a_2455_, 1);
v___x_2469_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2468_, v_val_2467_);
if (v___x_2469_ == 0)
{
lean_del_object(v___x_2457_);
v___y_2448_ = v_val_2467_;
v___y_2449_ = v___x_2469_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_val_2467_);
lean_dec_ref(v_rootToolchainFile_2302_);
lean_dec(v_lakeArgs_x3f_2294_);
lean_dec_ref(v_lakeEnv_2293_);
v___x_2470_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2254_);
v___x_2471_ = lean_apply_2(v_a_2254_, v___x_2470_, lean_box(0));
v___x_2472_ = lean_box(0);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2472_);
v___x_2474_ = v___x_2457_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
lean_dec(v_tc_x3f_2461_);
lean_dec(v_a_2455_);
lean_dec_ref(v_rootToolchainFile_2302_);
lean_dec(v_lakeArgs_x3f_2294_);
lean_dec_ref(v_lakeEnv_2293_);
v___x_2476_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2254_);
v___x_2477_ = lean_apply_2(v_a_2254_, v___x_2476_, lean_box(0));
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2477_);
v___x_2479_ = v___x_2457_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
else
{
lean_del_object(v___x_2457_);
lean_dec(v_a_2455_);
lean_dec_ref(v_rootToolchainFile_2302_);
lean_dec(v_lakeArgs_x3f_2294_);
lean_dec_ref(v_lakeEnv_2293_);
if (lean_obj_tag(v_tc_x3f_2461_) == 1)
{
if (v_fixed_2463_ == 0)
{
lean_object* v_val_2481_; lean_object* v___x_2482_; 
v_val_2481_ = lean_ctor_get(v_tc_x3f_2461_, 0);
lean_inc(v_val_2481_);
lean_dec_ref_known(v_tc_x3f_2461_, 1);
v___x_2482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2285_ = v___x_2465_;
v___y_2286_ = v___x_2464_;
v___y_2287_ = v_clashes_2462_;
v___y_2288_ = v_val_2481_;
v___y_2289_ = v_src_2460_;
v___y_2290_ = v___x_2482_;
goto v___jp_2284_;
}
else
{
lean_object* v_val_2483_; lean_object* v___x_2484_; 
v_val_2483_ = lean_ctor_get(v_tc_x3f_2461_, 0);
lean_inc(v_val_2483_);
lean_dec_ref_known(v_tc_x3f_2461_, 1);
v___x_2484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2285_ = v___x_2465_;
v___y_2286_ = v___x_2464_;
v___y_2287_ = v_clashes_2462_;
v___y_2288_ = v_val_2483_;
v___y_2289_ = v_src_2460_;
v___y_2290_ = v___x_2484_;
goto v___jp_2284_;
}
}
else
{
lean_object* v___x_2485_; 
lean_dec(v_tc_x3f_2461_);
lean_dec(v_src_2460_);
v___x_2485_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_2263_ = v___x_2464_;
v___y_2264_ = v___x_2465_;
v___y_2265_ = v_clashes_2462_;
v___y_2266_ = v___x_2485_;
goto v___jp_2262_;
}
}
}
v___jp_2486_:
{
if (lean_obj_tag(v___y_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v_src_2489_; lean_object* v_tc_x3f_2490_; lean_object* v_clashes_2491_; uint8_t v_fixed_2492_; 
v_a_2488_ = lean_ctor_get(v___y_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___y_2487_, 1);
v_src_2489_ = lean_ctor_get(v_a_2488_, 0);
lean_inc(v_src_2489_);
v_tc_x3f_2490_ = lean_ctor_get(v_a_2488_, 1);
lean_inc(v_tc_x3f_2490_);
v_clashes_2491_ = lean_ctor_get(v_a_2488_, 2);
lean_inc_ref(v_clashes_2491_);
v_fixed_2492_ = lean_ctor_get_uint8(v_a_2488_, sizeof(void*)*3);
lean_dec(v_a_2488_);
v_src_2460_ = v_src_2489_;
v_tc_x3f_2461_ = v_tc_x3f_2490_;
v_clashes_2462_ = v_clashes_2491_;
v_fixed_2463_ = v_fixed_2492_;
goto v___jp_2459_;
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_del_object(v___x_2457_);
lean_dec(v_a_2455_);
lean_dec_ref(v_rootToolchainFile_2302_);
lean_dec(v_lakeArgs_x3f_2294_);
lean_dec_ref(v_lakeEnv_2293_);
v_a_2493_ = lean_ctor_get(v___y_2487_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___y_2487_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___y_2487_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___y_2487_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v_rootToolchainFile_2302_);
lean_dec_ref(v_config_2300_);
lean_dec_ref(v_dir_2299_);
lean_dec(v_baseName_2298_);
lean_dec(v_lakeArgs_x3f_2294_);
lean_dec_ref(v_lakeEnv_2293_);
v_a_2514_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2516_ = v___x_2454_;
v_isShared_2517_ = v_isSharedCheck_2526_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2454_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2526_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2518_ = lean_io_error_to_string(v_a_2514_);
v___x_2519_ = 3;
v___x_2520_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set_uint8(v___x_2520_, sizeof(void*)*1, v___x_2519_);
lean_inc_ref(v_a_2254_);
v___x_2521_ = lean_apply_2(v_a_2254_, v___x_2520_, lean_box(0));
v___x_2522_ = lean_box(0);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2522_);
v___x_2524_ = v___x_2516_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
v___jp_2256_:
{
uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2258_ = 2;
v___x_2259_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2259_, 0, v___y_2257_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*1, v___x_2258_);
lean_inc_ref(v_a_2254_);
v___x_2260_ = lean_apply_2(v_a_2254_, v___x_2259_, lean_box(0));
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
return v___x_2261_;
}
v___jp_2262_:
{
if (v___y_2264_ == 0)
{
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2263_);
v___y_2257_ = v___y_2266_;
goto v___jp_2256_;
}
else
{
size_t v___x_2267_; size_t v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = lean_usize_of_nat(v___y_2263_);
v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2263_, v___y_2265_, v___x_2267_, v___x_2268_, v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2263_);
v___y_2257_ = v___x_2269_;
goto v___jp_2256_;
}
}
v___jp_2270_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
lean_inc_ref(v___y_2276_);
v___x_2278_ = lean_string_append(v___y_2276_, v___y_2277_);
lean_dec_ref(v___y_2277_);
v___x_2279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2280_ = lean_string_append(v___x_2278_, v___x_2279_);
v___x_2281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2275_, v___y_2272_);
v___x_2282_ = lean_string_append(v___x_2280_, v___x_2281_);
lean_dec_ref(v___x_2281_);
v___x_2283_ = lean_string_append(v___x_2282_, v___y_2274_);
v___y_2263_ = v___y_2271_;
v___y_2264_ = v___y_2272_;
v___y_2265_ = v___y_2273_;
v___y_2266_ = v___x_2283_;
goto v___jp_2262_;
}
v___jp_2284_:
{
lean_object* v___x_2291_; lean_object* v_toString_2292_; 
v___x_2291_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_2292_ = lean_ctor_get(v___y_2288_, 0);
lean_inc_ref(v_toString_2292_);
lean_dec_ref(v___y_2288_);
v___y_2271_ = v___y_2286_;
v___y_2272_ = v___y_2285_;
v___y_2273_ = v___y_2287_;
v___y_2274_ = v___y_2290_;
v___y_2275_ = v___y_2289_;
v___y_2276_ = v___x_2291_;
v___y_2277_ = v_toString_2292_;
goto v___jp_2270_;
}
v___jp_2303_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
lean_inc_ref(v___y_2306_);
v___x_2308_ = lean_string_append(v___y_2306_, v___y_2307_);
v___x_2309_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2310_ = lean_string_append(v___x_2308_, v___x_2309_);
v___x_2311_ = 1;
v___x_2312_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*1, v___x_2311_);
lean_inc_ref(v_a_2254_);
v___x_2313_ = lean_apply_2(v_a_2254_, v___x_2312_, lean_box(0));
v___x_2314_ = l_IO_FS_writeFile(v_rootToolchainFile_2302_, v___y_2307_);
lean_dec_ref(v_rootToolchainFile_2302_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_dec_ref_known(v___x_2314_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2294_) == 1)
{
lean_object* v_elan_x3f_2315_; 
v_elan_x3f_2315_ = lean_ctor_get(v_lakeEnv_2293_, 2);
if (lean_obj_tag(v_elan_x3f_2315_) == 1)
{
lean_object* v_val_2316_; lean_object* v_val_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_elan_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_val_2316_ = lean_ctor_get(v_lakeArgs_x3f_2294_, 0);
lean_inc(v_val_2316_);
lean_dec_ref_known(v_lakeArgs_x3f_2294_, 1);
v_val_2317_ = lean_ctor_get(v_elan_x3f_2315_, 0);
v___x_2318_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_2254_);
v___x_2319_ = lean_apply_2(v_a_2254_, v___x_2318_, lean_box(0));
v___x_2320_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_2321_ = lean_ctor_get(v_val_2317_, 1);
lean_inc_ref(v_elan_2321_);
v___x_2322_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_2323_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_2324_ = lean_array_push(v___x_2323_, v___y_2307_);
v___x_2325_ = lean_array_push(v___x_2324_, v___x_2322_);
v___x_2326_ = l_Array_append___redArg(v___x_2325_, v_val_2316_);
lean_dec(v_val_2316_);
v___x_2327_ = lean_box(0);
v___x_2328_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2293_);
v___x_2329_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2329_, 0, v___x_2320_);
lean_ctor_set(v___x_2329_, 1, v_elan_2321_);
lean_ctor_set(v___x_2329_, 2, v___x_2326_);
lean_ctor_set(v___x_2329_, 3, v___x_2327_);
lean_ctor_set(v___x_2329_, 4, v___x_2328_);
lean_ctor_set_uint8(v___x_2329_, sizeof(void*)*5, v___y_2305_);
lean_ctor_set_uint8(v___x_2329_, sizeof(void*)*5 + 1, v___y_2304_);
v___x_2330_ = lean_io_process_spawn(v___x_2329_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2332_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = lean_io_process_child_wait(v___x_2320_, v_a_2331_);
lean_dec(v_a_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; uint32_t v___x_2334_; uint8_t v___x_2335_; lean_object* v___x_2336_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = lean_unbox_uint32(v_a_2333_);
lean_dec(v_a_2333_);
v___x_2335_ = lean_uint32_to_uint8(v___x_2334_);
v___x_2336_ = lean_io_exit(v___x_2335_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2357_; 
v_a_2345_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2347_ = v___x_2336_;
v_isShared_2348_ = v_isSharedCheck_2357_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2336_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2357_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2349_ = lean_io_error_to_string(v_a_2345_);
v___x_2350_ = 3;
v___x_2351_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*1, v___x_2350_);
lean_inc_ref(v_a_2254_);
v___x_2352_ = lean_apply_2(v_a_2254_, v___x_2351_, lean_box(0));
v___x_2353_ = lean_box(0);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2353_);
v___x_2355_ = v___x_2347_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2370_; 
v_a_2358_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2360_ = v___x_2332_;
v_isShared_2361_ = v_isSharedCheck_2370_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2332_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2370_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; uint8_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2362_ = lean_io_error_to_string(v_a_2358_);
v___x_2363_ = 3;
v___x_2364_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*1, v___x_2363_);
lean_inc_ref(v_a_2254_);
v___x_2365_ = lean_apply_2(v_a_2254_, v___x_2364_, lean_box(0));
v___x_2366_ = lean_box(0);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2366_);
v___x_2368_ = v___x_2360_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2383_; 
v_a_2371_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2373_ = v___x_2330_;
v_isShared_2374_ = v_isSharedCheck_2383_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2330_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2383_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2381_; 
v___x_2375_ = lean_io_error_to_string(v_a_2371_);
v___x_2376_ = 3;
v___x_2377_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*1, v___x_2376_);
lean_inc_ref(v_a_2254_);
v___x_2378_ = lean_apply_2(v_a_2254_, v___x_2377_, lean_box(0));
v___x_2379_ = lean_box(0);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2379_);
v___x_2381_ = v___x_2373_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; 
lean_dec_ref_known(v_lakeArgs_x3f_2294_, 1);
lean_dec_ref(v___y_2307_);
lean_dec_ref(v_lakeEnv_2293_);
v___x_2384_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_2254_);
v___x_2385_ = lean_apply_2(v_a_2254_, v___x_2384_, lean_box(0));
v___x_2386_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11);
v___x_2387_ = lean_io_exit(v___x_2386_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2408_; 
v_a_2396_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2398_ = v___x_2387_;
v_isShared_2399_ = v_isSharedCheck_2408_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2387_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2408_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2400_ = lean_io_error_to_string(v_a_2396_);
v___x_2401_ = 3;
v___x_2402_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*1, v___x_2401_);
lean_inc_ref(v_a_2254_);
v___x_2403_ = lean_apply_2(v_a_2254_, v___x_2402_, lean_box(0));
v___x_2404_ = lean_box(0);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2404_);
v___x_2406_ = v___x_2398_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2412_; 
lean_dec_ref(v___y_2307_);
lean_dec(v_lakeArgs_x3f_2294_);
lean_dec_ref(v_lakeEnv_2293_);
v___x_2409_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
lean_inc_ref(v_a_2254_);
v___x_2410_ = lean_apply_2(v_a_2254_, v___x_2409_, lean_box(0));
v___x_2411_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11);
v___x_2412_ = lean_io_exit(v___x_2411_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2433_; 
v_a_2421_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2423_ = v___x_2412_;
v_isShared_2424_ = v_isSharedCheck_2433_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2412_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2433_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2425_ = lean_io_error_to_string(v_a_2421_);
v___x_2426_ = 3;
v___x_2427_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*1, v___x_2426_);
lean_inc_ref(v_a_2254_);
v___x_2428_ = lean_apply_2(v_a_2254_, v___x_2427_, lean_box(0));
v___x_2429_ = lean_box(0);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2429_);
v___x_2431_ = v___x_2423_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2446_; 
lean_dec_ref(v___y_2307_);
lean_dec(v_lakeArgs_x3f_2294_);
lean_dec_ref(v_lakeEnv_2293_);
v_a_2434_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2436_ = v___x_2314_;
v_isShared_2437_ = v_isSharedCheck_2446_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2314_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2446_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2438_ = lean_io_error_to_string(v_a_2434_);
v___x_2439_ = 3;
v___x_2440_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set_uint8(v___x_2440_, sizeof(void*)*1, v___x_2439_);
lean_inc_ref(v_a_2254_);
v___x_2441_ = lean_apply_2(v_a_2254_, v___x_2440_, lean_box(0));
v___x_2442_ = lean_box(0);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2442_);
v___x_2444_ = v___x_2436_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
v___jp_2447_:
{
uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v_toString_2452_; 
v___x_2450_ = 1;
v___x_2451_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_2452_ = lean_ctor_get(v___y_2448_, 0);
lean_inc_ref(v_toString_2452_);
lean_dec_ref(v___y_2448_);
v___y_2304_ = v___y_2449_;
v___y_2305_ = v___x_2450_;
v___y_2306_ = v___x_2451_;
v___y_2307_ = v_toString_2452_;
goto v___jp_2303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2527_, lean_object* v_rootDeps_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2527_, v_rootDeps_2528_, v_a_2529_);
lean_dec_ref(v_a_2529_);
lean_dec_ref(v_rootDeps_2528_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2532_, lean_object* v_dep_2533_, lean_object* v_ws_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2534_, v_pkg_2532_, v_dep_2533_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v_fst_2540_; lean_object* v_snd_2541_; lean_object* v___x_2542_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v_fst_2540_ = lean_ctor_get(v_a_2539_, 0);
lean_inc_n(v_fst_2540_, 2);
v_snd_2541_ = lean_ctor_get(v_a_2539_, 1);
lean_inc(v_snd_2541_);
lean_dec(v_a_2539_);
v___x_2542_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2540_, v_snd_2541_, v_a_2536_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2559_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2559_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2559_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_snd_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2557_; 
v_snd_2547_ = lean_ctor_get(v_a_2543_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_a_2543_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; 
v_unused_2558_ = lean_ctor_get(v_a_2543_, 0);
lean_dec(v_unused_2558_);
v___x_2549_ = v_a_2543_;
v_isShared_2550_ = v_isSharedCheck_2557_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_snd_2547_);
lean_dec(v_a_2543_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2557_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v_fst_2540_);
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_fst_2540_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_snd_2547_);
v___x_2552_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2554_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2552_);
v___x_2554_ = v___x_2545_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v_fst_2540_);
v_a_2560_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2542_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2542_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2568_, lean_object* v_dep_2569_, lean_object* v_ws_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2568_, v_dep_2569_, v_ws_2570_, v_a_2571_, v_a_2572_);
lean_dec_ref(v_a_2572_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2575_, lean_object* v_ws_2576_, lean_object* v_pkg_2577_, lean_object* v_dep_2578_, lean_object* v_a_2579_){
_start:
{
uint8_t v___y_2582_; lean_object* v___y_2583_; lean_object* v_name_2613_; lean_object* v___x_2614_; 
v_name_2613_ = lean_ctor_get(v_dep_2578_, 0);
v___x_2614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2579_, v_name_2613_);
if (lean_obj_tag(v___x_2614_) == 1)
{
lean_object* v_val_2615_; lean_object* v_lakeEnv_2616_; lean_object* v_packages_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v_config_2620_; lean_object* v_dir_2621_; lean_object* v_toWorkspaceConfig_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec_ref(v_dep_2578_);
lean_dec_ref(v_pkg_2577_);
v_val_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_val_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v_lakeEnv_2616_ = lean_ctor_get(v_ws_2576_, 0);
lean_inc_ref(v_lakeEnv_2616_);
v_packages_2617_ = lean_ctor_get(v_ws_2576_, 4);
lean_inc_ref(v_packages_2617_);
lean_dec_ref(v_ws_2576_);
v___x_2618_ = lean_unsigned_to_nat(0u);
v___x_2619_ = lean_array_fget(v_packages_2617_, v___x_2618_);
lean_dec_ref(v_packages_2617_);
v_config_2620_ = lean_ctor_get(v___x_2619_, 6);
lean_inc_ref(v_config_2620_);
v_dir_2621_ = lean_ctor_get(v___x_2619_, 4);
lean_inc_ref(v_dir_2621_);
lean_dec(v___x_2619_);
v_toWorkspaceConfig_2622_ = lean_ctor_get(v_config_2620_, 0);
lean_inc_ref(v_toWorkspaceConfig_2622_);
lean_dec_ref(v_config_2620_);
v___x_2623_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2622_);
v___x_2624_ = l_Lake_PackageEntry_materialize(v_val_2615_, v_lakeEnv_2616_, v_dir_2621_, v___x_2623_, v___y_2575_);
lean_dec_ref(v_lakeEnv_2616_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2633_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2633_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2633_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2629_, 0, v_a_2625_);
lean_ctor_set(v___x_2629_, 1, v_a_2579_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2629_);
v___x_2631_ = v___x_2627_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec(v_a_2579_);
v_a_2634_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2624_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2624_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
lean_object* v_wsIdx_2642_; lean_object* v_relDir_2643_; uint8_t v___y_2645_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
lean_dec(v___x_2614_);
v_wsIdx_2642_ = lean_ctor_get(v_pkg_2577_, 0);
lean_inc(v_wsIdx_2642_);
v_relDir_2643_ = lean_ctor_get(v_pkg_2577_, 5);
lean_inc_ref(v_relDir_2643_);
lean_dec_ref(v_pkg_2577_);
v___x_2649_ = lean_unsigned_to_nat(0u);
v___x_2650_ = lean_nat_dec_eq(v_wsIdx_2642_, v___x_2649_);
lean_dec(v_wsIdx_2642_);
if (v___x_2650_ == 0)
{
uint8_t v___x_2651_; 
v___x_2651_ = 1;
v___y_2645_ = v___x_2651_;
goto v___jp_2644_;
}
else
{
uint8_t v___x_2652_; 
v___x_2652_ = 0;
v___y_2645_ = v___x_2652_;
goto v___jp_2644_;
}
v___jp_2644_:
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2647_ = lean_string_dec_eq(v_relDir_2643_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lake_joinRelative(v_relDir_2643_, v___x_2646_);
v___y_2582_ = v___y_2645_;
v___y_2583_ = v___x_2648_;
goto v___jp_2581_;
}
else
{
v___y_2582_ = v___y_2645_;
v___y_2583_ = v_relDir_2643_;
goto v___jp_2581_;
}
}
}
v___jp_2581_:
{
lean_object* v_lakeEnv_2584_; lean_object* v_packages_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v_config_2588_; lean_object* v_dir_2589_; lean_object* v_toWorkspaceConfig_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_lakeEnv_2584_ = lean_ctor_get(v_ws_2576_, 0);
lean_inc_ref(v_lakeEnv_2584_);
v_packages_2585_ = lean_ctor_get(v_ws_2576_, 4);
lean_inc_ref(v_packages_2585_);
lean_dec_ref(v_ws_2576_);
v___x_2586_ = lean_unsigned_to_nat(0u);
v___x_2587_ = lean_array_fget(v_packages_2585_, v___x_2586_);
lean_dec_ref(v_packages_2585_);
v_config_2588_ = lean_ctor_get(v___x_2587_, 6);
lean_inc_ref(v_config_2588_);
v_dir_2589_ = lean_ctor_get(v___x_2587_, 4);
lean_inc_ref(v_dir_2589_);
lean_dec(v___x_2587_);
v_toWorkspaceConfig_2590_ = lean_ctor_get(v_config_2588_, 0);
lean_inc_ref(v_toWorkspaceConfig_2590_);
lean_dec_ref(v_config_2588_);
v___x_2591_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2590_);
v___x_2592_ = l_Lake_Dependency_materialize(v_dep_2578_, v___y_2582_, v_lakeEnv_2584_, v_dir_2589_, v___x_2591_, v___y_2583_, v___y_2575_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2604_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2604_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2604_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v_manifestEntry_2597_; lean_object* v_name_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v_manifestEntry_2597_ = lean_ctor_get(v_a_2593_, 4);
v_name_2598_ = lean_ctor_get(v_manifestEntry_2597_, 0);
lean_inc_ref(v_manifestEntry_2597_);
lean_inc(v_name_2598_);
v___x_2599_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2598_, v_manifestEntry_2597_, v_a_2579_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v_a_2593_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2600_);
v___x_2602_ = v___x_2595_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec(v_a_2579_);
v_a_2605_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2592_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2592_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2653_, lean_object* v_ws_2654_, lean_object* v_pkg_2655_, lean_object* v_dep_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2653_, v_ws_2654_, v_pkg_2655_, v_dep_2656_, v_a_2657_);
lean_dec_ref(v___y_2653_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2660_, lean_object* v_dep_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_manifestEntry_2664_; lean_object* v_pkgDir_2665_; lean_object* v_name_2666_; lean_object* v_manifestFile_x3f_2667_; lean_object* v___y_2669_; lean_object* v_fst_2670_; lean_object* v_snd_2671_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v_val_2723_; lean_object* v___y_2739_; 
v_manifestEntry_2664_ = lean_ctor_get(v_dep_2661_, 4);
v_pkgDir_2665_ = lean_ctor_get(v_dep_2661_, 0);
v_name_2666_ = lean_ctor_get(v_manifestEntry_2664_, 0);
v_manifestFile_x3f_2667_ = lean_ctor_get(v_manifestEntry_2664_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2667_) == 0)
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2665_);
v___x_2760_ = l_Lake_joinRelative(v_pkgDir_2665_, v___x_2759_);
v___y_2739_ = v___x_2760_;
goto v___jp_2738_;
}
else
{
lean_object* v_val_2761_; lean_object* v___x_2762_; 
v_val_2761_ = lean_ctor_get(v_manifestFile_x3f_2667_, 0);
lean_inc(v_val_2761_);
lean_inc_ref(v_pkgDir_2665_);
v___x_2762_ = l_Lake_joinRelative(v_pkgDir_2665_, v_val_2761_);
v___y_2739_ = v___x_2762_;
goto v___jp_2738_;
}
v___jp_2668_:
{
if (lean_obj_tag(v_fst_2670_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2701_; 
lean_inc(v_name_2666_);
lean_dec_ref(v_dep_2661_);
v_a_2672_ = lean_ctor_get(v_fst_2670_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_fst_2670_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2674_ = v_fst_2670_;
v_isShared_2675_ = v_isSharedCheck_2701_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v_fst_2670_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2701_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
if (lean_obj_tag(v_a_2672_) == 11)
{
uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_dec_ref_known(v_a_2672_, 2);
v___x_2676_ = 0;
v___x_2677_ = l_Lean_Name_toString(v_name_2666_, v___x_2676_);
v___x_2678_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2679_ = lean_string_append(v___x_2677_, v___x_2678_);
v___x_2680_ = lean_string_append(v___x_2679_, v___y_2669_);
lean_dec_ref(v___y_2669_);
v___x_2681_ = 2;
v___x_2682_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set_uint8(v___x_2682_, sizeof(void*)*1, v___x_2681_);
v___x_2683_ = lean_apply_2(v___y_2660_, v___x_2682_, lean_box(0));
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v_snd_2671_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2684_);
v___x_2686_ = v___x_2674_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
else
{
uint8_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
lean_dec_ref(v___y_2669_);
v___x_2688_ = 0;
v___x_2689_ = l_Lean_Name_toString(v_name_2666_, v___x_2688_);
v___x_2690_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2691_ = lean_string_append(v___x_2689_, v___x_2690_);
v___x_2692_ = lean_io_error_to_string(v_a_2672_);
v___x_2693_ = lean_string_append(v___x_2691_, v___x_2692_);
lean_dec_ref(v___x_2692_);
v___x_2694_ = 2;
v___x_2695_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set_uint8(v___x_2695_, sizeof(void*)*1, v___x_2694_);
v___x_2696_ = lean_apply_2(v___y_2660_, v___x_2695_, lean_box(0));
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
lean_ctor_set(v___x_2697_, 1, v_snd_2671_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2697_);
v___x_2699_ = v___x_2674_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v___y_2669_);
lean_dec_ref(v___y_2660_);
v_a_2702_ = lean_ctor_get(v_fst_2670_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_fst_2670_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2704_ = v_fst_2670_;
v_isShared_2705_ = v_isSharedCheck_2718_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v_fst_2670_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2718_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v_packages_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
v_packages_2706_ = lean_ctor_get(v_a_2702_, 3);
lean_inc_ref(v_packages_2706_);
lean_dec(v_a_2702_);
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_array_get_size(v_packages_2706_);
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_nat_dec_lt(v___x_2707_, v___x_2708_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2713_; 
lean_dec_ref(v_packages_2706_);
lean_dec_ref(v_dep_2661_);
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v_snd_2671_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set_tag(v___x_2704_, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2711_);
v___x_2713_ = v___x_2704_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
else
{
size_t v___x_2715_; size_t v___x_2716_; lean_object* v___x_2717_; 
lean_del_object(v___x_2704_);
v___x_2715_ = ((size_t)0ULL);
v___x_2716_ = lean_usize_of_nat(v___x_2708_);
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2661_, v_packages_2706_, v___x_2715_, v___x_2716_, v___x_2709_, v_snd_2671_);
lean_dec_ref(v_packages_2706_);
return v___x_2717_;
}
}
}
}
v___jp_2719_:
{
lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2724_ = lean_array_get_size(v___y_2720_);
v___x_2725_ = lean_nat_dec_lt(v___y_2721_, v___x_2724_);
if (v___x_2725_ == 0)
{
v___y_2669_ = v___y_2722_;
v_fst_2670_ = v_val_2723_;
v_snd_2671_ = v_a_2662_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2726_; size_t v___x_2727_; size_t v___x_2728_; lean_object* v___x_2729_; 
v___x_2726_ = lean_box(0);
v___x_2727_ = ((size_t)0ULL);
v___x_2728_ = lean_usize_of_nat(v___x_2724_);
v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2720_, v___x_2727_, v___x_2728_, v___x_2726_, v___y_2660_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_dec_ref_known(v___x_2729_, 1);
v___y_2669_ = v___y_2722_;
v_fst_2670_ = v_val_2723_;
v_snd_2671_ = v_a_2662_;
goto v___jp_2668_;
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec_ref(v_val_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v_a_2662_);
lean_dec_ref(v_dep_2661_);
lean_dec_ref(v___y_2660_);
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
v___jp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = lean_unsigned_to_nat(0u);
v___x_2741_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2739_);
v___x_2742_ = l_Lake_Manifest_load(v___y_2739_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 1);
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
v___y_2720_ = v___x_2741_;
v___y_2721_ = v___x_2740_;
v___y_2722_ = v___y_2739_;
v_val_2723_ = v___x_2748_;
goto v___jp_2719_;
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
v_a_2751_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2742_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2742_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 0);
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
v___y_2720_ = v___x_2741_;
v___y_2721_ = v___x_2740_;
v___y_2722_ = v___y_2739_;
v_val_2723_ = v___x_2756_;
goto v___jp_2719_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2763_, lean_object* v_dep_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2763_, v_dep_2764_, v_a_2765_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2772_, v___y_2770_, v___y_2768_, v___y_2769_, v___y_2771_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v_fst_2776_; lean_object* v_snd_2777_; lean_object* v___x_2778_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v_fst_2776_ = lean_ctor_get(v_a_2775_, 0);
lean_inc_n(v_fst_2776_, 2);
v_snd_2777_ = lean_ctor_get(v_a_2775_, 1);
lean_inc(v_snd_2777_);
lean_dec(v_a_2775_);
v___x_2778_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2772_, v_fst_2776_, v_snd_2777_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2795_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2795_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2795_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_snd_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2793_; 
v_snd_2783_ = lean_ctor_get(v_a_2779_, 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_a_2779_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v_a_2779_, 0);
lean_dec(v_unused_2794_);
v___x_2785_ = v_a_2779_;
v_isShared_2786_ = v_isSharedCheck_2793_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_snd_2783_);
lean_dec(v_a_2779_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2793_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v_fst_2776_);
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_fst_2776_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_snd_2783_);
v___x_2788_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2790_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2788_);
v___x_2790_ = v___x_2781_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_fst_2776_);
v_a_2796_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2778_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2778_);
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
else
{
lean_dec_ref(v___y_2772_);
return v___x_2774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(lean_object* v_toUpdate_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v_entries_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___y_2819_; 
if (lean_obj_tag(v_toUpdate_2811_) == 0)
{
lean_object* v_depConfigs_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v_depConfigs_2861_ = lean_ctor_get(v___x_2812_, 12);
v___x_2862_ = l_Lean_NameSet_empty;
v___x_2863_ = lean_array_get_size(v_depConfigs_2861_);
v___x_2864_ = lean_nat_dec_lt(v___x_2813_, v___x_2863_);
if (v___x_2864_ == 0)
{
v___y_2819_ = v___x_2862_;
goto v___jp_2818_;
}
else
{
size_t v___x_2865_; size_t v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = ((size_t)0ULL);
v___x_2866_ = lean_usize_of_nat(v___x_2863_);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_2861_, v___x_2865_, v___x_2866_, v___x_2862_);
v___y_2819_ = v___x_2867_;
goto v___jp_2818_;
}
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2868_ = lean_box(0);
v___x_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set(v___x_2869_, 1, v___y_2815_);
v___x_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
return v___x_2870_;
}
v___jp_2818_:
{
size_t v_sz_2820_; size_t v___x_2821_; lean_object* v___x_2822_; 
v_sz_2820_ = lean_array_size(v_entries_2814_);
v___x_2821_ = ((size_t)0ULL);
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_entries_2814_, v_sz_2820_, v___x_2821_, v___y_2819_, v___y_2815_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v_fst_2824_; lean_object* v_snd_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v_fst_2824_ = lean_ctor_get(v_a_2823_, 0);
lean_inc(v_fst_2824_);
v_snd_2825_ = lean_ctor_get(v_a_2823_, 1);
lean_inc(v_snd_2825_);
lean_dec(v_a_2823_);
v___x_2826_ = lean_box(0);
v___x_2827_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_2824_, v___x_2826_, v_toUpdate_2811_, v_snd_2825_, v___y_2816_);
lean_dec(v_fst_2824_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2844_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2844_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2844_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v_snd_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2842_; 
v_snd_2832_ = lean_ctor_get(v_a_2828_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_a_2828_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v_a_2828_, 0);
lean_dec(v_unused_2843_);
v___x_2834_ = v_a_2828_;
v_isShared_2835_ = v_isSharedCheck_2842_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_snd_2832_);
lean_dec(v_a_2828_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2842_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2826_);
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_snd_2832_);
v___x_2837_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2839_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2837_);
v___x_2839_ = v___x_2830_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_a_2845_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2827_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2827_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v_toUpdate_2811_);
v_a_2853_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2822_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2822_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0___boxed(lean_object* v_toUpdate_2871_, lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v_entries_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2871_, v___x_2872_, v___x_2873_, v_entries_2874_, v___y_2875_, v___y_2876_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v_entries_2874_);
lean_dec(v___x_2873_);
lean_dec_ref(v___x_2872_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2879_, lean_object* v_ws_2880_, lean_object* v_toUpdate_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v___y_2885_; lean_object* v___y_2890_; lean_object* v_fst_2891_; lean_object* v_snd_2892_; lean_object* v_packages_2911_; lean_object* v___x_2912_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v_val_2917_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___x_2953_; lean_object* v_baseName_2954_; lean_object* v_dir_2955_; lean_object* v_config_2956_; lean_object* v_relManifestFile_2957_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; uint8_t v_fst_2962_; lean_object* v_snd_2963_; lean_object* v_packagesDir_x3f_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; uint8_t v___x_3007_; lean_object* v_rootName_3008_; lean_object* v_fst_3010_; lean_object* v_snd_3011_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v_val_3078_; lean_object* v___x_3092_; 
v_packages_2911_ = lean_ctor_get(v_ws_2880_, 4);
v___x_2912_ = lean_unsigned_to_nat(0u);
v___x_2953_ = lean_array_fget_borrowed(v_packages_2911_, v___x_2912_);
v_baseName_2954_ = lean_ctor_get(v___x_2953_, 1);
v_dir_2955_ = lean_ctor_get(v___x_2953_, 4);
v_config_2956_ = lean_ctor_get(v___x_2953_, 6);
v_relManifestFile_2957_ = lean_ctor_get(v___x_2953_, 9);
v___x_3007_ = 0;
lean_inc(v_baseName_2954_);
v_rootName_3008_ = l_Lean_Name_toString(v_baseName_2954_, v___x_3007_);
lean_inc_ref(v_relManifestFile_2957_);
lean_inc_ref(v_dir_2955_);
v___x_3075_ = l_Lake_joinRelative(v_dir_2955_, v_relManifestFile_2957_);
v___x_3076_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_3092_ = l_Lake_Manifest_load(v___x_3075_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3092_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3092_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
lean_ctor_set_tag(v___x_3095_, 1);
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
v_val_3078_ = v___x_3098_;
goto v___jp_3077_;
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3101_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3092_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3092_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set_tag(v___x_3103_, 0);
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
v_val_3078_ = v___x_3106_;
goto v___jp_3077_;
}
}
}
v___jp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___y_2885_);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
return v___x_2888_;
}
v___jp_2889_:
{
if (lean_obj_tag(v_fst_2891_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_snd_2892_);
v_a_2893_ = lean_ctor_get(v_fst_2891_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_fst_2891_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2895_ = v_fst_2891_;
v_isShared_2896_ = v_isSharedCheck_2907_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v_fst_2891_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2907_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2897_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2898_ = lean_io_error_to_string(v_a_2893_);
v___x_2899_ = lean_string_append(v___x_2897_, v___x_2898_);
lean_dec_ref(v___x_2898_);
v___x_2900_ = 3;
v___x_2901_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set_uint8(v___x_2901_, sizeof(void*)*1, v___x_2900_);
lean_inc_ref(v___y_2890_);
v___x_2902_ = lean_apply_2(v___y_2890_, v___x_2901_, lean_box(0));
v___x_2903_ = lean_box(0);
if (v_isShared_2896_ == 0)
{
lean_ctor_set_tag(v___x_2895_, 1);
lean_ctor_set(v___x_2895_, 0, v___x_2903_);
v___x_2905_ = v___x_2895_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_dec_ref(v_fst_2891_);
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v_snd_2892_);
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
return v___x_2910_;
}
}
v___jp_2913_:
{
lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = lean_array_get_size(v___y_2916_);
v___x_2919_ = lean_nat_dec_lt(v___x_2912_, v___x_2918_);
if (v___x_2919_ == 0)
{
v___y_2890_ = v___y_2915_;
v_fst_2891_ = v_val_2917_;
v_snd_2892_ = v___y_2914_;
goto v___jp_2889_;
}
else
{
lean_object* v___x_2920_; size_t v___x_2921_; size_t v___x_2922_; lean_object* v___x_2923_; 
v___x_2920_ = lean_box(0);
v___x_2921_ = ((size_t)0ULL);
v___x_2922_ = lean_usize_of_nat(v___x_2918_);
v___x_2923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2916_, v___x_2921_, v___x_2922_, v___x_2920_, v___y_2915_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_dec_ref_known(v___x_2923_, 1);
v___y_2890_ = v___y_2915_;
v_fst_2891_ = v_val_2917_;
v_snd_2892_ = v___y_2914_;
goto v___jp_2889_;
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref(v_val_2917_);
lean_dec(v___y_2914_);
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
v___jp_2932_:
{
if (lean_obj_tag(v___y_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
v_a_2937_ = lean_ctor_get(v___y_2936_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___y_2936_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___y_2936_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___y_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set_tag(v___x_2939_, 1);
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
v___y_2914_ = v___y_2933_;
v___y_2915_ = v___y_2934_;
v___y_2916_ = v___y_2935_;
v_val_2917_ = v___x_2942_;
goto v___jp_2913_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
v_a_2945_ = lean_ctor_get(v___y_2936_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___y_2936_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___y_2936_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___y_2936_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 0);
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
v___y_2914_ = v___y_2933_;
v___y_2915_ = v___y_2934_;
v___y_2916_ = v___y_2935_;
v_val_2917_ = v___x_2950_;
goto v___jp_2913_;
}
}
}
}
v___jp_2958_:
{
lean_object* v_toWorkspaceConfig_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v_toWorkspaceConfig_2964_ = lean_ctor_get(v_config_2956_, 0);
v___x_2965_ = l_System_FilePath_normalize(v___y_2960_);
lean_inc_ref(v_toWorkspaceConfig_2964_);
v___x_2966_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2964_);
lean_inc_ref(v___x_2966_);
v___x_2967_ = l_System_FilePath_normalize(v___x_2966_);
v___x_2968_ = lean_string_dec_eq(v___x_2965_, v___x_2967_);
lean_dec_ref(v___x_2967_);
lean_dec_ref(v___x_2965_);
if (v___x_2968_ == 0)
{
if (v_fst_2962_ == 0)
{
lean_dec_ref(v___x_2966_);
lean_dec_ref(v___y_2961_);
v___y_2885_ = v_snd_2963_;
goto v___jp_2884_;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2969_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2970_ = lean_string_append(v___x_2969_, v___y_2961_);
v___x_2971_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2972_ = lean_string_append(v___x_2970_, v___x_2971_);
lean_inc_ref(v_dir_2955_);
v___x_2973_ = l_Lake_joinRelative(v_dir_2955_, v___x_2966_);
v___x_2974_ = lean_string_append(v___x_2972_, v___x_2973_);
v___x_2975_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2976_ = lean_string_append(v___x_2974_, v___x_2975_);
v___x_2977_ = 1;
v___x_2978_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2978_, 0, v___x_2976_);
lean_ctor_set_uint8(v___x_2978_, sizeof(void*)*1, v___x_2977_);
lean_inc_ref(v___y_2959_);
v___x_2979_ = lean_apply_2(v___y_2959_, v___x_2978_, lean_box(0));
v___x_2980_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2973_);
v___x_2981_ = l_Lake_createParentDirs(v___x_2973_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v___x_2982_; 
lean_dec_ref_known(v___x_2981_, 1);
v___x_2982_ = lean_io_rename(v___y_2961_, v___x_2973_);
lean_dec_ref(v___x_2973_);
lean_dec_ref(v___y_2961_);
v___y_2933_ = v_snd_2963_;
v___y_2934_ = v___y_2959_;
v___y_2935_ = v___x_2980_;
v___y_2936_ = v___x_2982_;
goto v___jp_2932_;
}
else
{
lean_dec_ref(v___x_2973_);
lean_dec_ref(v___y_2961_);
v___y_2933_ = v_snd_2963_;
v___y_2934_ = v___y_2959_;
v___y_2935_ = v___x_2980_;
v___y_2936_ = v___x_2981_;
goto v___jp_2932_;
}
}
}
else
{
lean_dec_ref(v___x_2966_);
lean_dec_ref(v___y_2961_);
v___y_2885_ = v_snd_2963_;
goto v___jp_2884_;
}
}
v___jp_2983_:
{
if (lean_obj_tag(v_packagesDir_x3f_2984_) == 1)
{
lean_object* v_val_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; uint8_t v___x_2991_; 
v_val_2987_ = lean_ctor_get(v_packagesDir_x3f_2984_, 0);
lean_inc_n(v_val_2987_, 2);
lean_dec_ref_known(v_packagesDir_x3f_2984_, 1);
lean_inc_ref(v_dir_2955_);
v___x_2988_ = l_Lake_joinRelative(v_dir_2955_, v_val_2987_);
v___x_2989_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2990_ = l_System_FilePath_pathExists(v___x_2988_);
v___x_2991_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2991_ == 0)
{
v___y_2959_ = v___y_2986_;
v___y_2960_ = v_val_2987_;
v___y_2961_ = v___x_2988_;
v_fst_2962_ = v___x_2990_;
v_snd_2963_ = v___y_2985_;
goto v___jp_2958_;
}
else
{
lean_object* v___x_2992_; size_t v___x_2993_; size_t v___x_2994_; lean_object* v___x_2995_; 
v___x_2992_ = lean_box(0);
v___x_2993_ = ((size_t)0ULL);
v___x_2994_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_2995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_2989_, v___x_2993_, v___x_2994_, v___x_2992_, v___y_2986_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_dec_ref_known(v___x_2995_, 1);
v___y_2959_ = v___y_2986_;
v___y_2960_ = v_val_2987_;
v___y_2961_ = v___x_2988_;
v_fst_2962_ = v___x_2990_;
v_snd_2963_ = v___y_2985_;
goto v___jp_2958_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v___x_2988_);
lean_dec(v_val_2987_);
lean_dec(v___y_2985_);
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2995_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
lean_dec(v_packagesDir_x3f_2984_);
v___x_3004_ = lean_box(0);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
lean_ctor_set(v___x_3005_, 1, v___y_2985_);
v___x_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
return v___x_3006_;
}
}
v___jp_3009_:
{
if (lean_obj_tag(v_fst_3010_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3059_; 
v_a_3012_ = lean_ctor_get(v_fst_3010_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_fst_3010_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3014_ = v_fst_3010_;
v_isShared_3015_ = v_isSharedCheck_3059_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v_fst_3010_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3059_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
if (lean_obj_tag(v_a_3012_) == 11)
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
lean_dec_ref_known(v_a_3012_, 2);
lean_del_object(v___x_3014_);
v___x_3016_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_3017_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2881_, v___x_2953_, v___x_2912_, v___x_3016_, v_snd_3011_, v_a_2879_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3039_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3039_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3039_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v_snd_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3037_; 
v_snd_3022_ = lean_ctor_get(v_a_3018_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_a_3018_);
if (v_isSharedCheck_3037_ == 0)
{
lean_object* v_unused_3038_; 
v_unused_3038_ = lean_ctor_get(v_a_3018_, 0);
lean_dec(v_unused_3038_);
v___x_3024_ = v_a_3018_;
v_isShared_3025_ = v_isSharedCheck_3037_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_snd_3022_);
lean_dec(v_a_3018_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3037_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3026_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8));
v___x_3027_ = lean_string_append(v_rootName_3008_, v___x_3026_);
v___x_3028_ = 1;
v___x_3029_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set_uint8(v___x_3029_, sizeof(void*)*1, v___x_3028_);
lean_inc_ref(v_a_2879_);
v___x_3030_ = lean_apply_2(v_a_2879_, v___x_3029_, lean_box(0));
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3030_);
v___x_3032_ = v___x_3024_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_snd_3022_);
v___x_3032_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3032_);
v___x_3034_ = v___x_3020_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
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
else
{
lean_dec_ref(v_rootName_3008_);
return v___x_3017_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2881_) == 0)
{
lean_object* v___x_3040_; uint8_t v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
lean_dec_ref_known(v_toUpdate_2881_, 5);
lean_dec(v_snd_3011_);
lean_dec_ref(v_rootName_3008_);
v___x_3040_ = lean_io_error_to_string(v_a_3012_);
v___x_3041_ = 3;
v___x_3042_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*1, v___x_3041_);
lean_inc_ref(v_a_2879_);
v___x_3043_ = lean_apply_2(v_a_2879_, v___x_3042_, lean_box(0));
v___x_3044_ = lean_box(0);
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 1);
lean_ctor_set(v___x_3014_, 0, v___x_3044_);
v___x_3046_ = v___x_3014_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v___x_3048_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_3049_ = lean_string_append(v_rootName_3008_, v___x_3048_);
v___x_3050_ = lean_io_error_to_string(v_a_3012_);
v___x_3051_ = lean_string_append(v___x_3049_, v___x_3050_);
lean_dec_ref(v___x_3050_);
v___x_3052_ = 2;
v___x_3053_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3051_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*1, v___x_3052_);
lean_inc_ref(v_a_2879_);
v___x_3054_ = lean_apply_2(v_a_2879_, v___x_3053_, lean_box(0));
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v_snd_3011_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3055_);
v___x_3057_ = v___x_3014_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v_packagesDir_x3f_3061_; lean_object* v_packages_3062_; lean_object* v___x_3063_; 
lean_dec_ref(v_rootName_3008_);
v_a_3060_ = lean_ctor_get(v_fst_3010_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v_fst_3010_, 1);
v_packagesDir_x3f_3061_ = lean_ctor_get(v_a_3060_, 2);
lean_inc(v_packagesDir_x3f_3061_);
v_packages_3062_ = lean_ctor_get(v_a_3060_, 3);
lean_inc_ref(v_packages_3062_);
lean_dec(v_a_3060_);
lean_inc(v_toUpdate_2881_);
v___x_3063_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2881_, v___x_2953_, v___x_2912_, v_packages_3062_, v_snd_3011_, v_a_2879_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v___x_3063_, 1);
if (lean_obj_tag(v_toUpdate_2881_) == 0)
{
lean_object* v_snd_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v_snd_3065_ = lean_ctor_get(v_a_3064_, 1);
lean_inc(v_snd_3065_);
lean_dec(v_a_3064_);
v___x_3066_ = lean_array_get_size(v_packages_3062_);
v___x_3067_ = lean_nat_dec_lt(v___x_2912_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_dec_ref_known(v_toUpdate_2881_, 5);
lean_dec_ref(v_packages_3062_);
v_packagesDir_x3f_2984_ = v_packagesDir_x3f_3061_;
v___y_2985_ = v_snd_3065_;
v___y_2986_ = v_a_2879_;
goto v___jp_2983_;
}
else
{
lean_object* v___x_3068_; size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_3071_; 
v___x_3068_ = lean_box(0);
v___x_3069_ = ((size_t)0ULL);
v___x_3070_ = lean_usize_of_nat(v___x_3066_);
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_2881_, v_packages_3062_, v___x_3069_, v___x_3070_, v___x_3068_, v_snd_3065_);
lean_dec_ref(v_packages_3062_);
lean_dec_ref_known(v_toUpdate_2881_, 5);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v_snd_3073_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v_snd_3073_ = lean_ctor_get(v_a_3072_, 1);
lean_inc(v_snd_3073_);
lean_dec(v_a_3072_);
v_packagesDir_x3f_2984_ = v_packagesDir_x3f_3061_;
v___y_2985_ = v_snd_3073_;
v___y_2986_ = v_a_2879_;
goto v___jp_2983_;
}
else
{
lean_dec(v_packagesDir_x3f_3061_);
return v___x_3071_;
}
}
}
else
{
lean_object* v_snd_3074_; 
lean_dec_ref(v_packages_3062_);
v_snd_3074_ = lean_ctor_get(v_a_3064_, 1);
lean_inc(v_snd_3074_);
lean_dec(v_a_3064_);
v_packagesDir_x3f_2984_ = v_packagesDir_x3f_3061_;
v___y_2985_ = v_snd_3074_;
v___y_2986_ = v_a_2879_;
goto v___jp_2983_;
}
}
else
{
lean_dec_ref(v_packages_3062_);
lean_dec(v_packagesDir_x3f_3061_);
lean_dec(v_toUpdate_2881_);
return v___x_3063_;
}
}
}
v___jp_3077_:
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_3079_ == 0)
{
v_fst_3010_ = v_val_3078_;
v_snd_3011_ = v_a_2882_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3080_; size_t v___x_3081_; size_t v___x_3082_; lean_object* v___x_3083_; 
v___x_3080_ = lean_box(0);
v___x_3081_ = ((size_t)0ULL);
v___x_3082_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_3076_, v___x_3081_, v___x_3082_, v___x_3080_, v_a_2879_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_dec_ref_known(v___x_3083_, 1);
v_fst_3010_ = v_val_3078_;
v_snd_3011_ = v_a_2882_;
goto v___jp_3009_;
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v_val_3078_);
lean_dec_ref(v_rootName_3008_);
lean_dec(v_a_2882_);
lean_dec(v_toUpdate_2881_);
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_3109_, lean_object* v_ws_3110_, lean_object* v_toUpdate_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_3109_, v_ws_3110_, v_toUpdate_3111_, v_a_3112_);
lean_dec_ref(v_ws_3110_);
lean_dec_ref(v_a_3109_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_a_3115_, lean_object* v_ws_3116_, lean_object* v_rootDeps_3117_){
_start:
{
lean_object* v___y_3120_; lean_object* v___y_3126_; lean_object* v___y_3127_; uint8_t v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; uint8_t v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; uint8_t v___y_3152_; lean_object* v___y_3153_; lean_object* v_lakeEnv_3156_; lean_object* v_lakeArgs_x3f_3157_; lean_object* v_packages_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v_baseName_3161_; lean_object* v_dir_3162_; lean_object* v_config_3163_; lean_object* v___x_3164_; lean_object* v_rootToolchainFile_3165_; uint8_t v___y_3167_; uint8_t v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3313_; uint8_t v___y_3314_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_lakeEnv_3156_ = lean_ctor_get(v_ws_3116_, 0);
lean_inc_ref(v_lakeEnv_3156_);
v_lakeArgs_x3f_3157_ = lean_ctor_get(v_ws_3116_, 3);
lean_inc(v_lakeArgs_x3f_3157_);
v_packages_3158_ = lean_ctor_get(v_ws_3116_, 4);
lean_inc_ref(v_packages_3158_);
lean_dec_ref(v_ws_3116_);
v___x_3159_ = lean_unsigned_to_nat(0u);
v___x_3160_ = lean_array_fget(v_packages_3158_, v___x_3159_);
lean_dec_ref(v_packages_3158_);
v_baseName_3161_ = lean_ctor_get(v___x_3160_, 1);
lean_inc(v_baseName_3161_);
v_dir_3162_ = lean_ctor_get(v___x_3160_, 4);
lean_inc_ref_n(v_dir_3162_, 3);
v_config_3163_ = lean_ctor_get(v___x_3160_, 6);
lean_inc_ref(v_config_3163_);
lean_dec(v___x_3160_);
v___x_3164_ = l_Lake_toolchainFileName;
v_rootToolchainFile_3165_ = l_Lake_joinRelative(v_dir_3162_, v___x_3164_);
v___x_3318_ = l_System_FilePath_join(v_dir_3162_, v___x_3164_);
v___x_3319_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3318_);
lean_dec_ref(v___x_3318_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3372_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3372_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3372_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v_src_3325_; lean_object* v_tc_x3f_3326_; lean_object* v_clashes_3327_; uint8_t v_fixed_3328_; uint8_t v_fixedToolchain_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v_fixedToolchain_3351_ = lean_ctor_get_uint8(v_config_3163_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_3163_);
v___x_3352_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_3353_ = lean_array_get_size(v_rootDeps_3117_);
v___x_3354_ = lean_nat_dec_lt(v___x_3159_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_dec_ref(v_dir_3162_);
lean_inc(v_a_3320_);
v_src_3325_ = v_baseName_3161_;
v_tc_x3f_3326_ = v_a_3320_;
v_clashes_3327_ = v___x_3352_;
v_fixed_3328_ = v_fixedToolchain_3351_;
goto v___jp_3324_;
}
else
{
lean_object* v___x_3355_; size_t v___x_3356_; size_t v___x_3357_; lean_object* v___x_3358_; 
lean_inc(v_a_3320_);
v___x_3355_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3355_, 0, v_baseName_3161_);
lean_ctor_set(v___x_3355_, 1, v_a_3320_);
lean_ctor_set(v___x_3355_, 2, v___x_3352_);
lean_ctor_set_uint8(v___x_3355_, sizeof(void*)*3, v_fixedToolchain_3351_);
v___x_3356_ = ((size_t)0ULL);
v___x_3357_ = lean_usize_of_nat(v___x_3353_);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3162_, v_rootDeps_3117_, v___x_3356_, v___x_3357_, v___x_3355_, v_a_3115_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v_src_3360_; lean_object* v_tc_x3f_3361_; lean_object* v_clashes_3362_; uint8_t v_fixed_3363_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___x_3358_, 1);
v_src_3360_ = lean_ctor_get(v_a_3359_, 0);
lean_inc(v_src_3360_);
v_tc_x3f_3361_ = lean_ctor_get(v_a_3359_, 1);
lean_inc(v_tc_x3f_3361_);
v_clashes_3362_ = lean_ctor_get(v_a_3359_, 2);
lean_inc_ref(v_clashes_3362_);
v_fixed_3363_ = lean_ctor_get_uint8(v_a_3359_, sizeof(void*)*3);
lean_dec(v_a_3359_);
v_src_3325_ = v_src_3360_;
v_tc_x3f_3326_ = v_tc_x3f_3361_;
v_clashes_3327_ = v_clashes_3362_;
v_fixed_3328_ = v_fixed_3363_;
goto v___jp_3324_;
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_del_object(v___x_3322_);
lean_dec(v_a_3320_);
lean_dec_ref(v_rootToolchainFile_3165_);
lean_dec(v_lakeArgs_x3f_3157_);
lean_dec_ref(v_lakeEnv_3156_);
v_a_3364_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3358_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3358_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
v___jp_3324_:
{
lean_object* v___x_3329_; uint8_t v___x_3330_; 
v___x_3329_ = lean_array_get_size(v_clashes_3327_);
v___x_3330_ = lean_nat_dec_lt(v___x_3159_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_dec_ref(v_clashes_3327_);
lean_dec(v_src_3325_);
if (lean_obj_tag(v_tc_x3f_3326_) == 1)
{
if (lean_obj_tag(v_a_3320_) == 0)
{
lean_object* v_val_3331_; 
lean_del_object(v___x_3322_);
v_val_3331_ = lean_ctor_get(v_tc_x3f_3326_, 0);
lean_inc(v_val_3331_);
lean_dec_ref_known(v_tc_x3f_3326_, 1);
v___y_3313_ = v_val_3331_;
v___y_3314_ = v___x_3330_;
goto v___jp_3312_;
}
else
{
lean_object* v_val_3332_; lean_object* v_val_3333_; uint8_t v___x_3334_; 
v_val_3332_ = lean_ctor_get(v_tc_x3f_3326_, 0);
lean_inc_n(v_val_3332_, 2);
lean_dec_ref_known(v_tc_x3f_3326_, 1);
v_val_3333_ = lean_ctor_get(v_a_3320_, 0);
lean_inc(v_val_3333_);
lean_dec_ref_known(v_a_3320_, 1);
v___x_3334_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3333_, v_val_3332_);
if (v___x_3334_ == 0)
{
lean_del_object(v___x_3322_);
v___y_3313_ = v_val_3332_;
v___y_3314_ = v___x_3334_;
goto v___jp_3312_;
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
lean_dec(v_val_3332_);
lean_dec_ref(v_rootToolchainFile_3165_);
lean_dec(v_lakeArgs_x3f_3157_);
lean_dec_ref(v_lakeEnv_3156_);
v___x_3335_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_3115_);
v___x_3336_ = lean_apply_2(v_a_3115_, v___x_3335_, lean_box(0));
v___x_3337_ = lean_box(0);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3337_);
v___x_3339_ = v___x_3322_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
lean_dec(v_tc_x3f_3326_);
lean_dec(v_a_3320_);
lean_dec_ref(v_rootToolchainFile_3165_);
lean_dec(v_lakeArgs_x3f_3157_);
lean_dec_ref(v_lakeEnv_3156_);
v___x_3341_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_3115_);
v___x_3342_ = lean_apply_2(v_a_3115_, v___x_3341_, lean_box(0));
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3342_);
v___x_3344_ = v___x_3322_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
else
{
lean_del_object(v___x_3322_);
lean_dec(v_a_3320_);
lean_dec_ref(v_rootToolchainFile_3165_);
lean_dec(v_lakeArgs_x3f_3157_);
lean_dec_ref(v_lakeEnv_3156_);
if (lean_obj_tag(v_tc_x3f_3326_) == 1)
{
if (v_fixed_3328_ == 0)
{
lean_object* v_val_3346_; lean_object* v___x_3347_; 
v_val_3346_ = lean_ctor_get(v_tc_x3f_3326_, 0);
lean_inc(v_val_3346_);
lean_dec_ref_known(v_tc_x3f_3326_, 1);
v___x_3347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3148_ = v_src_3325_;
v___y_3149_ = v___x_3329_;
v___y_3150_ = v_clashes_3327_;
v___y_3151_ = v_val_3346_;
v___y_3152_ = v___x_3330_;
v___y_3153_ = v___x_3347_;
goto v___jp_3147_;
}
else
{
lean_object* v_val_3348_; lean_object* v___x_3349_; 
v_val_3348_ = lean_ctor_get(v_tc_x3f_3326_, 0);
lean_inc(v_val_3348_);
lean_dec_ref_known(v_tc_x3f_3326_, 1);
v___x_3349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3148_ = v_src_3325_;
v___y_3149_ = v___x_3329_;
v___y_3150_ = v_clashes_3327_;
v___y_3151_ = v_val_3348_;
v___y_3152_ = v___x_3330_;
v___y_3153_ = v___x_3349_;
goto v___jp_3147_;
}
}
else
{
lean_object* v___x_3350_; 
lean_dec(v_tc_x3f_3326_);
lean_dec(v_src_3325_);
v___x_3350_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_3126_ = v___x_3329_;
v___y_3127_ = v_clashes_3327_;
v___y_3128_ = v___x_3330_;
v___y_3129_ = v___x_3350_;
goto v___jp_3125_;
}
}
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3385_; 
lean_dec_ref(v_rootToolchainFile_3165_);
lean_dec_ref(v_config_3163_);
lean_dec_ref(v_dir_3162_);
lean_dec(v_baseName_3161_);
lean_dec(v_lakeArgs_x3f_3157_);
lean_dec_ref(v_lakeEnv_3156_);
v_a_3373_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3375_ = v___x_3319_;
v_isShared_3376_ = v_isSharedCheck_3385_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3319_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3385_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; uint8_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3377_ = lean_io_error_to_string(v_a_3373_);
v___x_3378_ = 3;
v___x_3379_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3379_, 0, v___x_3377_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*1, v___x_3378_);
lean_inc_ref(v_a_3115_);
v___x_3380_ = lean_apply_2(v_a_3115_, v___x_3379_, lean_box(0));
v___x_3381_ = lean_box(0);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3381_);
v___x_3383_ = v___x_3375_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
v___jp_3119_:
{
uint8_t v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3121_ = 2;
v___x_3122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3122_, 0, v___y_3120_);
lean_ctor_set_uint8(v___x_3122_, sizeof(void*)*1, v___x_3121_);
lean_inc_ref(v_a_3115_);
v___x_3123_ = lean_apply_2(v_a_3115_, v___x_3122_, lean_box(0));
v___x_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
return v___x_3124_;
}
v___jp_3125_:
{
if (v___y_3128_ == 0)
{
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
v___y_3120_ = v___y_3129_;
goto v___jp_3119_;
}
else
{
size_t v___x_3130_; size_t v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = ((size_t)0ULL);
v___x_3131_ = lean_usize_of_nat(v___y_3126_);
v___x_3132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3126_, v___y_3127_, v___x_3130_, v___x_3131_, v___y_3129_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
v___y_3120_ = v___x_3132_;
goto v___jp_3119_;
}
}
v___jp_3133_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_inc_ref(v___y_3139_);
v___x_3141_ = lean_string_append(v___y_3139_, v___y_3140_);
lean_dec_ref(v___y_3140_);
v___x_3142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3143_ = lean_string_append(v___x_3141_, v___x_3142_);
v___x_3144_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3135_, v___y_3138_);
v___x_3145_ = lean_string_append(v___x_3143_, v___x_3144_);
lean_dec_ref(v___x_3144_);
v___x_3146_ = lean_string_append(v___x_3145_, v___y_3134_);
v___y_3126_ = v___y_3136_;
v___y_3127_ = v___y_3137_;
v___y_3128_ = v___y_3138_;
v___y_3129_ = v___x_3146_;
goto v___jp_3125_;
}
v___jp_3147_:
{
lean_object* v___x_3154_; lean_object* v_toString_3155_; 
v___x_3154_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_3155_ = lean_ctor_get(v___y_3151_, 0);
lean_inc_ref(v_toString_3155_);
lean_dec_ref(v___y_3151_);
v___y_3134_ = v___y_3153_;
v___y_3135_ = v___y_3148_;
v___y_3136_ = v___y_3149_;
v___y_3137_ = v___y_3150_;
v___y_3138_ = v___y_3152_;
v___y_3139_ = v___x_3154_;
v___y_3140_ = v_toString_3155_;
goto v___jp_3133_;
}
v___jp_3166_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_inc_ref(v___y_3169_);
v___x_3171_ = lean_string_append(v___y_3169_, v___y_3170_);
v___x_3172_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_3173_ = lean_string_append(v___x_3171_, v___x_3172_);
v___x_3174_ = 1;
v___x_3175_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set_uint8(v___x_3175_, sizeof(void*)*1, v___x_3174_);
lean_inc_ref(v_a_3115_);
v___x_3176_ = lean_apply_2(v_a_3115_, v___x_3175_, lean_box(0));
v___x_3177_ = l_IO_FS_writeFile(v_rootToolchainFile_3165_, v___y_3170_);
lean_dec_ref(v_rootToolchainFile_3165_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_dec_ref_known(v___x_3177_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_3157_) == 1)
{
lean_object* v_elan_x3f_3178_; 
v_elan_x3f_3178_ = lean_ctor_get(v_lakeEnv_3156_, 2);
if (lean_obj_tag(v_elan_x3f_3178_) == 1)
{
lean_object* v_val_3179_; lean_object* v_val_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v_elan_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_val_3179_ = lean_ctor_get(v_lakeArgs_x3f_3157_, 0);
lean_inc(v_val_3179_);
lean_dec_ref_known(v_lakeArgs_x3f_3157_, 1);
v_val_3180_ = lean_ctor_get(v_elan_x3f_3178_, 0);
v___x_3181_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_3115_);
v___x_3182_ = lean_apply_2(v_a_3115_, v___x_3181_, lean_box(0));
v___x_3183_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_3184_ = lean_ctor_get(v_val_3180_, 1);
lean_inc_ref(v_elan_3184_);
v___x_3185_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_3186_ = lean_unsigned_to_nat(4u);
v___x_3187_ = lean_mk_empty_array_with_capacity(v___x_3186_);
lean_dec_ref(v___x_3187_);
v___x_3188_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_3189_ = lean_array_push(v___x_3188_, v___y_3170_);
v___x_3190_ = lean_array_push(v___x_3189_, v___x_3185_);
v___x_3191_ = l_Array_append___redArg(v___x_3190_, v_val_3179_);
lean_dec(v_val_3179_);
v___x_3192_ = lean_box(0);
v___x_3193_ = l_Lake_Env_noToolchainVars(v_lakeEnv_3156_);
v___x_3194_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3194_, 0, v___x_3183_);
lean_ctor_set(v___x_3194_, 1, v_elan_3184_);
lean_ctor_set(v___x_3194_, 2, v___x_3191_);
lean_ctor_set(v___x_3194_, 3, v___x_3192_);
lean_ctor_set(v___x_3194_, 4, v___x_3193_);
lean_ctor_set_uint8(v___x_3194_, sizeof(void*)*5, v___y_3167_);
lean_ctor_set_uint8(v___x_3194_, sizeof(void*)*5 + 1, v___y_3168_);
v___x_3195_ = lean_io_process_spawn(v___x_3194_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3197_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v___x_3197_ = lean_io_process_child_wait(v___x_3183_, v_a_3196_);
lean_dec(v_a_3196_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; uint32_t v___x_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3197_, 1);
v___x_3199_ = lean_unbox_uint32(v_a_3198_);
lean_dec(v_a_3198_);
v___x_3200_ = lean_uint32_to_uint8(v___x_3199_);
v___x_3201_ = lean_io_exit(v___x_3200_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3222_; 
v_a_3210_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3212_ = v___x_3201_;
v_isShared_3213_ = v_isSharedCheck_3222_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3201_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3222_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3214_ = lean_io_error_to_string(v_a_3210_);
v___x_3215_ = 3;
v___x_3216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3216_, 0, v___x_3214_);
lean_ctor_set_uint8(v___x_3216_, sizeof(void*)*1, v___x_3215_);
lean_inc_ref(v_a_3115_);
v___x_3217_ = lean_apply_2(v_a_3115_, v___x_3216_, lean_box(0));
v___x_3218_ = lean_box(0);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3218_);
v___x_3220_ = v___x_3212_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3235_; 
v_a_3223_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3225_ = v___x_3197_;
v_isShared_3226_ = v_isSharedCheck_3235_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3197_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3235_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; uint8_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3227_ = lean_io_error_to_string(v_a_3223_);
v___x_3228_ = 3;
v___x_3229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3229_, 0, v___x_3227_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*1, v___x_3228_);
lean_inc_ref(v_a_3115_);
v___x_3230_ = lean_apply_2(v_a_3115_, v___x_3229_, lean_box(0));
v___x_3231_ = lean_box(0);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3231_);
v___x_3233_ = v___x_3225_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3248_; 
v_a_3236_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3238_ = v___x_3195_;
v_isShared_3239_ = v_isSharedCheck_3248_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3195_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3248_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; uint8_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3240_ = lean_io_error_to_string(v_a_3236_);
v___x_3241_ = 3;
v___x_3242_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set_uint8(v___x_3242_, sizeof(void*)*1, v___x_3241_);
lean_inc_ref(v_a_3115_);
v___x_3243_ = lean_apply_2(v_a_3115_, v___x_3242_, lean_box(0));
v___x_3244_ = lean_box(0);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3244_);
v___x_3246_ = v___x_3238_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; lean_object* v___x_3252_; 
lean_dec_ref_known(v_lakeArgs_x3f_3157_, 1);
lean_dec_ref(v___y_3170_);
lean_dec_ref(v_lakeEnv_3156_);
v___x_3249_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_3115_);
v___x_3250_ = lean_apply_2(v_a_3115_, v___x_3249_, lean_box(0));
v___x_3251_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11);
v___x_3252_ = lean_io_exit(v___x_3251_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3273_; 
v_a_3261_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3263_ = v___x_3252_;
v_isShared_3264_ = v_isSharedCheck_3273_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3252_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3273_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; uint8_t v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3271_; 
v___x_3265_ = lean_io_error_to_string(v_a_3261_);
v___x_3266_ = 3;
v___x_3267_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set_uint8(v___x_3267_, sizeof(void*)*1, v___x_3266_);
lean_inc_ref(v_a_3115_);
v___x_3268_ = lean_apply_2(v_a_3115_, v___x_3267_, lean_box(0));
v___x_3269_ = lean_box(0);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v___x_3269_);
v___x_3271_ = v___x_3263_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3269_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; 
lean_dec_ref(v___y_3170_);
lean_dec(v_lakeArgs_x3f_3157_);
lean_dec_ref(v_lakeEnv_3156_);
v___x_3274_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
lean_inc_ref(v_a_3115_);
v___x_3275_ = lean_apply_2(v_a_3115_, v___x_3274_, lean_box(0));
v___x_3276_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11);
v___x_3277_ = lean_io_exit(v___x_3276_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3298_; 
v_a_3286_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3288_ = v___x_3277_;
v_isShared_3289_ = v_isSharedCheck_3298_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3277_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3298_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3290_ = lean_io_error_to_string(v_a_3286_);
v___x_3291_ = 3;
v___x_3292_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set_uint8(v___x_3292_, sizeof(void*)*1, v___x_3291_);
lean_inc_ref(v_a_3115_);
v___x_3293_ = lean_apply_2(v_a_3115_, v___x_3292_, lean_box(0));
v___x_3294_ = lean_box(0);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v___x_3294_);
v___x_3296_ = v___x_3288_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3311_; 
lean_dec_ref(v___y_3170_);
lean_dec(v_lakeArgs_x3f_3157_);
lean_dec_ref(v_lakeEnv_3156_);
v_a_3299_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3301_ = v___x_3177_;
v_isShared_3302_ = v_isSharedCheck_3311_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3177_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3311_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
v___x_3303_ = lean_io_error_to_string(v_a_3299_);
v___x_3304_ = 3;
v___x_3305_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set_uint8(v___x_3305_, sizeof(void*)*1, v___x_3304_);
lean_inc_ref(v_a_3115_);
v___x_3306_ = lean_apply_2(v_a_3115_, v___x_3305_, lean_box(0));
v___x_3307_ = lean_box(0);
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 0, v___x_3307_);
v___x_3309_ = v___x_3301_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
v___jp_3312_:
{
uint8_t v___x_3315_; lean_object* v___x_3316_; lean_object* v_toString_3317_; 
v___x_3315_ = 1;
v___x_3316_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_3317_ = lean_ctor_get(v___y_3313_, 0);
lean_inc_ref(v_toString_3317_);
lean_dec_ref(v___y_3313_);
v___y_3167_ = v___x_3315_;
v___y_3168_ = v___y_3314_;
v___y_3169_ = v___x_3316_;
v___y_3170_ = v_toString_3317_;
goto v___jp_3166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_a_3386_, lean_object* v_ws_3387_, lean_object* v_rootDeps_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3386_, v_ws_3387_, v_rootDeps_3388_);
lean_dec_ref(v_rootDeps_3388_);
lean_dec_ref(v_a_3386_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(lean_object* v_msg_3391_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = lean_box(1);
v___x_3393_ = lean_panic_fn_borrowed(v___x_3392_, v_msg_3391_);
return v___x_3393_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3397_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3398_ = lean_unsigned_to_nat(35u);
v___x_3399_ = lean_unsigned_to_nat(182u);
v___x_3400_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3401_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3402_ = l_mkPanicMessageWithDecl(v___x_3401_, v___x_3400_, v___x_3399_, v___x_3398_, v___x_3397_);
return v___x_3402_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3403_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3404_ = lean_unsigned_to_nat(21u);
v___x_3405_ = lean_unsigned_to_nat(183u);
v___x_3406_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3407_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3408_ = l_mkPanicMessageWithDecl(v___x_3407_, v___x_3406_, v___x_3405_, v___x_3404_, v___x_3403_);
return v___x_3408_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3411_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3412_ = lean_unsigned_to_nat(35u);
v___x_3413_ = lean_unsigned_to_nat(276u);
v___x_3414_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3416_ = l_mkPanicMessageWithDecl(v___x_3415_, v___x_3414_, v___x_3413_, v___x_3412_, v___x_3411_);
return v___x_3416_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3417_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3418_ = lean_unsigned_to_nat(21u);
v___x_3419_ = lean_unsigned_to_nat(277u);
v___x_3420_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3421_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3422_ = l_mkPanicMessageWithDecl(v___x_3421_, v___x_3420_, v___x_3419_, v___x_3418_, v___x_3417_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(lean_object* v_k_3423_, lean_object* v_v_3424_, lean_object* v_t_3425_){
_start:
{
if (lean_obj_tag(v_t_3425_) == 0)
{
lean_object* v_size_3426_; lean_object* v_k_3427_; lean_object* v_v_3428_; lean_object* v_l_3429_; lean_object* v_r_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3786_; 
v_size_3426_ = lean_ctor_get(v_t_3425_, 0);
v_k_3427_ = lean_ctor_get(v_t_3425_, 1);
v_v_3428_ = lean_ctor_get(v_t_3425_, 2);
v_l_3429_ = lean_ctor_get(v_t_3425_, 3);
v_r_3430_ = lean_ctor_get(v_t_3425_, 4);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_t_3425_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3432_ = v_t_3425_;
v_isShared_3433_ = v_isSharedCheck_3786_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_r_3430_);
lean_inc(v_l_3429_);
lean_inc(v_v_3428_);
lean_inc(v_k_3427_);
lean_inc(v_size_3426_);
lean_dec(v_t_3425_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3786_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
uint8_t v___x_3434_; 
v___x_3434_ = lean_string_compare(v_k_3423_, v_k_3427_);
switch(v___x_3434_)
{
case 0:
{
lean_object* v___x_3435_; 
lean_dec(v_size_3426_);
v___x_3435_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3423_, v_v_3424_, v_l_3429_);
if (lean_obj_tag(v_r_3430_) == 0)
{
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_size_3436_; lean_object* v_size_3437_; lean_object* v_k_3438_; lean_object* v_v_3439_; lean_object* v_l_3440_; lean_object* v_r_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; uint8_t v___x_3444_; 
v_size_3436_ = lean_ctor_get(v_r_3430_, 0);
v_size_3437_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_size_3437_);
v_k_3438_ = lean_ctor_get(v___x_3435_, 1);
lean_inc(v_k_3438_);
v_v_3439_ = lean_ctor_get(v___x_3435_, 2);
lean_inc(v_v_3439_);
v_l_3440_ = lean_ctor_get(v___x_3435_, 3);
lean_inc(v_l_3440_);
v_r_3441_ = lean_ctor_get(v___x_3435_, 4);
lean_inc(v_r_3441_);
v___x_3442_ = lean_unsigned_to_nat(3u);
v___x_3443_ = lean_nat_mul(v___x_3442_, v_size_3436_);
v___x_3444_ = lean_nat_dec_lt(v___x_3443_, v_size_3437_);
lean_dec(v___x_3443_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3449_; 
lean_dec(v_r_3441_);
lean_dec(v_l_3440_);
lean_dec(v_v_3439_);
lean_dec(v_k_3438_);
v___x_3445_ = lean_unsigned_to_nat(1u);
v___x_3446_ = lean_nat_add(v___x_3445_, v_size_3437_);
lean_dec(v_size_3437_);
v___x_3447_ = lean_nat_add(v___x_3446_, v_size_3436_);
lean_dec(v___x_3446_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 3, v___x_3435_);
lean_ctor_set(v___x_3432_, 0, v___x_3447_);
v___x_3449_ = v___x_3432_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3450_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3450_, 3, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3450_, 4, v_r_3430_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
else
{
lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3522_; 
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3522_ == 0)
{
lean_object* v_unused_3523_; lean_object* v_unused_3524_; lean_object* v_unused_3525_; lean_object* v_unused_3526_; lean_object* v_unused_3527_; 
v_unused_3523_ = lean_ctor_get(v___x_3435_, 4);
lean_dec(v_unused_3523_);
v_unused_3524_ = lean_ctor_get(v___x_3435_, 3);
lean_dec(v_unused_3524_);
v_unused_3525_ = lean_ctor_get(v___x_3435_, 2);
lean_dec(v_unused_3525_);
v_unused_3526_ = lean_ctor_get(v___x_3435_, 1);
lean_dec(v_unused_3526_);
v_unused_3527_ = lean_ctor_get(v___x_3435_, 0);
lean_dec(v_unused_3527_);
v___x_3452_ = v___x_3435_;
v_isShared_3453_ = v_isSharedCheck_3522_;
goto v_resetjp_3451_;
}
else
{
lean_dec(v___x_3435_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3522_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
if (lean_obj_tag(v_l_3440_) == 0)
{
if (lean_obj_tag(v_r_3441_) == 0)
{
lean_object* v_size_3454_; lean_object* v_size_3455_; lean_object* v_k_3456_; lean_object* v_v_3457_; lean_object* v_l_3458_; lean_object* v_r_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v_size_3454_ = lean_ctor_get(v_l_3440_, 0);
v_size_3455_ = lean_ctor_get(v_r_3441_, 0);
v_k_3456_ = lean_ctor_get(v_r_3441_, 1);
v_v_3457_ = lean_ctor_get(v_r_3441_, 2);
v_l_3458_ = lean_ctor_get(v_r_3441_, 3);
v_r_3459_ = lean_ctor_get(v_r_3441_, 4);
v___x_3460_ = lean_unsigned_to_nat(2u);
v___x_3461_ = lean_nat_mul(v___x_3460_, v_size_3454_);
v___x_3462_ = lean_nat_dec_lt(v_size_3455_, v___x_3461_);
lean_dec(v___x_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3492_; 
lean_inc(v_r_3459_);
lean_inc(v_l_3458_);
lean_inc(v_v_3457_);
lean_inc(v_k_3456_);
v_isSharedCheck_3492_ = !lean_is_exclusive(v_r_3441_);
if (v_isSharedCheck_3492_ == 0)
{
lean_object* v_unused_3493_; lean_object* v_unused_3494_; lean_object* v_unused_3495_; lean_object* v_unused_3496_; lean_object* v_unused_3497_; 
v_unused_3493_ = lean_ctor_get(v_r_3441_, 4);
lean_dec(v_unused_3493_);
v_unused_3494_ = lean_ctor_get(v_r_3441_, 3);
lean_dec(v_unused_3494_);
v_unused_3495_ = lean_ctor_get(v_r_3441_, 2);
lean_dec(v_unused_3495_);
v_unused_3496_ = lean_ctor_get(v_r_3441_, 1);
lean_dec(v_unused_3496_);
v_unused_3497_ = lean_ctor_get(v_r_3441_, 0);
lean_dec(v_unused_3497_);
v___x_3464_ = v_r_3441_;
v_isShared_3465_ = v_isSharedCheck_3492_;
goto v_resetjp_3463_;
}
else
{
lean_dec(v_r_3441_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3492_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___x_3480_; lean_object* v___y_3482_; 
v___x_3466_ = lean_unsigned_to_nat(1u);
v___x_3467_ = lean_nat_add(v___x_3466_, v_size_3437_);
lean_dec(v_size_3437_);
v___x_3468_ = lean_nat_add(v___x_3467_, v_size_3436_);
lean_dec(v___x_3467_);
v___x_3480_ = lean_nat_add(v___x_3466_, v_size_3454_);
if (lean_obj_tag(v_l_3458_) == 0)
{
lean_object* v_size_3490_; 
v_size_3490_ = lean_ctor_get(v_l_3458_, 0);
lean_inc(v_size_3490_);
v___y_3482_ = v_size_3490_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_unsigned_to_nat(0u);
v___y_3482_ = v___x_3491_;
goto v___jp_3481_;
}
v___jp_3469_:
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3473_ = lean_nat_add(v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec(v___y_3471_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 4, v_r_3430_);
lean_ctor_set(v___x_3464_, 3, v_r_3459_);
lean_ctor_set(v___x_3464_, 2, v_v_3428_);
lean_ctor_set(v___x_3464_, 1, v_k_3427_);
lean_ctor_set(v___x_3464_, 0, v___x_3473_);
v___x_3475_ = v___x_3464_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_r_3459_);
lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_r_3430_);
v___x_3475_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3477_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 4, v___x_3475_);
lean_ctor_set(v___x_3452_, 3, v___y_3470_);
lean_ctor_set(v___x_3452_, 2, v_v_3457_);
lean_ctor_set(v___x_3452_, 1, v_k_3456_);
lean_ctor_set(v___x_3452_, 0, v___x_3468_);
v___x_3477_ = v___x_3452_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_k_3456_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_v_3457_);
lean_ctor_set(v_reuseFailAlloc_3478_, 3, v___y_3470_);
lean_ctor_set(v_reuseFailAlloc_3478_, 4, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
v___jp_3481_:
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = lean_nat_add(v___x_3480_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec(v___x_3480_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v_l_3458_);
lean_ctor_set(v___x_3432_, 3, v_l_3440_);
lean_ctor_set(v___x_3432_, 2, v_v_3439_);
lean_ctor_set(v___x_3432_, 1, v_k_3438_);
lean_ctor_set(v___x_3432_, 0, v___x_3483_);
v___x_3485_ = v___x_3432_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_k_3438_);
lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_v_3439_);
lean_ctor_set(v_reuseFailAlloc_3489_, 3, v_l_3440_);
lean_ctor_set(v_reuseFailAlloc_3489_, 4, v_l_3458_);
v___x_3485_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3486_; 
v___x_3486_ = lean_nat_add(v___x_3466_, v_size_3436_);
if (lean_obj_tag(v_r_3459_) == 0)
{
lean_object* v_size_3487_; 
v_size_3487_ = lean_ctor_get(v_r_3459_, 0);
lean_inc(v_size_3487_);
v___y_3470_ = v___x_3485_;
v___y_3471_ = v___x_3486_;
v___y_3472_ = v_size_3487_;
goto v___jp_3469_;
}
else
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_unsigned_to_nat(0u);
v___y_3470_ = v___x_3485_;
v___y_3471_ = v___x_3486_;
v___y_3472_ = v___x_3488_;
goto v___jp_3469_;
}
}
}
}
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3504_; 
lean_del_object(v___x_3432_);
v___x_3498_ = lean_unsigned_to_nat(1u);
v___x_3499_ = lean_nat_add(v___x_3498_, v_size_3437_);
lean_dec(v_size_3437_);
v___x_3500_ = lean_nat_add(v___x_3499_, v_size_3436_);
lean_dec(v___x_3499_);
v___x_3501_ = lean_nat_add(v___x_3498_, v_size_3436_);
v___x_3502_ = lean_nat_add(v___x_3501_, v_size_3455_);
lean_dec(v___x_3501_);
lean_inc_ref(v_r_3430_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 4, v_r_3430_);
lean_ctor_set(v___x_3452_, 3, v_r_3441_);
lean_ctor_set(v___x_3452_, 2, v_v_3428_);
lean_ctor_set(v___x_3452_, 1, v_k_3427_);
lean_ctor_set(v___x_3452_, 0, v___x_3502_);
v___x_3504_ = v___x_3452_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3517_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3517_, 3, v_r_3441_);
lean_ctor_set(v_reuseFailAlloc_3517_, 4, v_r_3430_);
v___x_3504_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
v_isSharedCheck_3511_ = !lean_is_exclusive(v_r_3430_);
if (v_isSharedCheck_3511_ == 0)
{
lean_object* v_unused_3512_; lean_object* v_unused_3513_; lean_object* v_unused_3514_; lean_object* v_unused_3515_; lean_object* v_unused_3516_; 
v_unused_3512_ = lean_ctor_get(v_r_3430_, 4);
lean_dec(v_unused_3512_);
v_unused_3513_ = lean_ctor_get(v_r_3430_, 3);
lean_dec(v_unused_3513_);
v_unused_3514_ = lean_ctor_get(v_r_3430_, 2);
lean_dec(v_unused_3514_);
v_unused_3515_ = lean_ctor_get(v_r_3430_, 1);
lean_dec(v_unused_3515_);
v_unused_3516_ = lean_ctor_get(v_r_3430_, 0);
lean_dec(v_unused_3516_);
v___x_3506_ = v_r_3430_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_dec(v_r_3430_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 4, v___x_3504_);
lean_ctor_set(v___x_3506_, 3, v_l_3440_);
lean_ctor_set(v___x_3506_, 2, v_v_3439_);
lean_ctor_set(v___x_3506_, 1, v_k_3438_);
lean_ctor_set(v___x_3506_, 0, v___x_3500_);
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_k_3438_);
lean_ctor_set(v_reuseFailAlloc_3510_, 2, v_v_3439_);
lean_ctor_set(v_reuseFailAlloc_3510_, 3, v_l_3440_);
lean_ctor_set(v_reuseFailAlloc_3510_, 4, v___x_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
else
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_dec_ref_known(v_l_3440_, 5);
lean_del_object(v___x_3452_);
lean_dec(v_v_3439_);
lean_dec(v_k_3438_);
lean_dec(v_size_3437_);
lean_dec_ref_known(v_r_3430_, 5);
lean_del_object(v___x_3432_);
lean_dec(v_v_3428_);
lean_dec(v_k_3427_);
v___x_3518_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3);
v___x_3519_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3518_);
return v___x_3519_;
}
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
lean_del_object(v___x_3452_);
lean_dec(v_r_3441_);
lean_dec(v_v_3439_);
lean_dec(v_k_3438_);
lean_dec(v_size_3437_);
lean_dec_ref_known(v_r_3430_, 5);
lean_del_object(v___x_3432_);
lean_dec(v_v_3428_);
lean_dec(v_k_3427_);
v___x_3520_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4);
v___x_3521_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3520_);
return v___x_3521_;
}
}
}
}
else
{
lean_object* v_size_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3532_; 
v_size_3528_ = lean_ctor_get(v_r_3430_, 0);
v___x_3529_ = lean_unsigned_to_nat(1u);
v___x_3530_ = lean_nat_add(v___x_3529_, v_size_3528_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 3, v___x_3435_);
lean_ctor_set(v___x_3432_, 0, v___x_3530_);
v___x_3532_ = v___x_3432_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3533_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3533_, 3, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3533_, 4, v_r_3430_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
else
{
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_l_3534_; 
v_l_3534_ = lean_ctor_get(v___x_3435_, 3);
lean_inc(v_l_3534_);
if (lean_obj_tag(v_l_3534_) == 0)
{
lean_object* v_r_3535_; 
v_r_3535_ = lean_ctor_get(v___x_3435_, 4);
lean_inc(v_r_3535_);
if (lean_obj_tag(v_r_3535_) == 0)
{
lean_object* v_size_3536_; lean_object* v_k_3537_; lean_object* v_v_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3552_; 
v_size_3536_ = lean_ctor_get(v___x_3435_, 0);
v_k_3537_ = lean_ctor_get(v___x_3435_, 1);
v_v_3538_ = lean_ctor_get(v___x_3435_, 2);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3552_ == 0)
{
lean_object* v_unused_3553_; lean_object* v_unused_3554_; 
v_unused_3553_ = lean_ctor_get(v___x_3435_, 4);
lean_dec(v_unused_3553_);
v_unused_3554_ = lean_ctor_get(v___x_3435_, 3);
lean_dec(v_unused_3554_);
v___x_3540_ = v___x_3435_;
v_isShared_3541_ = v_isSharedCheck_3552_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_v_3538_);
lean_inc(v_k_3537_);
lean_inc(v_size_3536_);
lean_dec(v___x_3435_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3552_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v_size_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3547_; 
v_size_3542_ = lean_ctor_get(v_r_3535_, 0);
v___x_3543_ = lean_unsigned_to_nat(1u);
v___x_3544_ = lean_nat_add(v___x_3543_, v_size_3536_);
lean_dec(v_size_3536_);
v___x_3545_ = lean_nat_add(v___x_3543_, v_size_3542_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 4, v_r_3430_);
lean_ctor_set(v___x_3540_, 3, v_r_3535_);
lean_ctor_set(v___x_3540_, 2, v_v_3428_);
lean_ctor_set(v___x_3540_, 1, v_k_3427_);
lean_ctor_set(v___x_3540_, 0, v___x_3545_);
v___x_3547_ = v___x_3540_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3551_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3551_, 3, v_r_3535_);
lean_ctor_set(v_reuseFailAlloc_3551_, 4, v_r_3430_);
v___x_3547_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3549_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v___x_3547_);
lean_ctor_set(v___x_3432_, 3, v_l_3534_);
lean_ctor_set(v___x_3432_, 2, v_v_3538_);
lean_ctor_set(v___x_3432_, 1, v_k_3537_);
lean_ctor_set(v___x_3432_, 0, v___x_3544_);
v___x_3549_ = v___x_3432_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3550_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3550_, 3, v_l_3534_);
lean_ctor_set(v_reuseFailAlloc_3550_, 4, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
else
{
lean_object* v_k_3555_; lean_object* v_v_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3568_; 
v_k_3555_ = lean_ctor_get(v___x_3435_, 1);
v_v_3556_ = lean_ctor_get(v___x_3435_, 2);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; lean_object* v_unused_3570_; lean_object* v_unused_3571_; 
v_unused_3569_ = lean_ctor_get(v___x_3435_, 4);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v___x_3435_, 3);
lean_dec(v_unused_3570_);
v_unused_3571_ = lean_ctor_get(v___x_3435_, 0);
lean_dec(v_unused_3571_);
v___x_3558_ = v___x_3435_;
v_isShared_3559_ = v_isSharedCheck_3568_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_v_3556_);
lean_inc(v_k_3555_);
lean_dec(v___x_3435_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3568_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3560_ = lean_unsigned_to_nat(3u);
v___x_3561_ = lean_unsigned_to_nat(1u);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 3, v_r_3535_);
lean_ctor_set(v___x_3558_, 2, v_v_3428_);
lean_ctor_set(v___x_3558_, 1, v_k_3427_);
lean_ctor_set(v___x_3558_, 0, v___x_3561_);
v___x_3563_ = v___x_3558_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3567_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3567_, 3, v_r_3535_);
lean_ctor_set(v_reuseFailAlloc_3567_, 4, v_r_3535_);
v___x_3563_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3565_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v___x_3563_);
lean_ctor_set(v___x_3432_, 3, v_l_3534_);
lean_ctor_set(v___x_3432_, 2, v_v_3556_);
lean_ctor_set(v___x_3432_, 1, v_k_3555_);
lean_ctor_set(v___x_3432_, 0, v___x_3560_);
v___x_3565_ = v___x_3432_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_k_3555_);
lean_ctor_set(v_reuseFailAlloc_3566_, 2, v_v_3556_);
lean_ctor_set(v_reuseFailAlloc_3566_, 3, v_l_3534_);
lean_ctor_set(v_reuseFailAlloc_3566_, 4, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
}
else
{
lean_object* v_r_3572_; 
v_r_3572_ = lean_ctor_get(v___x_3435_, 4);
lean_inc(v_r_3572_);
if (lean_obj_tag(v_r_3572_) == 0)
{
lean_object* v_k_3573_; lean_object* v_v_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3598_; 
v_k_3573_ = lean_ctor_get(v___x_3435_, 1);
v_v_3574_ = lean_ctor_get(v___x_3435_, 2);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; lean_object* v_unused_3600_; lean_object* v_unused_3601_; 
v_unused_3599_ = lean_ctor_get(v___x_3435_, 4);
lean_dec(v_unused_3599_);
v_unused_3600_ = lean_ctor_get(v___x_3435_, 3);
lean_dec(v_unused_3600_);
v_unused_3601_ = lean_ctor_get(v___x_3435_, 0);
lean_dec(v_unused_3601_);
v___x_3576_ = v___x_3435_;
v_isShared_3577_ = v_isSharedCheck_3598_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_v_3574_);
lean_inc(v_k_3573_);
lean_dec(v___x_3435_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3598_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v_k_3578_; lean_object* v_v_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3594_; 
v_k_3578_ = lean_ctor_get(v_r_3572_, 1);
v_v_3579_ = lean_ctor_get(v_r_3572_, 2);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_r_3572_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; lean_object* v_unused_3596_; lean_object* v_unused_3597_; 
v_unused_3595_ = lean_ctor_get(v_r_3572_, 4);
lean_dec(v_unused_3595_);
v_unused_3596_ = lean_ctor_get(v_r_3572_, 3);
lean_dec(v_unused_3596_);
v_unused_3597_ = lean_ctor_get(v_r_3572_, 0);
lean_dec(v_unused_3597_);
v___x_3581_ = v_r_3572_;
v_isShared_3582_ = v_isSharedCheck_3594_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_v_3579_);
lean_inc(v_k_3578_);
lean_dec(v_r_3572_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3594_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3583_ = lean_unsigned_to_nat(3u);
v___x_3584_ = lean_unsigned_to_nat(1u);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 4, v_l_3534_);
lean_ctor_set(v___x_3581_, 3, v_l_3534_);
lean_ctor_set(v___x_3581_, 2, v_v_3574_);
lean_ctor_set(v___x_3581_, 1, v_k_3573_);
lean_ctor_set(v___x_3581_, 0, v___x_3584_);
v___x_3586_ = v___x_3581_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_k_3573_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v_v_3574_);
lean_ctor_set(v_reuseFailAlloc_3593_, 3, v_l_3534_);
lean_ctor_set(v_reuseFailAlloc_3593_, 4, v_l_3534_);
v___x_3586_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3588_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 4, v_l_3534_);
lean_ctor_set(v___x_3576_, 2, v_v_3428_);
lean_ctor_set(v___x_3576_, 1, v_k_3427_);
lean_ctor_set(v___x_3576_, 0, v___x_3584_);
v___x_3588_ = v___x_3576_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3592_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3592_, 3, v_l_3534_);
lean_ctor_set(v_reuseFailAlloc_3592_, 4, v_l_3534_);
v___x_3588_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3590_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v___x_3588_);
lean_ctor_set(v___x_3432_, 3, v___x_3586_);
lean_ctor_set(v___x_3432_, 2, v_v_3579_);
lean_ctor_set(v___x_3432_, 1, v_k_3578_);
lean_ctor_set(v___x_3432_, 0, v___x_3583_);
v___x_3590_ = v___x_3432_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3583_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v_k_3578_);
lean_ctor_set(v_reuseFailAlloc_3591_, 2, v_v_3579_);
lean_ctor_set(v_reuseFailAlloc_3591_, 3, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3591_, 4, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
}
else
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = lean_unsigned_to_nat(2u);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v_r_3572_);
lean_ctor_set(v___x_3432_, 3, v___x_3435_);
lean_ctor_set(v___x_3432_, 0, v___x_3602_);
v___x_3604_ = v___x_3432_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3605_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3605_, 3, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3605_, 4, v_r_3572_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
else
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3606_ = lean_unsigned_to_nat(1u);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v___x_3435_);
lean_ctor_set(v___x_3432_, 3, v___x_3435_);
lean_ctor_set(v___x_3432_, 0, v___x_3606_);
v___x_3608_ = v___x_3432_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3609_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3609_, 3, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3609_, 4, v___x_3435_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
case 1:
{
lean_object* v___x_3611_; 
lean_dec(v_v_3428_);
lean_dec(v_k_3427_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 2, v_v_3424_);
lean_ctor_set(v___x_3432_, 1, v_k_3423_);
v___x_3611_ = v___x_3432_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_size_3426_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_k_3423_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_v_3424_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_l_3429_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v_r_3430_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
default: 
{
lean_object* v___x_3613_; 
lean_dec(v_size_3426_);
v___x_3613_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3423_, v_v_3424_, v_r_3430_);
if (lean_obj_tag(v_l_3429_) == 0)
{
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_size_3614_; lean_object* v_size_3615_; lean_object* v_k_3616_; lean_object* v_v_3617_; lean_object* v_l_3618_; lean_object* v_r_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v_size_3614_ = lean_ctor_get(v_l_3429_, 0);
v_size_3615_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_size_3615_);
v_k_3616_ = lean_ctor_get(v___x_3613_, 1);
lean_inc(v_k_3616_);
v_v_3617_ = lean_ctor_get(v___x_3613_, 2);
lean_inc(v_v_3617_);
v_l_3618_ = lean_ctor_get(v___x_3613_, 3);
lean_inc(v_l_3618_);
v_r_3619_ = lean_ctor_get(v___x_3613_, 4);
lean_inc(v_r_3619_);
v___x_3620_ = lean_unsigned_to_nat(3u);
v___x_3621_ = lean_nat_mul(v___x_3620_, v_size_3614_);
v___x_3622_ = lean_nat_dec_lt(v___x_3621_, v_size_3615_);
lean_dec(v___x_3621_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3627_; 
lean_dec(v_r_3619_);
lean_dec(v_l_3618_);
lean_dec(v_v_3617_);
lean_dec(v_k_3616_);
v___x_3623_ = lean_unsigned_to_nat(1u);
v___x_3624_ = lean_nat_add(v___x_3623_, v_size_3614_);
v___x_3625_ = lean_nat_add(v___x_3624_, v_size_3615_);
lean_dec(v_size_3615_);
lean_dec(v___x_3624_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v___x_3613_);
lean_ctor_set(v___x_3432_, 0, v___x_3625_);
v___x_3627_ = v___x_3432_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3628_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3628_, 3, v_l_3429_);
lean_ctor_set(v_reuseFailAlloc_3628_, 4, v___x_3613_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
else
{
lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3698_; 
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3698_ == 0)
{
lean_object* v_unused_3699_; lean_object* v_unused_3700_; lean_object* v_unused_3701_; lean_object* v_unused_3702_; lean_object* v_unused_3703_; 
v_unused_3699_ = lean_ctor_get(v___x_3613_, 4);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v___x_3613_, 3);
lean_dec(v_unused_3700_);
v_unused_3701_ = lean_ctor_get(v___x_3613_, 2);
lean_dec(v_unused_3701_);
v_unused_3702_ = lean_ctor_get(v___x_3613_, 1);
lean_dec(v_unused_3702_);
v_unused_3703_ = lean_ctor_get(v___x_3613_, 0);
lean_dec(v_unused_3703_);
v___x_3630_ = v___x_3613_;
v_isShared_3631_ = v_isSharedCheck_3698_;
goto v_resetjp_3629_;
}
else
{
lean_dec(v___x_3613_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3698_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
if (lean_obj_tag(v_l_3618_) == 0)
{
if (lean_obj_tag(v_r_3619_) == 0)
{
lean_object* v_size_3632_; lean_object* v_k_3633_; lean_object* v_v_3634_; lean_object* v_l_3635_; lean_object* v_r_3636_; lean_object* v_size_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
v_size_3632_ = lean_ctor_get(v_l_3618_, 0);
v_k_3633_ = lean_ctor_get(v_l_3618_, 1);
v_v_3634_ = lean_ctor_get(v_l_3618_, 2);
v_l_3635_ = lean_ctor_get(v_l_3618_, 3);
v_r_3636_ = lean_ctor_get(v_l_3618_, 4);
v_size_3637_ = lean_ctor_get(v_r_3619_, 0);
v___x_3638_ = lean_unsigned_to_nat(2u);
v___x_3639_ = lean_nat_mul(v___x_3638_, v_size_3637_);
v___x_3640_ = lean_nat_dec_lt(v_size_3632_, v___x_3639_);
lean_dec(v___x_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3669_; 
lean_inc(v_r_3636_);
lean_inc(v_l_3635_);
lean_inc(v_v_3634_);
lean_inc(v_k_3633_);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_l_3618_);
if (v_isSharedCheck_3669_ == 0)
{
lean_object* v_unused_3670_; lean_object* v_unused_3671_; lean_object* v_unused_3672_; lean_object* v_unused_3673_; lean_object* v_unused_3674_; 
v_unused_3670_ = lean_ctor_get(v_l_3618_, 4);
lean_dec(v_unused_3670_);
v_unused_3671_ = lean_ctor_get(v_l_3618_, 3);
lean_dec(v_unused_3671_);
v_unused_3672_ = lean_ctor_get(v_l_3618_, 2);
lean_dec(v_unused_3672_);
v_unused_3673_ = lean_ctor_get(v_l_3618_, 1);
lean_dec(v_unused_3673_);
v_unused_3674_ = lean_ctor_get(v_l_3618_, 0);
lean_dec(v_unused_3674_);
v___x_3642_ = v_l_3618_;
v_isShared_3643_ = v_isSharedCheck_3669_;
goto v_resetjp_3641_;
}
else
{
lean_dec(v_l_3618_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3669_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3659_; 
v___x_3644_ = lean_unsigned_to_nat(1u);
v___x_3645_ = lean_nat_add(v___x_3644_, v_size_3614_);
v___x_3646_ = lean_nat_add(v___x_3645_, v_size_3615_);
lean_dec(v_size_3615_);
if (lean_obj_tag(v_l_3635_) == 0)
{
lean_object* v_size_3667_; 
v_size_3667_ = lean_ctor_get(v_l_3635_, 0);
lean_inc(v_size_3667_);
v___y_3659_ = v_size_3667_;
goto v___jp_3658_;
}
else
{
lean_object* v___x_3668_; 
v___x_3668_ = lean_unsigned_to_nat(0u);
v___y_3659_ = v___x_3668_;
goto v___jp_3658_;
}
v___jp_3647_:
{
lean_object* v___x_3651_; lean_object* v___x_3653_; 
v___x_3651_ = lean_nat_add(v___y_3648_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec(v___y_3648_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 4, v_r_3619_);
lean_ctor_set(v___x_3642_, 3, v_r_3636_);
lean_ctor_set(v___x_3642_, 2, v_v_3617_);
lean_ctor_set(v___x_3642_, 1, v_k_3616_);
lean_ctor_set(v___x_3642_, 0, v___x_3651_);
v___x_3653_ = v___x_3642_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_k_3616_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v_v_3617_);
lean_ctor_set(v_reuseFailAlloc_3657_, 3, v_r_3636_);
lean_ctor_set(v_reuseFailAlloc_3657_, 4, v_r_3619_);
v___x_3653_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
lean_object* v___x_3655_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v___x_3653_);
lean_ctor_set(v___x_3630_, 3, v___y_3649_);
lean_ctor_set(v___x_3630_, 2, v_v_3634_);
lean_ctor_set(v___x_3630_, 1, v_k_3633_);
lean_ctor_set(v___x_3630_, 0, v___x_3646_);
v___x_3655_ = v___x_3630_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_k_3633_);
lean_ctor_set(v_reuseFailAlloc_3656_, 2, v_v_3634_);
lean_ctor_set(v_reuseFailAlloc_3656_, 3, v___y_3649_);
lean_ctor_set(v_reuseFailAlloc_3656_, 4, v___x_3653_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
v___jp_3658_:
{
lean_object* v___x_3660_; lean_object* v___x_3662_; 
v___x_3660_ = lean_nat_add(v___x_3645_, v___y_3659_);
lean_dec(v___y_3659_);
lean_dec(v___x_3645_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v_l_3635_);
lean_ctor_set(v___x_3432_, 0, v___x_3660_);
v___x_3662_ = v___x_3432_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3666_, 3, v_l_3429_);
lean_ctor_set(v_reuseFailAlloc_3666_, 4, v_l_3635_);
v___x_3662_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_nat_add(v___x_3644_, v_size_3637_);
if (lean_obj_tag(v_r_3636_) == 0)
{
lean_object* v_size_3664_; 
v_size_3664_ = lean_ctor_get(v_r_3636_, 0);
lean_inc(v_size_3664_);
v___y_3648_ = v___x_3663_;
v___y_3649_ = v___x_3662_;
v___y_3650_ = v_size_3664_;
goto v___jp_3647_;
}
else
{
lean_object* v___x_3665_; 
v___x_3665_ = lean_unsigned_to_nat(0u);
v___y_3648_ = v___x_3663_;
v___y_3649_ = v___x_3662_;
v___y_3650_ = v___x_3665_;
goto v___jp_3647_;
}
}
}
}
}
else
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
lean_del_object(v___x_3432_);
v___x_3675_ = lean_unsigned_to_nat(1u);
v___x_3676_ = lean_nat_add(v___x_3675_, v_size_3614_);
v___x_3677_ = lean_nat_add(v___x_3676_, v_size_3615_);
lean_dec(v_size_3615_);
v___x_3678_ = lean_nat_add(v___x_3676_, v_size_3632_);
lean_dec(v___x_3676_);
lean_inc_ref(v_l_3429_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v_l_3618_);
lean_ctor_set(v___x_3630_, 3, v_l_3429_);
lean_ctor_set(v___x_3630_, 2, v_v_3428_);
lean_ctor_set(v___x_3630_, 1, v_k_3427_);
lean_ctor_set(v___x_3630_, 0, v___x_3678_);
v___x_3680_ = v___x_3630_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3693_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3693_, 3, v_l_3429_);
lean_ctor_set(v_reuseFailAlloc_3693_, 4, v_l_3618_);
v___x_3680_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
v_isSharedCheck_3687_ = !lean_is_exclusive(v_l_3429_);
if (v_isSharedCheck_3687_ == 0)
{
lean_object* v_unused_3688_; lean_object* v_unused_3689_; lean_object* v_unused_3690_; lean_object* v_unused_3691_; lean_object* v_unused_3692_; 
v_unused_3688_ = lean_ctor_get(v_l_3429_, 4);
lean_dec(v_unused_3688_);
v_unused_3689_ = lean_ctor_get(v_l_3429_, 3);
lean_dec(v_unused_3689_);
v_unused_3690_ = lean_ctor_get(v_l_3429_, 2);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_l_3429_, 1);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_l_3429_, 0);
lean_dec(v_unused_3692_);
v___x_3682_ = v_l_3429_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_dec(v_l_3429_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 4, v_r_3619_);
lean_ctor_set(v___x_3682_, 3, v___x_3680_);
lean_ctor_set(v___x_3682_, 2, v_v_3617_);
lean_ctor_set(v___x_3682_, 1, v_k_3616_);
lean_ctor_set(v___x_3682_, 0, v___x_3677_);
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3677_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_k_3616_);
lean_ctor_set(v_reuseFailAlloc_3686_, 2, v_v_3617_);
lean_ctor_set(v_reuseFailAlloc_3686_, 3, v___x_3680_);
lean_ctor_set(v_reuseFailAlloc_3686_, 4, v_r_3619_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
else
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
lean_dec_ref_known(v_l_3618_, 5);
lean_del_object(v___x_3630_);
lean_dec(v_v_3617_);
lean_dec(v_k_3616_);
lean_dec(v_size_3615_);
lean_dec_ref_known(v_l_3429_, 5);
lean_del_object(v___x_3432_);
lean_dec(v_v_3428_);
lean_dec(v_k_3427_);
v___x_3694_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7);
v___x_3695_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3694_);
return v___x_3695_;
}
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_del_object(v___x_3630_);
lean_dec(v_r_3619_);
lean_dec(v_v_3617_);
lean_dec(v_k_3616_);
lean_dec(v_size_3615_);
lean_dec_ref_known(v_l_3429_, 5);
lean_del_object(v___x_3432_);
lean_dec(v_v_3428_);
lean_dec(v_k_3427_);
v___x_3696_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8);
v___x_3697_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3696_);
return v___x_3697_;
}
}
}
}
else
{
lean_object* v_size_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3708_; 
v_size_3704_ = lean_ctor_get(v_l_3429_, 0);
v___x_3705_ = lean_unsigned_to_nat(1u);
v___x_3706_ = lean_nat_add(v___x_3705_, v_size_3704_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v___x_3613_);
lean_ctor_set(v___x_3432_, 0, v___x_3706_);
v___x_3708_ = v___x_3432_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3709_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3709_, 3, v_l_3429_);
lean_ctor_set(v_reuseFailAlloc_3709_, 4, v___x_3613_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
else
{
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_l_3710_; 
v_l_3710_ = lean_ctor_get(v___x_3613_, 3);
lean_inc(v_l_3710_);
if (lean_obj_tag(v_l_3710_) == 0)
{
lean_object* v_r_3711_; 
v_r_3711_ = lean_ctor_get(v___x_3613_, 4);
lean_inc(v_r_3711_);
if (lean_obj_tag(v_r_3711_) == 0)
{
lean_object* v_size_3712_; lean_object* v_k_3713_; lean_object* v_v_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3728_; 
v_size_3712_ = lean_ctor_get(v___x_3613_, 0);
v_k_3713_ = lean_ctor_get(v___x_3613_, 1);
v_v_3714_ = lean_ctor_get(v___x_3613_, 2);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; lean_object* v_unused_3730_; 
v_unused_3729_ = lean_ctor_get(v___x_3613_, 4);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v___x_3613_, 3);
lean_dec(v_unused_3730_);
v___x_3716_ = v___x_3613_;
v_isShared_3717_ = v_isSharedCheck_3728_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_v_3714_);
lean_inc(v_k_3713_);
lean_inc(v_size_3712_);
lean_dec(v___x_3613_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3728_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v_size_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
v_size_3718_ = lean_ctor_get(v_l_3710_, 0);
v___x_3719_ = lean_unsigned_to_nat(1u);
v___x_3720_ = lean_nat_add(v___x_3719_, v_size_3712_);
lean_dec(v_size_3712_);
v___x_3721_ = lean_nat_add(v___x_3719_, v_size_3718_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v_l_3710_);
lean_ctor_set(v___x_3716_, 3, v_l_3429_);
lean_ctor_set(v___x_3716_, 2, v_v_3428_);
lean_ctor_set(v___x_3716_, 1, v_k_3427_);
lean_ctor_set(v___x_3716_, 0, v___x_3721_);
v___x_3723_ = v___x_3716_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_l_3429_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v_l_3710_);
v___x_3723_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v_r_3711_);
lean_ctor_set(v___x_3432_, 3, v___x_3723_);
lean_ctor_set(v___x_3432_, 2, v_v_3714_);
lean_ctor_set(v___x_3432_, 1, v_k_3713_);
lean_ctor_set(v___x_3432_, 0, v___x_3720_);
v___x_3725_ = v___x_3432_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_k_3713_);
lean_ctor_set(v_reuseFailAlloc_3726_, 2, v_v_3714_);
lean_ctor_set(v_reuseFailAlloc_3726_, 3, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3726_, 4, v_r_3711_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
lean_object* v_k_3731_; lean_object* v_v_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3756_; 
v_k_3731_ = lean_ctor_get(v___x_3613_, 1);
v_v_3732_ = lean_ctor_get(v___x_3613_, 2);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; 
v_unused_3757_ = lean_ctor_get(v___x_3613_, 4);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v___x_3613_, 3);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v___x_3613_, 0);
lean_dec(v_unused_3759_);
v___x_3734_ = v___x_3613_;
v_isShared_3735_ = v_isSharedCheck_3756_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_v_3732_);
lean_inc(v_k_3731_);
lean_dec(v___x_3613_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3756_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v_k_3736_; lean_object* v_v_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3752_; 
v_k_3736_ = lean_ctor_get(v_l_3710_, 1);
v_v_3737_ = lean_ctor_get(v_l_3710_, 2);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_l_3710_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; lean_object* v_unused_3754_; lean_object* v_unused_3755_; 
v_unused_3753_ = lean_ctor_get(v_l_3710_, 4);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_l_3710_, 3);
lean_dec(v_unused_3754_);
v_unused_3755_ = lean_ctor_get(v_l_3710_, 0);
lean_dec(v_unused_3755_);
v___x_3739_ = v_l_3710_;
v_isShared_3740_ = v_isSharedCheck_3752_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_v_3737_);
lean_inc(v_k_3736_);
lean_dec(v_l_3710_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3752_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3744_; 
v___x_3741_ = lean_unsigned_to_nat(3u);
v___x_3742_ = lean_unsigned_to_nat(1u);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 4, v_r_3711_);
lean_ctor_set(v___x_3739_, 3, v_r_3711_);
lean_ctor_set(v___x_3739_, 2, v_v_3428_);
lean_ctor_set(v___x_3739_, 1, v_k_3427_);
lean_ctor_set(v___x_3739_, 0, v___x_3742_);
v___x_3744_ = v___x_3739_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3751_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3751_, 3, v_r_3711_);
lean_ctor_set(v_reuseFailAlloc_3751_, 4, v_r_3711_);
v___x_3744_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
lean_object* v___x_3746_; 
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 3, v_r_3711_);
lean_ctor_set(v___x_3734_, 0, v___x_3742_);
v___x_3746_ = v___x_3734_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_k_3731_);
lean_ctor_set(v_reuseFailAlloc_3750_, 2, v_v_3732_);
lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_r_3711_);
lean_ctor_set(v_reuseFailAlloc_3750_, 4, v_r_3711_);
v___x_3746_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v___x_3746_);
lean_ctor_set(v___x_3432_, 3, v___x_3744_);
lean_ctor_set(v___x_3432_, 2, v_v_3737_);
lean_ctor_set(v___x_3432_, 1, v_k_3736_);
lean_ctor_set(v___x_3432_, 0, v___x_3741_);
v___x_3748_ = v___x_3432_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_k_3736_);
lean_ctor_set(v_reuseFailAlloc_3749_, 2, v_v_3737_);
lean_ctor_set(v_reuseFailAlloc_3749_, 3, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3749_, 4, v___x_3746_);
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
}
}
else
{
lean_object* v_r_3760_; 
v_r_3760_ = lean_ctor_get(v___x_3613_, 4);
lean_inc(v_r_3760_);
if (lean_obj_tag(v_r_3760_) == 0)
{
lean_object* v_k_3761_; lean_object* v_v_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3774_; 
v_k_3761_ = lean_ctor_get(v___x_3613_, 1);
v_v_3762_ = lean_ctor_get(v___x_3613_, 2);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3774_ == 0)
{
lean_object* v_unused_3775_; lean_object* v_unused_3776_; lean_object* v_unused_3777_; 
v_unused_3775_ = lean_ctor_get(v___x_3613_, 4);
lean_dec(v_unused_3775_);
v_unused_3776_ = lean_ctor_get(v___x_3613_, 3);
lean_dec(v_unused_3776_);
v_unused_3777_ = lean_ctor_get(v___x_3613_, 0);
lean_dec(v_unused_3777_);
v___x_3764_ = v___x_3613_;
v_isShared_3765_ = v_isSharedCheck_3774_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_v_3762_);
lean_inc(v_k_3761_);
lean_dec(v___x_3613_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3774_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3766_ = lean_unsigned_to_nat(3u);
v___x_3767_ = lean_unsigned_to_nat(1u);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 4, v_l_3710_);
lean_ctor_set(v___x_3764_, 2, v_v_3428_);
lean_ctor_set(v___x_3764_, 1, v_k_3427_);
lean_ctor_set(v___x_3764_, 0, v___x_3767_);
v___x_3769_ = v___x_3764_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3767_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3773_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3773_, 3, v_l_3710_);
lean_ctor_set(v_reuseFailAlloc_3773_, 4, v_l_3710_);
v___x_3769_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3771_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v_r_3760_);
lean_ctor_set(v___x_3432_, 3, v___x_3769_);
lean_ctor_set(v___x_3432_, 2, v_v_3762_);
lean_ctor_set(v___x_3432_, 1, v_k_3761_);
lean_ctor_set(v___x_3432_, 0, v___x_3766_);
v___x_3771_ = v___x_3432_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_3772_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_3772_, 3, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3772_, 4, v_r_3760_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3780_; 
v___x_3778_ = lean_unsigned_to_nat(2u);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v___x_3613_);
lean_ctor_set(v___x_3432_, 3, v_r_3760_);
lean_ctor_set(v___x_3432_, 0, v___x_3778_);
v___x_3780_ = v___x_3432_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_r_3760_);
lean_ctor_set(v_reuseFailAlloc_3781_, 4, v___x_3613_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v___x_3782_; lean_object* v___x_3784_; 
v___x_3782_ = lean_unsigned_to_nat(1u);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v___x_3613_);
lean_ctor_set(v___x_3432_, 3, v___x_3613_);
lean_ctor_set(v___x_3432_, 0, v___x_3782_);
v___x_3784_ = v___x_3432_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3785_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3785_, 3, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3785_, 4, v___x_3613_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = lean_unsigned_to_nat(1u);
v___x_3788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
lean_ctor_set(v___x_3788_, 1, v_k_3423_);
lean_ctor_set(v___x_3788_, 2, v_v_3424_);
lean_ctor_set(v___x_3788_, 3, v_t_3425_);
lean_ctor_set(v___x_3788_, 4, v_t_3425_);
return v___x_3788_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(lean_object* v_init_3789_, lean_object* v_x_3790_){
_start:
{
if (lean_obj_tag(v_x_3790_) == 0)
{
lean_object* v_k_3791_; lean_object* v_v_3792_; lean_object* v_l_3793_; lean_object* v_r_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v_k_3791_ = lean_ctor_get(v_x_3790_, 1);
lean_inc(v_k_3791_);
v_v_3792_ = lean_ctor_get(v_x_3790_, 2);
lean_inc(v_v_3792_);
v_l_3793_ = lean_ctor_get(v_x_3790_, 3);
lean_inc(v_l_3793_);
v_r_3794_ = lean_ctor_get(v_x_3790_, 4);
lean_inc(v_r_3794_);
lean_dec_ref_known(v_x_3790_, 5);
v___x_3795_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_3789_, v_l_3793_);
v___x_3796_ = 1;
v___x_3797_ = l_Lean_Name_toString(v_k_3791_, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3798_, 0, v_v_3792_);
v___x_3799_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v___x_3797_, v___x_3798_, v___x_3795_);
v_init_3789_ = v___x_3799_;
v_x_3790_ = v_r_3794_;
goto _start;
}
else
{
return v_init_3789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_m_3801_){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3802_ = lean_box(1);
v___x_3803_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v___x_3802_, v_m_3801_);
v___x_3804_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v___x_3807_, uint8_t v_updateToolchain_3808_, lean_object* v_ws_3809_, lean_object* v_dep_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v_baseName_3814_; lean_object* v_name_3815_; lean_object* v_opts_3816_; uint8_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v_baseName_3814_ = lean_ctor_get(v___x_3807_, 1);
v_name_3815_ = lean_ctor_get(v_dep_3810_, 0);
v_opts_3816_ = lean_ctor_get(v_dep_3810_, 4);
v___x_3817_ = 0;
lean_inc(v_baseName_3814_);
v___x_3818_ = l_Lean_Name_toString(v_baseName_3814_, v___x_3817_);
v___x_3819_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3820_ = lean_string_append(v___x_3818_, v___x_3819_);
lean_inc(v_name_3815_);
v___x_3821_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3815_, v_updateToolchain_3808_);
v___x_3822_ = lean_string_append(v___x_3820_, v___x_3821_);
lean_dec_ref(v___x_3821_);
v___x_3823_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3824_ = lean_string_append(v___x_3822_, v___x_3823_);
lean_inc(v_opts_3816_);
v___x_3825_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_opts_3816_);
v___x_3826_ = lean_unsigned_to_nat(80u);
v___x_3827_ = l_Lean_Json_pretty(v___x_3825_, v___x_3826_);
v___x_3828_ = lean_string_append(v___x_3824_, v___x_3827_);
lean_dec_ref(v___x_3827_);
v___x_3829_ = 0;
v___x_3830_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3830_, 0, v___x_3828_);
lean_ctor_set_uint8(v___x_3830_, sizeof(void*)*1, v___x_3829_);
lean_inc_ref(v___y_3812_);
v___x_3831_ = lean_apply_2(v___y_3812_, v___x_3830_, lean_box(0));
v___x_3832_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3809_, v___x_3807_, v_dep_3810_, v___y_3811_, v___y_3812_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v___x_3833_, lean_object* v_updateToolchain_3834_, lean_object* v_ws_3835_, lean_object* v_dep_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
uint8_t v_updateToolchain_boxed_3840_; lean_object* v_res_3841_; 
v_updateToolchain_boxed_3840_ = lean_unbox(v_updateToolchain_3834_);
v_res_3841_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v___x_3833_, v_updateToolchain_boxed_3840_, v_ws_3835_, v_dep_3836_, v___y_3837_, v___y_3838_);
lean_dec_ref(v___y_3838_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_a_3842_, lean_object* v_b_3843_){
_start:
{
lean_object* v_next_3844_; 
v_next_3844_ = lean_ctor_get(v_a_3842_, 0);
lean_inc(v_next_3844_);
if (lean_obj_tag(v_next_3844_) == 0)
{
lean_dec_ref(v_a_3842_);
return v_b_3843_;
}
else
{
lean_object* v_upperBound_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3865_; 
v_upperBound_3845_ = lean_ctor_get(v_a_3842_, 1);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_a_3842_);
if (v_isSharedCheck_3865_ == 0)
{
lean_object* v_unused_3866_; 
v_unused_3866_ = lean_ctor_get(v_a_3842_, 0);
lean_dec(v_unused_3866_);
v___x_3847_ = v_a_3842_;
v_isShared_3848_ = v_isSharedCheck_3865_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_upperBound_3845_);
lean_dec(v_a_3842_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3865_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v_val_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3864_; 
v_val_3849_ = lean_ctor_get(v_next_3844_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_next_3844_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3851_ = v_next_3844_;
v_isShared_3852_ = v_isSharedCheck_3864_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_val_3849_);
lean_dec(v_next_3844_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3864_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
uint8_t v___x_3853_; 
v___x_3853_ = lean_nat_dec_lt(v_val_3849_, v_upperBound_3845_);
if (v___x_3853_ == 0)
{
lean_del_object(v___x_3851_);
lean_dec(v_val_3849_);
lean_del_object(v___x_3847_);
lean_dec(v_upperBound_3845_);
return v_b_3843_;
}
else
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3857_; 
v___x_3854_ = lean_unsigned_to_nat(1u);
v___x_3855_ = lean_nat_add(v_val_3849_, v___x_3854_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 0, v___x_3855_);
v___x_3857_ = v___x_3851_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
lean_object* v___x_3859_; 
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v___x_3857_);
v___x_3859_ = v___x_3847_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_upperBound_3845_);
v___x_3859_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3860_; 
v___x_3860_ = lean_array_push(v_b_3843_, v_val_3849_);
v_a_3842_ = v___x_3859_;
v_b_3843_ = v___x_3860_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_n_3867_, lean_object* v_f_3868_, lean_object* v_xs_3869_, lean_object* v_k_3870_, lean_object* v_acc_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
uint8_t v___x_3875_; 
v___x_3875_ = lean_nat_dec_lt(v_k_3870_, v_n_3867_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
lean_dec(v_k_3870_);
lean_dec_ref(v_f_3868_);
v___x_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3876_, 0, v_acc_3871_);
lean_ctor_set(v___x_3876_, 1, v___y_3872_);
v___x_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3876_);
return v___x_3877_;
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = lean_array_fget_borrowed(v_xs_3869_, v_k_3870_);
lean_inc_ref(v_f_3868_);
lean_inc_ref(v___y_3873_);
lean_inc(v___x_3878_);
v___x_3879_ = lean_apply_4(v_f_3868_, v___x_3878_, v___y_3872_, v___y_3873_, lean_box(0));
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v_fst_3881_; lean_object* v_snd_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v_fst_3881_ = lean_ctor_get(v_a_3880_, 0);
lean_inc(v_fst_3881_);
v_snd_3882_ = lean_ctor_get(v_a_3880_, 1);
lean_inc(v_snd_3882_);
lean_dec(v_a_3880_);
v___x_3883_ = lean_unsigned_to_nat(1u);
v___x_3884_ = lean_nat_add(v_k_3870_, v___x_3883_);
lean_dec(v_k_3870_);
v___x_3885_ = lean_array_push(v_acc_3871_, v_fst_3881_);
v_k_3870_ = v___x_3884_;
v_acc_3871_ = v___x_3885_;
v___y_3872_ = v_snd_3882_;
goto _start;
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_acc_3871_);
lean_dec(v_k_3870_);
lean_dec_ref(v_f_3868_);
v_a_3887_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3879_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3879_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object* v_n_3895_, lean_object* v_f_3896_, lean_object* v_xs_3897_, lean_object* v_k_3898_, lean_object* v_acc_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_3895_, v_f_3896_, v_xs_3897_, v_k_3898_, v_acc_3899_, v___y_3900_, v___y_3901_);
lean_dec_ref(v___y_3901_);
lean_dec_ref(v_xs_3897_);
lean_dec(v_n_3895_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object* v_upperBound_3904_, lean_object* v_fst_3905_, lean_object* v___x_3906_, lean_object* v_leanOpts_3907_, lean_object* v_a_3908_, lean_object* v_b_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_fst_3914_; lean_object* v_snd_3915_; uint8_t v___x_3919_; 
v___x_3919_ = lean_nat_dec_lt(v_a_3908_, v_upperBound_3904_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
lean_dec(v_a_3908_);
lean_dec_ref(v_leanOpts_3907_);
v___x_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3920_, 0, v_b_3909_);
lean_ctor_set(v___x_3920_, 1, v___y_3910_);
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
return v___x_3921_;
}
else
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = lean_array_fget_borrowed(v_fst_3905_, v_a_3908_);
lean_inc(v___x_3922_);
v___x_3923_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_3922_, v___y_3910_, v___y_3911_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3977_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3926_ = v___x_3923_;
v_isShared_3927_ = v_isSharedCheck_3977_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3923_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3977_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v_snd_3928_; lean_object* v___x_3929_; lean_object* v_opts_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v_snd_3928_ = lean_ctor_get(v_a_3924_, 1);
lean_inc(v_snd_3928_);
lean_dec(v_a_3924_);
v___x_3929_ = lean_array_fget_borrowed(v___x_3906_, v_a_3908_);
v_opts_3930_ = lean_ctor_get(v___x_3929_, 4);
v___x_3931_ = lean_unsigned_to_nat(0u);
v___x_3932_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3907_);
lean_inc(v_opts_3930_);
lean_inc(v___x_3922_);
v___x_3933_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_3909_, v___x_3922_, v_opts_3930_, v_leanOpts_3907_, v___x_3919_, v___x_3932_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v_a_3935_; lean_object* v___x_3936_; uint8_t v___x_3937_; 
lean_del_object(v___x_3926_);
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
v_a_3935_ = lean_ctor_get(v___x_3933_, 1);
lean_inc(v_a_3935_);
lean_dec_ref_known(v___x_3933_, 2);
v___x_3936_ = lean_array_get_size(v_a_3935_);
v___x_3937_ = lean_nat_dec_lt(v___x_3931_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_dec(v_a_3935_);
v_fst_3914_ = v_a_3934_;
v_snd_3915_ = v_snd_3928_;
goto v___jp_3913_;
}
else
{
lean_object* v___x_3938_; size_t v___x_3939_; size_t v___x_3940_; lean_object* v___x_3941_; 
v___x_3938_ = lean_box(0);
v___x_3939_ = ((size_t)0ULL);
v___x_3940_ = lean_usize_of_nat(v___x_3936_);
v___x_3941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3935_, v___x_3939_, v___x_3940_, v___x_3938_, v___y_3911_);
lean_dec(v_a_3935_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_dec_ref_known(v___x_3941_, 1);
v_fst_3914_ = v_a_3934_;
v_snd_3915_ = v_snd_3928_;
goto v___jp_3913_;
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec(v_a_3934_);
lean_dec(v_snd_3928_);
lean_dec(v_a_3908_);
lean_dec_ref(v_leanOpts_3907_);
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3941_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3941_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
else
{
lean_object* v_a_3950_; lean_object* v___x_3951_; uint8_t v___x_3952_; 
lean_dec(v_snd_3928_);
lean_dec(v_a_3908_);
lean_dec_ref(v_leanOpts_3907_);
v_a_3950_ = lean_ctor_get(v___x_3933_, 1);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3933_, 2);
v___x_3951_ = lean_array_get_size(v_a_3950_);
v___x_3952_ = lean_nat_dec_lt(v___x_3931_, v___x_3951_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
lean_dec(v_a_3950_);
v___x_3953_ = lean_box(0);
if (v_isShared_3927_ == 0)
{
lean_ctor_set_tag(v___x_3926_, 1);
lean_ctor_set(v___x_3926_, 0, v___x_3953_);
v___x_3955_ = v___x_3926_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
else
{
lean_object* v___x_3957_; size_t v___x_3958_; size_t v___x_3959_; lean_object* v___x_3960_; 
lean_del_object(v___x_3926_);
v___x_3957_ = lean_box(0);
v___x_3958_ = ((size_t)0ULL);
v___x_3959_ = lean_usize_of_nat(v___x_3951_);
v___x_3960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3950_, v___x_3958_, v___x_3959_, v___x_3957_, v___y_3911_);
lean_dec(v_a_3950_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3967_ == 0)
{
lean_object* v_unused_3968_; 
v_unused_3968_ = lean_ctor_get(v___x_3960_, 0);
lean_dec(v_unused_3968_);
v___x_3962_ = v___x_3960_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_dec(v___x_3960_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
lean_ctor_set_tag(v___x_3962_, 1);
lean_ctor_set(v___x_3962_, 0, v___x_3957_);
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3957_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
v_a_3969_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3960_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3960_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec_ref(v_b_3909_);
lean_dec(v_a_3908_);
lean_dec_ref(v_leanOpts_3907_);
v_a_3978_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3923_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3923_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
v___jp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3916_ = lean_unsigned_to_nat(1u);
v___x_3917_ = lean_nat_add(v_a_3908_, v___x_3916_);
lean_dec(v_a_3908_);
v_a_3908_ = v___x_3917_;
v_b_3909_ = v_fst_3914_;
v___y_3910_ = v_snd_3915_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object* v_upperBound_3986_, lean_object* v_fst_3987_, lean_object* v___x_3988_, lean_object* v_leanOpts_3989_, lean_object* v_a_3990_, lean_object* v_b_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_3986_, v_fst_3987_, v___x_3988_, v_leanOpts_3989_, v_a_3990_, v_b_3991_, v___y_3992_, v___y_3993_);
lean_dec_ref(v___y_3993_);
lean_dec_ref(v___x_3988_);
lean_dec_ref(v_fst_3987_);
lean_dec(v_upperBound_3986_);
return v_res_3995_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(lean_object* v___x_3996_, lean_object* v_x_3997_){
_start:
{
lean_object* v_baseName_3998_; lean_object* v_name_3999_; uint8_t v___x_4000_; 
v_baseName_3998_ = lean_ctor_get(v_x_3997_, 1);
v_name_3999_ = lean_ctor_get(v___x_3996_, 0);
v___x_4000_ = lean_name_eq(v_baseName_3998_, v_name_3999_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___x_4001_, lean_object* v_x_4002_){
_start:
{
uint8_t v_res_4003_; lean_object* v_r_4004_; 
v_res_4003_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(v___x_4001_, v_x_4002_);
lean_dec_ref(v_x_4002_);
lean_dec_ref(v___x_4001_);
v_r_4004_ = lean_box(v_res_4003_);
return v_r_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object* v_pkg_4005_, lean_object* v_leanOpts_4006_, uint8_t v_reconfigure_4007_, lean_object* v_as_4008_, size_t v_i_4009_, size_t v_stop_4010_, lean_object* v_b_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
uint8_t v___x_4015_; 
v___x_4015_ = lean_usize_dec_eq(v_i_4009_, v_stop_4010_);
if (v___x_4015_ == 0)
{
lean_object* v_ws_4016_; lean_object* v_depIdxs_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4114_; 
v_ws_4016_ = lean_ctor_get(v_b_4011_, 0);
v_depIdxs_4017_ = lean_ctor_get(v_b_4011_, 1);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_b_4011_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4019_ = v_b_4011_;
v_isShared_4020_ = v_isSharedCheck_4114_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_depIdxs_4017_);
lean_inc(v_ws_4016_);
lean_dec(v_b_4011_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4114_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v_packages_4021_; size_t v___x_4022_; size_t v___x_4023_; lean_object* v___x_4024_; lean_object* v___f_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v_packages_4021_ = lean_ctor_get(v_ws_4016_, 4);
v___x_4022_ = ((size_t)1ULL);
v___x_4023_ = lean_usize_sub(v_i_4009_, v___x_4022_);
v___x_4024_ = lean_array_uget_borrowed(v_as_4008_, v___x_4023_);
lean_inc(v___x_4024_);
v___f_4025_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4025_, 0, v___x_4024_);
v___x_4026_ = lean_unsigned_to_nat(0u);
v___x_4027_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_4025_, v_packages_4021_, v___x_4026_);
if (lean_obj_tag(v___x_4027_) == 1)
{
lean_object* v_val_4028_; lean_object* v___x_4029_; lean_object* v___x_4031_; 
v_val_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_val_4028_);
lean_dec_ref_known(v___x_4027_, 1);
v___x_4029_ = lean_array_push(v_depIdxs_4017_, v_val_4028_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 1, v___x_4029_);
v___x_4031_ = v___x_4019_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_ws_4016_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v___x_4029_);
v___x_4031_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
v_i_4009_ = v___x_4023_;
v_b_4011_ = v___x_4031_;
goto _start;
}
}
else
{
lean_object* v_baseName_4034_; lean_object* v_name_4035_; lean_object* v_opts_4036_; uint8_t v___x_4037_; 
lean_dec(v___x_4027_);
v_baseName_4034_ = lean_ctor_get(v_pkg_4005_, 1);
v_name_4035_ = lean_ctor_get(v___x_4024_, 0);
v_opts_4036_ = lean_ctor_get(v___x_4024_, 4);
v___x_4037_ = lean_name_eq(v_baseName_4034_, v_name_4035_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; 
lean_inc_ref(v___y_4013_);
lean_inc_ref(v_ws_4016_);
lean_inc(v___x_4024_);
lean_inc_ref(v_pkg_4005_);
v___x_4038_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_4005_, v___x_4024_, v_ws_4016_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4097_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4041_ = v___x_4038_;
v_isShared_4042_ = v_isSharedCheck_4097_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4038_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4097_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v_fst_4043_; lean_object* v_snd_4044_; lean_object* v___x_4045_; lean_object* v_wsIdx_4046_; lean_object* v___x_4047_; 
v_fst_4043_ = lean_ctor_get(v_a_4039_, 0);
lean_inc(v_fst_4043_);
v_snd_4044_ = lean_ctor_get(v_a_4039_, 1);
lean_inc(v_snd_4044_);
lean_dec(v_a_4039_);
v___x_4045_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_4046_ = lean_array_get_size(v_packages_4021_);
lean_inc_ref(v_leanOpts_4006_);
lean_inc(v_opts_4036_);
v___x_4047_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_4016_, v_fst_4043_, v_opts_4036_, v_leanOpts_4006_, v_reconfigure_4007_, v___x_4045_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v_a_4049_; lean_object* v___x_4050_; lean_object* v___x_4052_; 
lean_del_object(v___x_4041_);
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
v_a_4049_ = lean_ctor_get(v___x_4047_, 1);
lean_inc(v_a_4049_);
lean_dec_ref_known(v___x_4047_, 2);
v___x_4050_ = lean_array_push(v_depIdxs_4017_, v_wsIdx_4046_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 1, v___x_4050_);
lean_ctor_set(v___x_4019_, 0, v_a_4048_);
v___x_4052_ = v___x_4019_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4048_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4053_; uint8_t v___x_4054_; 
v___x_4053_ = lean_array_get_size(v_a_4049_);
v___x_4054_ = lean_nat_dec_lt(v___x_4026_, v___x_4053_);
if (v___x_4054_ == 0)
{
lean_dec(v_a_4049_);
v_i_4009_ = v___x_4023_;
v_b_4011_ = v___x_4052_;
v___y_4012_ = v_snd_4044_;
goto _start;
}
else
{
lean_object* v___x_4056_; size_t v___x_4057_; size_t v___x_4058_; lean_object* v___x_4059_; 
v___x_4056_ = lean_box(0);
v___x_4057_ = ((size_t)0ULL);
v___x_4058_ = lean_usize_of_nat(v___x_4053_);
v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4049_, v___x_4057_, v___x_4058_, v___x_4056_, v___y_4013_);
lean_dec(v_a_4049_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_dec_ref_known(v___x_4059_, 1);
v_i_4009_ = v___x_4023_;
v_b_4011_ = v___x_4052_;
v___y_4012_ = v_snd_4044_;
goto _start;
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec_ref(v___x_4052_);
lean_dec(v_snd_4044_);
lean_dec_ref(v_leanOpts_4006_);
lean_dec_ref(v_pkg_4005_);
v_a_4061_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4059_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4059_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4071_; uint8_t v___x_4072_; 
lean_dec(v_snd_4044_);
lean_del_object(v___x_4019_);
lean_dec_ref(v_depIdxs_4017_);
lean_dec_ref(v_leanOpts_4006_);
lean_dec_ref(v_pkg_4005_);
v_a_4070_ = lean_ctor_get(v___x_4047_, 1);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4047_, 2);
v___x_4071_ = lean_array_get_size(v_a_4070_);
v___x_4072_ = lean_nat_dec_lt(v___x_4026_, v___x_4071_);
if (v___x_4072_ == 0)
{
lean_object* v___x_4073_; lean_object* v___x_4075_; 
lean_dec(v_a_4070_);
v___x_4073_ = lean_box(0);
if (v_isShared_4042_ == 0)
{
lean_ctor_set_tag(v___x_4041_, 1);
lean_ctor_set(v___x_4041_, 0, v___x_4073_);
v___x_4075_ = v___x_4041_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
else
{
lean_object* v___x_4077_; size_t v___x_4078_; size_t v___x_4079_; lean_object* v___x_4080_; 
lean_del_object(v___x_4041_);
v___x_4077_ = lean_box(0);
v___x_4078_ = ((size_t)0ULL);
v___x_4079_ = lean_usize_of_nat(v___x_4071_);
v___x_4080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4070_, v___x_4078_, v___x_4079_, v___x_4077_, v___y_4013_);
lean_dec(v_a_4070_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; 
v_unused_4088_ = lean_ctor_get(v___x_4080_, 0);
lean_dec(v_unused_4088_);
v___x_4082_ = v___x_4080_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_dec(v___x_4080_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
lean_ctor_set_tag(v___x_4082_, 1);
lean_ctor_set(v___x_4082_, 0, v___x_4077_);
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4077_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
v_a_4089_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4080_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4080_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_del_object(v___x_4019_);
lean_dec_ref(v_depIdxs_4017_);
lean_dec_ref(v_ws_4016_);
lean_dec_ref(v_leanOpts_4006_);
lean_dec_ref(v_pkg_4005_);
v_a_4098_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4038_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4038_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
else
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_inc(v_baseName_4034_);
lean_del_object(v___x_4019_);
lean_dec_ref(v_depIdxs_4017_);
lean_dec_ref(v_ws_4016_);
lean_dec(v___y_4012_);
lean_dec_ref(v_leanOpts_4006_);
lean_dec_ref(v_pkg_4005_);
v___x_4106_ = l_Lean_Name_toString(v_baseName_4034_, v___x_4015_);
v___x_4107_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_4108_ = lean_string_append(v___x_4106_, v___x_4107_);
v___x_4109_ = 3;
v___x_4110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set_uint8(v___x_4110_, sizeof(void*)*1, v___x_4109_);
lean_inc_ref(v___y_4013_);
v___x_4111_ = lean_apply_2(v___y_4013_, v___x_4110_, lean_box(0));
v___x_4112_ = lean_box(0);
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
return v___x_4113_;
}
}
}
}
else
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
lean_dec_ref(v_leanOpts_4006_);
lean_dec_ref(v_pkg_4005_);
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v_b_4011_);
lean_ctor_set(v___x_4115_, 1, v___y_4012_);
v___x_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
return v___x_4116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___boxed(lean_object* v_pkg_4117_, lean_object* v_leanOpts_4118_, lean_object* v_reconfigure_4119_, lean_object* v_as_4120_, lean_object* v_i_4121_, lean_object* v_stop_4122_, lean_object* v_b_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
uint8_t v_reconfigure_boxed_4127_; size_t v_i_boxed_4128_; size_t v_stop_boxed_4129_; lean_object* v_res_4130_; 
v_reconfigure_boxed_4127_ = lean_unbox(v_reconfigure_4119_);
v_i_boxed_4128_ = lean_unbox_usize(v_i_4121_);
lean_dec(v_i_4121_);
v_stop_boxed_4129_ = lean_unbox_usize(v_stop_4122_);
lean_dec(v_stop_4122_);
v_res_4130_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4117_, v_leanOpts_4118_, v_reconfigure_boxed_4127_, v_as_4120_, v_i_boxed_4128_, v_stop_boxed_4129_, v_b_4123_, v___y_4124_, v___y_4125_);
lean_dec_ref(v___y_4125_);
lean_dec_ref(v_as_4120_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object* v_leanOpts_4131_, uint8_t v_reconfigure_4132_, lean_object* v_ws_4133_, lean_object* v_i_4134_, lean_object* v_next_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_packages_4139_; lean_object* v_pkg_4140_; lean_object* v_ws_4142_; lean_object* v_depIdxs_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v_____x_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v_depConfigs_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v_s_4164_; lean_object* v___x_4165_; uint8_t v___x_4166_; 
v_packages_4139_ = lean_ctor_get(v_ws_4133_, 4);
v_pkg_4140_ = lean_array_fget(v_packages_4139_, v_i_4134_);
lean_dec(v_i_4134_);
v_depConfigs_4161_ = lean_ctor_get(v_pkg_4140_, 12);
v___x_4162_ = lean_array_get_size(v_depConfigs_4161_);
v___x_4163_ = lean_mk_empty_array_with_capacity(v___x_4162_);
lean_inc_ref(v___x_4163_);
lean_inc_ref(v_ws_4133_);
v_s_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_4164_, 0, v_ws_4133_);
lean_ctor_set(v_s_4164_, 1, v___x_4163_);
v___x_4165_ = lean_unsigned_to_nat(0u);
v___x_4166_ = lean_nat_dec_le(v___x_4162_, v___x_4162_);
if (v___x_4166_ == 0)
{
uint8_t v___x_4167_; 
v___x_4167_ = lean_nat_dec_lt(v___x_4165_, v___x_4162_);
if (v___x_4167_ == 0)
{
lean_object* v_ws_4168_; lean_object* v_packages_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; 
lean_dec_ref_known(v_s_4164_, 2);
v_ws_4168_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4133_, v_pkg_4140_, v___x_4163_);
v_packages_4169_ = lean_ctor_get(v_ws_4168_, 4);
lean_inc_ref(v_packages_4169_);
v___x_4170_ = lean_array_get_size(v_packages_4169_);
lean_dec_ref(v_packages_4169_);
v___x_4171_ = lean_nat_dec_lt(v_next_4135_, v___x_4170_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
lean_dec(v_next_4135_);
lean_dec_ref(v_leanOpts_4131_);
v___x_4172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4172_, 0, v_ws_4168_);
lean_ctor_set(v___x_4172_, 1, v___y_4136_);
v___x_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
return v___x_4173_;
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = lean_unsigned_to_nat(1u);
v___x_4175_ = lean_nat_add(v_next_4135_, v___x_4174_);
v_ws_4133_ = v_ws_4168_;
v_i_4134_ = v_next_4135_;
v_next_4135_ = v___x_4175_;
goto _start;
}
}
else
{
size_t v___x_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
lean_dec_ref(v___x_4163_);
lean_dec_ref(v_ws_4133_);
v___x_4177_ = lean_usize_of_nat(v___x_4162_);
v___x_4178_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4131_);
lean_inc(v_pkg_4140_);
v___x_4179_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4140_, v_leanOpts_4131_, v_reconfigure_4132_, v_depConfigs_4161_, v___x_4177_, v___x_4178_, v_s_4164_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v_fst_4181_; lean_object* v_snd_4182_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
v_fst_4181_ = lean_ctor_get(v_a_4180_, 0);
lean_inc(v_fst_4181_);
v_snd_4182_ = lean_ctor_get(v_a_4180_, 1);
lean_inc(v_snd_4182_);
lean_dec(v_a_4180_);
v_____x_4156_ = v_fst_4181_;
v___y_4157_ = v_snd_4182_;
v___y_4158_ = v___y_4137_;
goto v___jp_4155_;
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
lean_dec(v_pkg_4140_);
lean_dec(v_next_4135_);
lean_dec_ref(v_leanOpts_4131_);
v_a_4183_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4179_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4179_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
}
else
{
uint8_t v___x_4191_; 
v___x_4191_ = lean_nat_dec_lt(v___x_4165_, v___x_4162_);
if (v___x_4191_ == 0)
{
lean_dec_ref_known(v_s_4164_, 2);
v_ws_4142_ = v_ws_4133_;
v_depIdxs_4143_ = v___x_4163_;
v___y_4144_ = v___y_4136_;
v___y_4145_ = v___y_4137_;
goto v___jp_4141_;
}
else
{
size_t v___x_4192_; size_t v___x_4193_; lean_object* v___x_4194_; 
lean_dec_ref(v___x_4163_);
lean_dec_ref(v_ws_4133_);
v___x_4192_ = lean_usize_of_nat(v___x_4162_);
v___x_4193_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4131_);
lean_inc(v_pkg_4140_);
v___x_4194_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4140_, v_leanOpts_4131_, v_reconfigure_4132_, v_depConfigs_4161_, v___x_4192_, v___x_4193_, v_s_4164_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v_fst_4196_; lean_object* v_snd_4197_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4194_, 1);
v_fst_4196_ = lean_ctor_get(v_a_4195_, 0);
lean_inc(v_fst_4196_);
v_snd_4197_ = lean_ctor_get(v_a_4195_, 1);
lean_inc(v_snd_4197_);
lean_dec(v_a_4195_);
v_____x_4156_ = v_fst_4196_;
v___y_4157_ = v_snd_4197_;
v___y_4158_ = v___y_4137_;
goto v___jp_4155_;
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec(v_pkg_4140_);
lean_dec(v_next_4135_);
lean_dec_ref(v_leanOpts_4131_);
v_a_4198_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4194_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4194_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
}
v___jp_4141_:
{
lean_object* v_ws_4146_; lean_object* v_packages_4147_; lean_object* v___x_4148_; uint8_t v___x_4149_; 
v_ws_4146_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4142_, v_pkg_4140_, v_depIdxs_4143_);
v_packages_4147_ = lean_ctor_get(v_ws_4146_, 4);
lean_inc_ref(v_packages_4147_);
v___x_4148_ = lean_array_get_size(v_packages_4147_);
lean_dec_ref(v_packages_4147_);
v___x_4149_ = lean_nat_dec_lt(v_next_4135_, v___x_4148_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; lean_object* v___x_4151_; 
lean_dec(v_next_4135_);
lean_dec_ref(v_leanOpts_4131_);
v___x_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4150_, 0, v_ws_4146_);
lean_ctor_set(v___x_4150_, 1, v___y_4144_);
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
return v___x_4151_;
}
else
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4152_ = lean_unsigned_to_nat(1u);
v___x_4153_ = lean_nat_add(v_next_4135_, v___x_4152_);
v_ws_4133_ = v_ws_4146_;
v_i_4134_ = v_next_4135_;
v_next_4135_ = v___x_4153_;
v___y_4136_ = v___y_4144_;
v___y_4137_ = v___y_4145_;
goto _start;
}
}
v___jp_4155_:
{
lean_object* v_ws_4159_; lean_object* v_depIdxs_4160_; 
v_ws_4159_ = lean_ctor_get(v_____x_4156_, 0);
lean_inc_ref(v_ws_4159_);
v_depIdxs_4160_ = lean_ctor_get(v_____x_4156_, 1);
lean_inc_ref(v_depIdxs_4160_);
lean_dec_ref(v_____x_4156_);
v_ws_4142_ = v_ws_4159_;
v_depIdxs_4143_ = v_depIdxs_4160_;
v___y_4144_ = v___y_4157_;
v___y_4145_ = v___y_4158_;
goto v___jp_4141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object* v_leanOpts_4206_, lean_object* v_reconfigure_4207_, lean_object* v_ws_4208_, lean_object* v_i_4209_, lean_object* v_next_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
uint8_t v_reconfigure_boxed_4214_; lean_object* v_res_4215_; 
v_reconfigure_boxed_4214_ = lean_unbox(v_reconfigure_4207_);
v_res_4215_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4206_, v_reconfigure_boxed_4214_, v_ws_4208_, v_i_4209_, v_next_4210_, v___y_4211_, v___y_4212_);
lean_dec_ref(v___y_4212_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4218_, lean_object* v_toUpdate_4219_, lean_object* v_leanOpts_4220_, uint8_t v_updateToolchain_4221_, lean_object* v_a_4222_){
_start:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4224_ = lean_box(1);
v___x_4225_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4222_, v_ws_4218_, v_toUpdate_4219_, v___x_4224_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v_snd_4227_; uint8_t v___x_4228_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v_snd_4227_ = lean_ctor_get(v_a_4226_, 1);
lean_inc(v_snd_4227_);
lean_dec(v_a_4226_);
v___x_4228_ = 1;
if (v_updateToolchain_4221_ == 0)
{
lean_object* v_packages_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v_wsIdx_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v_packages_4229_ = lean_ctor_get(v_ws_4218_, 4);
v___x_4230_ = lean_unsigned_to_nat(0u);
v___x_4231_ = lean_array_fget_borrowed(v_packages_4229_, v___x_4230_);
v_wsIdx_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_wsIdx_4232_);
v___x_4233_ = lean_array_get_size(v_packages_4229_);
v___x_4234_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4220_, v___x_4228_, v_ws_4218_, v_wsIdx_4232_, v___x_4233_, v_snd_4227_, v_a_4222_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4252_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4237_ = v___x_4234_;
v_isShared_4238_ = v_isSharedCheck_4252_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4234_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4252_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v_fst_4239_; lean_object* v_snd_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4251_; 
v_fst_4239_ = lean_ctor_get(v_a_4235_, 0);
v_snd_4240_ = lean_ctor_get(v_a_4235_, 1);
v_isSharedCheck_4251_ = !lean_is_exclusive(v_a_4235_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4242_ = v_a_4235_;
v_isShared_4243_ = v_isSharedCheck_4251_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_snd_4240_);
lean_inc(v_fst_4239_);
lean_dec(v_a_4235_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4251_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4244_; lean_object* v___x_4246_; 
v___x_4244_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4239_);
if (v_isShared_4243_ == 0)
{
lean_ctor_set(v___x_4242_, 0, v___x_4244_);
v___x_4246_ = v___x_4242_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4244_);
lean_ctor_set(v_reuseFailAlloc_4250_, 1, v_snd_4240_);
v___x_4246_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
lean_object* v___x_4248_; 
if (v_isShared_4238_ == 0)
{
lean_ctor_set(v___x_4237_, 0, v___x_4246_);
v___x_4248_ = v___x_4237_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4246_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
else
{
return v___x_4234_;
}
}
else
{
lean_object* v_packages_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v_depConfigs_4256_; lean_object* v___x_4257_; lean_object* v___f_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v_packages_4253_ = lean_ctor_get(v_ws_4218_, 4);
v___x_4254_ = lean_unsigned_to_nat(0u);
v___x_4255_ = lean_array_fget_borrowed(v_packages_4253_, v___x_4254_);
v_depConfigs_4256_ = lean_ctor_get(v___x_4255_, 12);
v___x_4257_ = lean_box(v_updateToolchain_4221_);
lean_inc_ref(v_ws_4218_);
lean_inc(v___x_4255_);
v___f_4258_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4258_, 0, v___x_4255_);
lean_closure_set(v___f_4258_, 1, v___x_4257_);
lean_closure_set(v___f_4258_, 2, v_ws_4218_);
v___x_4259_ = lean_array_get_size(v_depConfigs_4256_);
lean_inc_ref(v_depConfigs_4256_);
v___x_4260_ = l_Array_reverse___redArg(v_depConfigs_4256_);
v___x_4261_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4262_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4259_, v___f_4258_, v___x_4260_, v___x_4254_, v___x_4261_, v_snd_4227_, v_a_4222_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v_fst_4264_; lean_object* v_snd_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4337_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
v_fst_4264_ = lean_ctor_get(v_a_4263_, 0);
v_snd_4265_ = lean_ctor_get(v_a_4263_, 1);
v_isSharedCheck_4337_ = !lean_is_exclusive(v_a_4263_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4267_ = v_a_4263_;
v_isShared_4268_ = v_isSharedCheck_4337_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_snd_4265_);
lean_inc(v_fst_4264_);
lean_dec(v_a_4263_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4337_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4269_; 
lean_inc_ref(v_ws_4218_);
v___x_4269_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4222_, v_ws_4218_, v_fst_4264_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v___x_4270_; lean_object* v___x_4271_; 
lean_dec_ref_known(v___x_4269_, 1);
v___x_4270_ = lean_array_get_size(v_packages_4253_);
lean_inc_ref(v_leanOpts_4220_);
v___x_4271_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4259_, v_fst_4264_, v___x_4260_, v_leanOpts_4220_, v___x_4254_, v_ws_4218_, v_snd_4265_, v_a_4222_);
lean_dec_ref(v___x_4260_);
lean_dec(v_fst_4264_);
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4320_; 
v_a_4272_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4274_ = v___x_4271_;
v_isShared_4275_ = v_isSharedCheck_4320_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4271_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4320_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v_fst_4276_; lean_object* v_snd_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4319_; 
v_fst_4276_ = lean_ctor_get(v_a_4272_, 0);
v_snd_4277_ = lean_ctor_get(v_a_4272_, 1);
v_isSharedCheck_4319_ = !lean_is_exclusive(v_a_4272_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4279_ = v_a_4272_;
v_isShared_4280_ = v_isSharedCheck_4319_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_snd_4277_);
lean_inc(v_fst_4276_);
lean_dec(v_a_4272_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4319_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v_packages_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4286_; 
v_packages_4281_ = lean_ctor_get(v_fst_4276_, 4);
v___x_4282_ = lean_array_get_size(v_packages_4281_);
v___x_4283_ = lean_array_fget(v_packages_4281_, v___x_4254_);
v___x_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4270_);
if (v_isShared_4268_ == 0)
{
lean_ctor_set(v___x_4267_, 1, v___x_4282_);
lean_ctor_set(v___x_4267_, 0, v___x_4284_);
v___x_4286_ = v___x_4267_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4318_, 1, v___x_4282_);
v___x_4286_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; uint8_t v___x_4289_; 
v___x_4287_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4286_, v___x_4261_);
v___x_4288_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4276_, v___x_4283_, v___x_4287_);
v___x_4289_ = lean_nat_dec_eq(v___x_4270_, v___x_4282_);
if (v___x_4289_ == 0)
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
lean_del_object(v___x_4279_);
lean_del_object(v___x_4274_);
v___x_4290_ = lean_unsigned_to_nat(1u);
v___x_4291_ = lean_nat_add(v___x_4270_, v___x_4290_);
v___x_4292_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4220_, v___x_4228_, v___x_4288_, v___x_4270_, v___x_4291_, v_snd_4277_, v_a_4222_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4310_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4295_ = v___x_4292_;
v_isShared_4296_ = v_isSharedCheck_4310_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4292_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4310_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v_fst_4297_; lean_object* v_snd_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4309_; 
v_fst_4297_ = lean_ctor_get(v_a_4293_, 0);
v_snd_4298_ = lean_ctor_get(v_a_4293_, 1);
v_isSharedCheck_4309_ = !lean_is_exclusive(v_a_4293_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4300_ = v_a_4293_;
v_isShared_4301_ = v_isSharedCheck_4309_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_snd_4298_);
lean_inc(v_fst_4297_);
lean_dec(v_a_4293_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4309_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4302_; lean_object* v___x_4304_; 
v___x_4302_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4297_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v___x_4302_);
v___x_4304_ = v___x_4300_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4302_);
lean_ctor_set(v_reuseFailAlloc_4308_, 1, v_snd_4298_);
v___x_4304_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4306_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4304_);
v___x_4306_ = v___x_4295_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
}
else
{
return v___x_4292_;
}
}
else
{
lean_object* v___x_4311_; lean_object* v___x_4313_; 
lean_dec_ref(v_leanOpts_4220_);
v___x_4311_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4288_);
if (v_isShared_4280_ == 0)
{
lean_ctor_set(v___x_4279_, 0, v___x_4311_);
v___x_4313_ = v___x_4279_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4311_);
lean_ctor_set(v_reuseFailAlloc_4317_, 1, v_snd_4277_);
v___x_4313_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
lean_object* v___x_4315_; 
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 0, v___x_4313_);
v___x_4315_ = v___x_4274_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4313_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_del_object(v___x_4267_);
lean_dec_ref(v_leanOpts_4220_);
v_a_4321_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4271_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4271_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
lean_del_object(v___x_4267_);
lean_dec(v_snd_4265_);
lean_dec(v_fst_4264_);
lean_dec_ref(v___x_4260_);
lean_dec_ref(v_leanOpts_4220_);
lean_dec_ref(v_ws_4218_);
v_a_4329_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4269_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4269_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
else
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4345_; 
lean_dec_ref(v___x_4260_);
lean_dec_ref(v_leanOpts_4220_);
lean_dec_ref(v_ws_4218_);
v_a_4338_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4340_ = v___x_4262_;
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4262_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4343_; 
if (v_isShared_4341_ == 0)
{
v___x_4343_ = v___x_4340_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec_ref(v_leanOpts_4220_);
lean_dec_ref(v_ws_4218_);
v_a_4346_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4225_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4225_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4354_, lean_object* v_toUpdate_4355_, lean_object* v_leanOpts_4356_, lean_object* v_updateToolchain_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
uint8_t v_updateToolchain_boxed_4360_; lean_object* v_res_4361_; 
v_updateToolchain_boxed_4360_ = lean_unbox(v_updateToolchain_4357_);
v_res_4361_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4354_, v_toUpdate_4355_, v_leanOpts_4356_, v_updateToolchain_boxed_4360_, v_a_4358_);
lean_dec_ref(v_a_4358_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_leanOpts_4362_, uint8_t v_reconfigure_4363_, lean_object* v_ws_4364_, lean_object* v_i_4365_, lean_object* v_i__lt_4366_, lean_object* v_next_4367_, lean_object* v_lt__next_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4362_, v_reconfigure_4363_, v_ws_4364_, v_i_4365_, v_next_4367_, v___y_4369_, v___y_4370_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_leanOpts_4373_, lean_object* v_reconfigure_4374_, lean_object* v_ws_4375_, lean_object* v_i_4376_, lean_object* v_i__lt_4377_, lean_object* v_next_4378_, lean_object* v_lt__next_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
uint8_t v_reconfigure_boxed_4383_; lean_object* v_res_4384_; 
v_reconfigure_boxed_4383_ = lean_unbox(v_reconfigure_4374_);
v_res_4384_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4373_, v_reconfigure_boxed_4383_, v_ws_4375_, v_i_4376_, v_i__lt_4377_, v_next_4378_, v_lt__next_4379_, v___y_4380_, v___y_4381_);
lean_dec_ref(v___y_4381_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_00_u03b1_4385_, lean_object* v_00_u03b2_4386_, lean_object* v_n_4387_, lean_object* v_f_4388_, lean_object* v_xs_4389_, lean_object* v_k_4390_, lean_object* v_h_4391_, lean_object* v_acc_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4387_, v_f_4388_, v_xs_4389_, v_k_4390_, v_acc_4392_, v___y_4393_, v___y_4394_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_00_u03b1_4397_, lean_object* v_00_u03b2_4398_, lean_object* v_n_4399_, lean_object* v_f_4400_, lean_object* v_xs_4401_, lean_object* v_k_4402_, lean_object* v_h_4403_, lean_object* v_acc_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_00_u03b1_4397_, v_00_u03b2_4398_, v_n_4399_, v_f_4400_, v_xs_4401_, v_k_4402_, v_h_4403_, v_acc_4404_, v___y_4405_, v___y_4406_);
lean_dec_ref(v___y_4406_);
lean_dec_ref(v_xs_4401_);
lean_dec(v_n_4399_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_inst_4409_, lean_object* v_R_4410_, lean_object* v_a_4411_, lean_object* v_b_4412_){
_start:
{
lean_object* v___x_4413_; 
v___x_4413_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_a_4411_, v_b_4412_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_upperBound_4414_, lean_object* v_fst_4415_, lean_object* v___x_4416_, lean_object* v_leanOpts_4417_, lean_object* v_inst_4418_, lean_object* v_R_4419_, lean_object* v_a_4420_, lean_object* v_b_4421_, lean_object* v_c_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4414_, v_fst_4415_, v___x_4416_, v_leanOpts_4417_, v_a_4420_, v_b_4421_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_upperBound_4427_, lean_object* v_fst_4428_, lean_object* v___x_4429_, lean_object* v_leanOpts_4430_, lean_object* v_inst_4431_, lean_object* v_R_4432_, lean_object* v_a_4433_, lean_object* v_b_4434_, lean_object* v_c_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4427_, v_fst_4428_, v___x_4429_, v_leanOpts_4430_, v_inst_4431_, v_R_4432_, v_a_4433_, v_b_4434_, v_c_4435_, v___y_4436_, v___y_4437_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v___x_4429_);
lean_dec_ref(v_fst_4428_);
lean_dec(v_upperBound_4427_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_start_4440_, lean_object* v_pkg_4441_, lean_object* v_leanOpts_4442_, uint8_t v_reconfigure_4443_, lean_object* v_as_4444_, size_t v_i_4445_, size_t v_stop_4446_, lean_object* v_b_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; 
v___x_4451_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4441_, v_leanOpts_4442_, v_reconfigure_4443_, v_as_4444_, v_i_4445_, v_stop_4446_, v_b_4447_, v___y_4448_, v___y_4449_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_start_4452_, lean_object* v_pkg_4453_, lean_object* v_leanOpts_4454_, lean_object* v_reconfigure_4455_, lean_object* v_as_4456_, lean_object* v_i_4457_, lean_object* v_stop_4458_, lean_object* v_b_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
uint8_t v_reconfigure_boxed_4463_; size_t v_i_boxed_4464_; size_t v_stop_boxed_4465_; lean_object* v_res_4466_; 
v_reconfigure_boxed_4463_ = lean_unbox(v_reconfigure_4455_);
v_i_boxed_4464_ = lean_unbox_usize(v_i_4457_);
lean_dec(v_i_4457_);
v_stop_boxed_4465_ = lean_unbox_usize(v_stop_4458_);
lean_dec(v_stop_4458_);
v_res_4466_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_start_4452_, v_pkg_4453_, v_leanOpts_4454_, v_reconfigure_boxed_4463_, v_as_4456_, v_i_boxed_4464_, v_stop_boxed_4465_, v_b_4459_, v___y_4460_, v___y_4461_);
lean_dec_ref(v___y_4461_);
lean_dec_ref(v_as_4456_);
lean_dec(v_start_4452_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_4467_, lean_object* v_msg_4468_){
_start:
{
lean_object* v___x_4469_; 
v___x_4469_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v_msg_4468_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object* v_00_u03b2_4470_, lean_object* v_k_4471_, lean_object* v_v_4472_, lean_object* v_t_4473_){
_start:
{
lean_object* v___x_4474_; 
v___x_4474_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_4471_, v_v_4472_, v_t_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object* v_init_4475_, lean_object* v_t_4476_){
_start:
{
lean_object* v___x_4477_; 
v___x_4477_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_4475_, v_t_4476_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4478_, lean_object* v_as_4479_, size_t v_i_4480_, size_t v_stop_4481_, lean_object* v_b_4482_){
_start:
{
lean_object* v___y_4484_; uint8_t v___x_4488_; 
v___x_4488_ = lean_usize_dec_eq(v_i_4480_, v_stop_4481_);
if (v___x_4488_ == 0)
{
lean_object* v___x_4489_; lean_object* v_baseName_4490_; lean_object* v_relConfigFile_4491_; lean_object* v_relManifestFile_4492_; lean_object* v___x_4493_; 
v___x_4489_ = lean_array_uget_borrowed(v_as_4479_, v_i_4480_);
v_baseName_4490_ = lean_ctor_get(v___x_4489_, 1);
v_relConfigFile_4491_ = lean_ctor_get(v___x_4489_, 8);
v_relManifestFile_4492_ = lean_ctor_get(v___x_4489_, 9);
v___x_4493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4478_, v_baseName_4490_);
if (lean_obj_tag(v___x_4493_) == 0)
{
v___y_4484_ = v_b_4482_;
goto v___jp_4483_;
}
else
{
lean_object* v_val_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4515_; 
v_val_4494_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4496_ = v___x_4493_;
v_isShared_4497_ = v_isSharedCheck_4515_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_val_4494_);
lean_dec(v___x_4493_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4515_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v_name_4498_; lean_object* v_scope_4499_; uint8_t v_inherited_4500_; lean_object* v_src_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4512_; 
v_name_4498_ = lean_ctor_get(v_val_4494_, 0);
v_scope_4499_ = lean_ctor_get(v_val_4494_, 1);
v_inherited_4500_ = lean_ctor_get_uint8(v_val_4494_, sizeof(void*)*5);
v_src_4501_ = lean_ctor_get(v_val_4494_, 4);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_val_4494_);
if (v_isSharedCheck_4512_ == 0)
{
lean_object* v_unused_4513_; lean_object* v_unused_4514_; 
v_unused_4513_ = lean_ctor_get(v_val_4494_, 3);
lean_dec(v_unused_4513_);
v_unused_4514_ = lean_ctor_get(v_val_4494_, 2);
lean_dec(v_unused_4514_);
v___x_4503_ = v_val_4494_;
v_isShared_4504_ = v_isSharedCheck_4512_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_src_4501_);
lean_inc(v_scope_4499_);
lean_inc(v_name_4498_);
lean_dec(v_val_4494_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4512_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
lean_inc_ref(v_relManifestFile_4492_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v_relManifestFile_4492_);
v___x_4506_ = v___x_4496_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_relManifestFile_4492_);
v___x_4506_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
lean_object* v___x_4508_; 
lean_inc_ref(v_relConfigFile_4491_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 3, v___x_4506_);
lean_ctor_set(v___x_4503_, 2, v_relConfigFile_4491_);
v___x_4508_ = v___x_4503_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_name_4498_);
lean_ctor_set(v_reuseFailAlloc_4510_, 1, v_scope_4499_);
lean_ctor_set(v_reuseFailAlloc_4510_, 2, v_relConfigFile_4491_);
lean_ctor_set(v_reuseFailAlloc_4510_, 3, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4510_, 4, v_src_4501_);
lean_ctor_set_uint8(v_reuseFailAlloc_4510_, sizeof(void*)*5, v_inherited_4500_);
v___x_4508_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4509_; 
v___x_4509_ = lean_array_push(v_b_4482_, v___x_4508_);
v___y_4484_ = v___x_4509_;
goto v___jp_4483_;
}
}
}
}
}
}
else
{
return v_b_4482_;
}
v___jp_4483_:
{
size_t v___x_4485_; size_t v___x_4486_; 
v___x_4485_ = ((size_t)1ULL);
v___x_4486_ = lean_usize_add(v_i_4480_, v___x_4485_);
v_i_4480_ = v___x_4486_;
v_b_4482_ = v___y_4484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4516_, lean_object* v_as_4517_, lean_object* v_i_4518_, lean_object* v_stop_4519_, lean_object* v_b_4520_){
_start:
{
size_t v_i_boxed_4521_; size_t v_stop_boxed_4522_; lean_object* v_res_4523_; 
v_i_boxed_4521_ = lean_unbox_usize(v_i_4518_);
lean_dec(v_i_4518_);
v_stop_boxed_4522_ = lean_unbox_usize(v_stop_4519_);
lean_dec(v_stop_4519_);
v_res_4523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4516_, v_as_4517_, v_i_boxed_4521_, v_stop_boxed_4522_, v_b_4520_);
lean_dec_ref(v_as_4517_);
lean_dec(v_entries_4516_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4524_, lean_object* v_entries_4525_){
_start:
{
lean_object* v_packages_4527_; lean_object* v___y_4529_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; uint8_t v___x_4547_; 
v_packages_4527_ = lean_ctor_get(v_ws_4524_, 4);
v___x_4544_ = lean_unsigned_to_nat(0u);
v___x_4545_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4546_ = lean_array_get_size(v_packages_4527_);
v___x_4547_ = lean_nat_dec_lt(v___x_4544_, v___x_4546_);
if (v___x_4547_ == 0)
{
v___y_4529_ = v___x_4545_;
goto v___jp_4528_;
}
else
{
uint8_t v___x_4548_; 
v___x_4548_ = lean_nat_dec_le(v___x_4546_, v___x_4546_);
if (v___x_4548_ == 0)
{
if (v___x_4547_ == 0)
{
v___y_4529_ = v___x_4545_;
goto v___jp_4528_;
}
else
{
size_t v___x_4549_; size_t v___x_4550_; lean_object* v___x_4551_; 
v___x_4549_ = ((size_t)0ULL);
v___x_4550_ = lean_usize_of_nat(v___x_4546_);
v___x_4551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4525_, v_packages_4527_, v___x_4549_, v___x_4550_, v___x_4545_);
v___y_4529_ = v___x_4551_;
goto v___jp_4528_;
}
}
else
{
size_t v___x_4552_; size_t v___x_4553_; lean_object* v___x_4554_; 
v___x_4552_ = ((size_t)0ULL);
v___x_4553_ = lean_usize_of_nat(v___x_4546_);
v___x_4554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4525_, v_packages_4527_, v___x_4552_, v___x_4553_, v___x_4545_);
v___y_4529_ = v___x_4554_;
goto v___jp_4528_;
}
}
v___jp_4528_:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v_config_4532_; lean_object* v_baseName_4533_; lean_object* v_dir_4534_; lean_object* v_relManifestFile_4535_; lean_object* v_toWorkspaceConfig_4536_; uint8_t v_fixedToolchain_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v_manifest_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4530_ = lean_unsigned_to_nat(0u);
v___x_4531_ = lean_array_fget_borrowed(v_packages_4527_, v___x_4530_);
v_config_4532_ = lean_ctor_get(v___x_4531_, 6);
v_baseName_4533_ = lean_ctor_get(v___x_4531_, 1);
v_dir_4534_ = lean_ctor_get(v___x_4531_, 4);
v_relManifestFile_4535_ = lean_ctor_get(v___x_4531_, 9);
v_toWorkspaceConfig_4536_ = lean_ctor_get(v_config_4532_, 0);
v_fixedToolchain_4537_ = lean_ctor_get_uint8(v_config_4532_, sizeof(void*)*28 + 6);
v___x_4538_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4536_);
v___x_4539_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4536_);
v___x_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
lean_inc(v_baseName_4533_);
v_manifest_4541_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4541_, 0, v_baseName_4533_);
lean_ctor_set(v_manifest_4541_, 1, v___x_4538_);
lean_ctor_set(v_manifest_4541_, 2, v___x_4540_);
lean_ctor_set(v_manifest_4541_, 3, v___y_4529_);
lean_ctor_set_uint8(v_manifest_4541_, sizeof(void*)*4, v_fixedToolchain_4537_);
lean_inc_ref(v_relManifestFile_4535_);
lean_inc_ref(v_dir_4534_);
v___x_4542_ = l_Lake_joinRelative(v_dir_4534_, v_relManifestFile_4535_);
v___x_4543_ = l_Lake_Manifest_save(v_manifest_4541_, v___x_4542_);
lean_dec_ref(v___x_4542_);
return v___x_4543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4555_, lean_object* v_entries_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4555_, v_entries_4556_);
lean_dec(v_entries_4556_);
lean_dec_ref(v_ws_4555_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4559_, lean_object* v_as_4560_, size_t v_i_4561_, size_t v_stop_4562_, lean_object* v_b_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_a_4568_; lean_object* v___y_4573_; uint8_t v___x_4575_; 
v___x_4575_ = lean_usize_dec_eq(v_i_4561_, v_stop_4562_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_6568__overap_4578_; lean_object* v___x_4579_; 
v___x_4576_ = lean_unsigned_to_nat(0u);
v___x_4577_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_6568__overap_4578_ = lean_array_uget_borrowed(v_as_4560_, v_i_4561_);
lean_inc(v___x_6568__overap_4578_);
lean_inc(v___y_4564_);
lean_inc_ref(v_pkg_4559_);
v___x_4579_ = lean_apply_4(v___x_6568__overap_4578_, v_pkg_4559_, v___y_4564_, v___x_4577_, lean_box(0));
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v_a_4581_; lean_object* v___x_4582_; uint8_t v___x_4583_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
v_a_4581_ = lean_ctor_get(v___x_4579_, 1);
lean_inc(v_a_4581_);
lean_dec_ref_known(v___x_4579_, 2);
v___x_4582_ = lean_array_get_size(v_a_4581_);
v___x_4583_ = lean_nat_dec_lt(v___x_4576_, v___x_4582_);
if (v___x_4583_ == 0)
{
lean_dec(v_a_4581_);
v_a_4568_ = v_a_4580_;
goto v___jp_4567_;
}
else
{
lean_object* v___x_4584_; size_t v___x_4585_; size_t v___x_4586_; lean_object* v___x_4587_; 
v___x_4584_ = lean_box(0);
v___x_4585_ = ((size_t)0ULL);
v___x_4586_ = lean_usize_of_nat(v___x_4582_);
v___x_4587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4581_, v___x_4585_, v___x_4586_, v___x_4584_, v___y_4565_);
lean_dec(v_a_4581_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_dec_ref_known(v___x_4587_, 1);
v_a_4568_ = v_a_4580_;
goto v___jp_4567_;
}
else
{
lean_dec(v_a_4580_);
v___y_4573_ = v___x_4587_;
goto v___jp_4572_;
}
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4589_; uint8_t v___x_4590_; 
v_a_4588_ = lean_ctor_get(v___x_4579_, 1);
lean_inc(v_a_4588_);
lean_dec_ref_known(v___x_4579_, 2);
v___x_4589_ = lean_array_get_size(v_a_4588_);
v___x_4590_ = lean_nat_dec_lt(v___x_4576_, v___x_4589_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; lean_object* v___x_4592_; 
lean_dec(v_a_4588_);
lean_dec_ref(v_pkg_4559_);
v___x_4591_ = lean_box(0);
v___x_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4591_);
return v___x_4592_;
}
else
{
lean_object* v___x_4593_; size_t v___x_4594_; size_t v___x_4595_; lean_object* v___x_4596_; 
v___x_4593_ = lean_box(0);
v___x_4594_ = ((size_t)0ULL);
v___x_4595_ = lean_usize_of_nat(v___x_4589_);
v___x_4596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4588_, v___x_4594_, v___x_4595_, v___x_4593_, v___y_4565_);
lean_dec(v_a_4588_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
lean_dec_ref(v_pkg_4559_);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4603_ == 0)
{
lean_object* v_unused_4604_; 
v_unused_4604_ = lean_ctor_get(v___x_4596_, 0);
lean_dec(v_unused_4604_);
v___x_4598_ = v___x_4596_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_dec(v___x_4596_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
lean_ctor_set_tag(v___x_4598_, 1);
lean_ctor_set(v___x_4598_, 0, v___x_4593_);
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4593_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
else
{
v___y_4573_ = v___x_4596_;
goto v___jp_4572_;
}
}
}
}
else
{
lean_object* v___x_4605_; 
lean_dec_ref(v_pkg_4559_);
v___x_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4605_, 0, v_b_4563_);
return v___x_4605_;
}
v___jp_4567_:
{
size_t v___x_4569_; size_t v___x_4570_; 
v___x_4569_ = ((size_t)1ULL);
v___x_4570_ = lean_usize_add(v_i_4561_, v___x_4569_);
v_i_4561_ = v___x_4570_;
v_b_4563_ = v_a_4568_;
goto _start;
}
v___jp_4572_:
{
if (lean_obj_tag(v___y_4573_) == 0)
{
lean_object* v_a_4574_; 
v_a_4574_ = lean_ctor_get(v___y_4573_, 0);
lean_inc(v_a_4574_);
lean_dec_ref_known(v___y_4573_, 1);
v_a_4568_ = v_a_4574_;
goto v___jp_4567_;
}
else
{
lean_dec_ref(v_pkg_4559_);
return v___y_4573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4606_, lean_object* v_as_4607_, lean_object* v_i_4608_, lean_object* v_stop_4609_, lean_object* v_b_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
size_t v_i_boxed_4614_; size_t v_stop_boxed_4615_; lean_object* v_res_4616_; 
v_i_boxed_4614_ = lean_unbox_usize(v_i_4608_);
lean_dec(v_i_4608_);
v_stop_boxed_4615_ = lean_unbox_usize(v_stop_4609_);
lean_dec(v_stop_4609_);
v_res_4616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4606_, v_as_4607_, v_i_boxed_4614_, v_stop_boxed_4615_, v_b_4610_, v___y_4611_, v___y_4612_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v_as_4607_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_){
_start:
{
lean_object* v_baseName_4622_; lean_object* v_postUpdateHooks_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; uint8_t v___x_4626_; 
v_baseName_4622_ = lean_ctor_get(v_pkg_4618_, 1);
v_postUpdateHooks_4623_ = lean_ctor_get(v_pkg_4618_, 20);
lean_inc_ref(v_postUpdateHooks_4623_);
v___x_4624_ = lean_array_get_size(v_postUpdateHooks_4623_);
v___x_4625_ = lean_unsigned_to_nat(0u);
v___x_4626_ = lean_nat_dec_eq(v___x_4624_, v___x_4625_);
if (v___x_4626_ == 0)
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; uint8_t v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; 
lean_inc(v_baseName_4622_);
v___x_4627_ = l_Lean_Name_toString(v_baseName_4622_, v___x_4626_);
v___x_4628_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4629_ = lean_string_append(v___x_4627_, v___x_4628_);
v___x_4630_ = 1;
v___x_4631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4631_, 0, v___x_4629_);
lean_ctor_set_uint8(v___x_4631_, sizeof(void*)*1, v___x_4630_);
lean_inc_ref(v_a_4620_);
v___x_4632_ = lean_apply_2(v_a_4620_, v___x_4631_, lean_box(0));
v___x_4633_ = lean_box(0);
v___x_4634_ = lean_nat_dec_lt(v___x_4625_, v___x_4624_);
if (v___x_4634_ == 0)
{
lean_object* v___x_4635_; 
lean_dec_ref(v_postUpdateHooks_4623_);
lean_dec_ref(v_pkg_4618_);
v___x_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4633_);
return v___x_4635_;
}
else
{
uint8_t v___x_4636_; 
v___x_4636_ = lean_nat_dec_le(v___x_4624_, v___x_4624_);
if (v___x_4636_ == 0)
{
if (v___x_4634_ == 0)
{
lean_object* v___x_4637_; 
lean_dec_ref(v_postUpdateHooks_4623_);
lean_dec_ref(v_pkg_4618_);
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4633_);
return v___x_4637_;
}
else
{
size_t v___x_4638_; size_t v___x_4639_; lean_object* v___x_4640_; 
v___x_4638_ = ((size_t)0ULL);
v___x_4639_ = lean_usize_of_nat(v___x_4624_);
v___x_4640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4618_, v_postUpdateHooks_4623_, v___x_4638_, v___x_4639_, v___x_4633_, v_a_4619_, v_a_4620_);
lean_dec_ref(v_postUpdateHooks_4623_);
return v___x_4640_;
}
}
else
{
size_t v___x_4641_; size_t v___x_4642_; lean_object* v___x_4643_; 
v___x_4641_ = ((size_t)0ULL);
v___x_4642_ = lean_usize_of_nat(v___x_4624_);
v___x_4643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4618_, v_postUpdateHooks_4623_, v___x_4641_, v___x_4642_, v___x_4633_, v_a_4619_, v_a_4620_);
lean_dec_ref(v_postUpdateHooks_4623_);
return v___x_4643_;
}
}
}
else
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
lean_dec_ref(v_postUpdateHooks_4623_);
lean_dec_ref(v_pkg_4618_);
v___x_4644_ = lean_box(0);
v___x_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
return v___x_4645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4646_, v_a_4647_, v_a_4648_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4651_, lean_object* v_ws_4652_, lean_object* v_toUpdate_4653_, lean_object* v_leanOpts_4654_, uint8_t v_updateToolchain_4655_){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_box(1);
v___x_4658_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4651_, v_ws_4652_, v_toUpdate_4653_, v___x_4657_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v_snd_4660_; uint8_t v___x_4661_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4659_);
lean_dec_ref_known(v___x_4658_, 1);
v_snd_4660_ = lean_ctor_get(v_a_4659_, 1);
lean_inc(v_snd_4660_);
lean_dec(v_a_4659_);
v___x_4661_ = 1;
if (v_updateToolchain_4655_ == 0)
{
lean_object* v_packages_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v_wsIdx_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v_packages_4662_ = lean_ctor_get(v_ws_4652_, 4);
v___x_4663_ = lean_unsigned_to_nat(0u);
v___x_4664_ = lean_array_fget_borrowed(v_packages_4662_, v___x_4663_);
v_wsIdx_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_wsIdx_4665_);
v___x_4666_ = lean_array_get_size(v_packages_4662_);
v___x_4667_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4654_, v___x_4661_, v_ws_4652_, v_wsIdx_4665_, v___x_4666_, v_snd_4660_, v_a_4651_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4685_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4670_ = v___x_4667_;
v_isShared_4671_ = v_isSharedCheck_4685_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4667_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4685_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v_fst_4672_; lean_object* v_snd_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4684_; 
v_fst_4672_ = lean_ctor_get(v_a_4668_, 0);
v_snd_4673_ = lean_ctor_get(v_a_4668_, 1);
v_isSharedCheck_4684_ = !lean_is_exclusive(v_a_4668_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4675_ = v_a_4668_;
v_isShared_4676_ = v_isSharedCheck_4684_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_snd_4673_);
lean_inc(v_fst_4672_);
lean_dec(v_a_4668_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4684_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; lean_object* v___x_4679_; 
v___x_4677_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4672_);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 0, v___x_4677_);
v___x_4679_ = v___x_4675_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4677_);
lean_ctor_set(v_reuseFailAlloc_4683_, 1, v_snd_4673_);
v___x_4679_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
lean_object* v___x_4681_; 
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 0, v___x_4679_);
v___x_4681_ = v___x_4670_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4679_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
}
}
else
{
return v___x_4667_;
}
}
else
{
lean_object* v_packages_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v_depConfigs_4689_; lean_object* v___x_4690_; lean_object* v___f_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v_packages_4686_ = lean_ctor_get(v_ws_4652_, 4);
v___x_4687_ = lean_unsigned_to_nat(0u);
v___x_4688_ = lean_array_fget_borrowed(v_packages_4686_, v___x_4687_);
v_depConfigs_4689_ = lean_ctor_get(v___x_4688_, 12);
v___x_4690_ = lean_box(v_updateToolchain_4655_);
lean_inc_ref(v_ws_4652_);
lean_inc(v___x_4688_);
v___f_4691_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4691_, 0, v___x_4688_);
lean_closure_set(v___f_4691_, 1, v___x_4690_);
lean_closure_set(v___f_4691_, 2, v_ws_4652_);
v___x_4692_ = lean_array_get_size(v_depConfigs_4689_);
lean_inc_ref(v_depConfigs_4689_);
v___x_4693_ = l_Array_reverse___redArg(v_depConfigs_4689_);
v___x_4694_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4695_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4692_, v___f_4691_, v___x_4693_, v___x_4687_, v___x_4694_, v_snd_4660_, v_a_4651_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; lean_object* v_fst_4697_; lean_object* v_snd_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4770_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4695_, 1);
v_fst_4697_ = lean_ctor_get(v_a_4696_, 0);
v_snd_4698_ = lean_ctor_get(v_a_4696_, 1);
v_isSharedCheck_4770_ = !lean_is_exclusive(v_a_4696_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4700_ = v_a_4696_;
v_isShared_4701_ = v_isSharedCheck_4770_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_snd_4698_);
lean_inc(v_fst_4697_);
lean_dec(v_a_4696_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4770_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4702_; 
lean_inc_ref(v_ws_4652_);
v___x_4702_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4651_, v_ws_4652_, v_fst_4697_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_object* v___x_4703_; lean_object* v___x_4704_; 
lean_dec_ref_known(v___x_4702_, 1);
v___x_4703_ = lean_array_get_size(v_packages_4686_);
lean_inc_ref(v_leanOpts_4654_);
v___x_4704_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4692_, v_fst_4697_, v___x_4693_, v_leanOpts_4654_, v___x_4687_, v_ws_4652_, v_snd_4698_, v_a_4651_);
lean_dec_ref(v___x_4693_);
lean_dec(v_fst_4697_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4753_; 
v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4707_ = v___x_4704_;
v_isShared_4708_ = v_isSharedCheck_4753_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4704_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4753_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v_fst_4709_; lean_object* v_snd_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4752_; 
v_fst_4709_ = lean_ctor_get(v_a_4705_, 0);
v_snd_4710_ = lean_ctor_get(v_a_4705_, 1);
v_isSharedCheck_4752_ = !lean_is_exclusive(v_a_4705_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4712_ = v_a_4705_;
v_isShared_4713_ = v_isSharedCheck_4752_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_snd_4710_);
lean_inc(v_fst_4709_);
lean_dec(v_a_4705_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4752_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v_packages_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4719_; 
v_packages_4714_ = lean_ctor_get(v_fst_4709_, 4);
v___x_4715_ = lean_array_get_size(v_packages_4714_);
v___x_4716_ = lean_array_fget(v_packages_4714_, v___x_4687_);
v___x_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4703_);
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 1, v___x_4715_);
lean_ctor_set(v___x_4700_, 0, v___x_4717_);
v___x_4719_ = v___x_4700_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4751_, 1, v___x_4715_);
v___x_4719_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; uint8_t v___x_4722_; 
v___x_4720_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4719_, v___x_4694_);
v___x_4721_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4709_, v___x_4716_, v___x_4720_);
v___x_4722_ = lean_nat_dec_eq(v___x_4703_, v___x_4715_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
lean_del_object(v___x_4712_);
lean_del_object(v___x_4707_);
v___x_4723_ = lean_unsigned_to_nat(1u);
v___x_4724_ = lean_nat_add(v___x_4703_, v___x_4723_);
v___x_4725_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4654_, v___x_4661_, v___x_4721_, v___x_4703_, v___x_4724_, v_snd_4710_, v_a_4651_);
if (lean_obj_tag(v___x_4725_) == 0)
{
lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4743_; 
v_a_4726_ = lean_ctor_get(v___x_4725_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4725_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4728_ = v___x_4725_;
v_isShared_4729_ = v_isSharedCheck_4743_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___x_4725_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4743_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v_fst_4730_; lean_object* v_snd_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4742_; 
v_fst_4730_ = lean_ctor_get(v_a_4726_, 0);
v_snd_4731_ = lean_ctor_get(v_a_4726_, 1);
v_isSharedCheck_4742_ = !lean_is_exclusive(v_a_4726_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4733_ = v_a_4726_;
v_isShared_4734_ = v_isSharedCheck_4742_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_snd_4731_);
lean_inc(v_fst_4730_);
lean_dec(v_a_4726_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4742_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4735_; lean_object* v___x_4737_; 
v___x_4735_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4730_);
if (v_isShared_4734_ == 0)
{
lean_ctor_set(v___x_4733_, 0, v___x_4735_);
v___x_4737_ = v___x_4733_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4735_);
lean_ctor_set(v_reuseFailAlloc_4741_, 1, v_snd_4731_);
v___x_4737_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
lean_object* v___x_4739_; 
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 0, v___x_4737_);
v___x_4739_ = v___x_4728_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v___x_4737_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
}
}
else
{
return v___x_4725_;
}
}
else
{
lean_object* v___x_4744_; lean_object* v___x_4746_; 
lean_dec_ref(v_leanOpts_4654_);
v___x_4744_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4721_);
if (v_isShared_4713_ == 0)
{
lean_ctor_set(v___x_4712_, 0, v___x_4744_);
v___x_4746_ = v___x_4712_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_snd_4710_);
v___x_4746_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
lean_object* v___x_4748_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 0, v___x_4746_);
v___x_4748_ = v___x_4707_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4746_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4761_; 
lean_del_object(v___x_4700_);
lean_dec_ref(v_leanOpts_4654_);
v_a_4754_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4756_ = v___x_4704_;
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4704_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4759_; 
if (v_isShared_4757_ == 0)
{
v___x_4759_ = v___x_4756_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4754_);
v___x_4759_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
return v___x_4759_;
}
}
}
}
else
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4769_; 
lean_del_object(v___x_4700_);
lean_dec(v_snd_4698_);
lean_dec(v_fst_4697_);
lean_dec_ref(v___x_4693_);
lean_dec_ref(v_leanOpts_4654_);
lean_dec_ref(v_ws_4652_);
v_a_4762_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4764_ = v___x_4702_;
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4702_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_dec_ref(v___x_4693_);
lean_dec_ref(v_leanOpts_4654_);
lean_dec_ref(v_ws_4652_);
v_a_4771_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4695_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4695_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
}
else
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4786_; 
lean_dec_ref(v_leanOpts_4654_);
lean_dec_ref(v_ws_4652_);
v_a_4779_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4781_ = v___x_4658_;
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4658_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4784_; 
if (v_isShared_4782_ == 0)
{
v___x_4784_ = v___x_4781_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4779_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4787_, lean_object* v_ws_4788_, lean_object* v_toUpdate_4789_, lean_object* v_leanOpts_4790_, lean_object* v_updateToolchain_4791_, lean_object* v_a_4792_){
_start:
{
uint8_t v_updateToolchain_boxed_4793_; lean_object* v_res_4794_; 
v_updateToolchain_boxed_4793_ = lean_unbox(v_updateToolchain_4791_);
v_res_4794_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4787_, v_ws_4788_, v_toUpdate_4789_, v_leanOpts_4790_, v_updateToolchain_boxed_4793_);
lean_dec_ref(v_a_4787_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4795_, size_t v_i_4796_, size_t v_stop_4797_, lean_object* v_b_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
uint8_t v___x_4802_; 
v___x_4802_ = lean_usize_dec_eq(v_i_4796_, v_stop_4797_);
if (v___x_4802_ == 0)
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = lean_array_uget_borrowed(v_as_4795_, v_i_4796_);
lean_inc(v___x_4803_);
v___x_4804_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4803_, v___y_4799_, v___y_4800_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; size_t v___x_4806_; size_t v___x_4807_; 
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc(v_a_4805_);
lean_dec_ref_known(v___x_4804_, 1);
v___x_4806_ = ((size_t)1ULL);
v___x_4807_ = lean_usize_add(v_i_4796_, v___x_4806_);
v_i_4796_ = v___x_4807_;
v_b_4798_ = v_a_4805_;
goto _start;
}
else
{
return v___x_4804_;
}
}
else
{
lean_object* v___x_4809_; 
v___x_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4809_, 0, v_b_4798_);
return v___x_4809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4810_, lean_object* v_i_4811_, lean_object* v_stop_4812_, lean_object* v_b_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
size_t v_i_boxed_4817_; size_t v_stop_boxed_4818_; lean_object* v_res_4819_; 
v_i_boxed_4817_ = lean_unbox_usize(v_i_4811_);
lean_dec(v_i_4811_);
v_stop_boxed_4818_ = lean_unbox_usize(v_stop_4812_);
lean_dec(v_stop_4812_);
v_res_4819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4810_, v_i_boxed_4817_, v_stop_boxed_4818_, v_b_4813_, v___y_4814_, v___y_4815_);
lean_dec_ref(v___y_4815_);
lean_dec(v___y_4814_);
lean_dec_ref(v_as_4810_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4820_, lean_object* v_toUpdate_4821_, lean_object* v_leanOpts_4822_, uint8_t v_updateToolchain_4823_, lean_object* v_a_4824_){
_start:
{
lean_object* v___x_4826_; 
v___x_4826_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4824_, v_ws_4820_, v_toUpdate_4821_, v_leanOpts_4822_, v_updateToolchain_4823_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_object* v_a_4827_; lean_object* v_fst_4828_; lean_object* v_snd_4829_; lean_object* v___y_4831_; lean_object* v___x_4848_; 
v_a_4827_ = lean_ctor_get(v___x_4826_, 0);
lean_inc(v_a_4827_);
lean_dec_ref_known(v___x_4826_, 1);
v_fst_4828_ = lean_ctor_get(v_a_4827_, 0);
lean_inc(v_fst_4828_);
v_snd_4829_ = lean_ctor_get(v_a_4827_, 1);
lean_inc(v_snd_4829_);
lean_dec(v_a_4827_);
v___x_4848_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4828_, v_snd_4829_);
lean_dec(v_snd_4829_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4870_; 
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4870_ == 0)
{
lean_object* v_unused_4871_; 
v_unused_4871_ = lean_ctor_get(v___x_4848_, 0);
lean_dec(v_unused_4871_);
v___x_4850_ = v___x_4848_;
v_isShared_4851_ = v_isSharedCheck_4870_;
goto v_resetjp_4849_;
}
else
{
lean_dec(v___x_4848_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4870_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v_packages_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; uint8_t v___x_4855_; 
v_packages_4852_ = lean_ctor_get(v_fst_4828_, 4);
v___x_4853_ = lean_unsigned_to_nat(0u);
v___x_4854_ = lean_array_get_size(v_packages_4852_);
v___x_4855_ = lean_nat_dec_lt(v___x_4853_, v___x_4854_);
if (v___x_4855_ == 0)
{
lean_object* v___x_4857_; 
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 0, v_fst_4828_);
v___x_4857_ = v___x_4850_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_fst_4828_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
else
{
lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4859_ = lean_box(0);
v___x_4860_ = lean_nat_dec_le(v___x_4854_, v___x_4854_);
if (v___x_4860_ == 0)
{
if (v___x_4855_ == 0)
{
lean_object* v___x_4862_; 
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 0, v_fst_4828_);
v___x_4862_ = v___x_4850_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_fst_4828_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
else
{
size_t v___x_4864_; size_t v___x_4865_; lean_object* v___x_4866_; 
lean_del_object(v___x_4850_);
v___x_4864_ = ((size_t)0ULL);
v___x_4865_ = lean_usize_of_nat(v___x_4854_);
v___x_4866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4852_, v___x_4864_, v___x_4865_, v___x_4859_, v_fst_4828_, v_a_4824_);
v___y_4831_ = v___x_4866_;
goto v___jp_4830_;
}
}
else
{
size_t v___x_4867_; size_t v___x_4868_; lean_object* v___x_4869_; 
lean_del_object(v___x_4850_);
v___x_4867_ = ((size_t)0ULL);
v___x_4868_ = lean_usize_of_nat(v___x_4854_);
v___x_4869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4852_, v___x_4867_, v___x_4868_, v___x_4859_, v_fst_4828_, v_a_4824_);
v___y_4831_ = v___x_4869_;
goto v___jp_4830_;
}
}
}
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4884_; 
lean_dec(v_fst_4828_);
v_a_4872_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4874_ = v___x_4848_;
v_isShared_4875_ = v_isSharedCheck_4884_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4848_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4884_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4876_; uint8_t v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4876_ = lean_io_error_to_string(v_a_4872_);
v___x_4877_ = 3;
v___x_4878_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4878_, 0, v___x_4876_);
lean_ctor_set_uint8(v___x_4878_, sizeof(void*)*1, v___x_4877_);
lean_inc_ref(v_a_4824_);
v___x_4879_ = lean_apply_2(v_a_4824_, v___x_4878_, lean_box(0));
v___x_4880_ = lean_box(0);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 0, v___x_4880_);
v___x_4882_ = v___x_4874_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
v___jp_4830_:
{
if (lean_obj_tag(v___y_4831_) == 0)
{
lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
v_isSharedCheck_4838_ = !lean_is_exclusive(v___y_4831_);
if (v_isSharedCheck_4838_ == 0)
{
lean_object* v_unused_4839_; 
v_unused_4839_ = lean_ctor_get(v___y_4831_, 0);
lean_dec(v_unused_4839_);
v___x_4833_ = v___y_4831_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_dec(v___y_4831_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 0, v_fst_4828_);
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_fst_4828_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
else
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4847_; 
lean_dec(v_fst_4828_);
v_a_4840_ = lean_ctor_get(v___y_4831_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___y_4831_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___y_4831_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___y_4831_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4845_; 
if (v_isShared_4843_ == 0)
{
v___x_4845_ = v___x_4842_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_a_4840_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
v_a_4885_ = lean_ctor_get(v___x_4826_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4826_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4826_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4826_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4893_, lean_object* v_toUpdate_4894_, lean_object* v_leanOpts_4895_, lean_object* v_updateToolchain_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_){
_start:
{
uint8_t v_updateToolchain_boxed_4899_; lean_object* v_res_4900_; 
v_updateToolchain_boxed_4899_ = lean_unbox(v_updateToolchain_4896_);
v_res_4900_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4893_, v_toUpdate_4894_, v_leanOpts_4895_, v_updateToolchain_boxed_4899_, v_a_4897_);
lean_dec_ref(v_a_4897_);
return v_res_4900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_4905_, lean_object* v_what_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v_name_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; uint8_t v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; uint8_t v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; 
v_name_4909_ = lean_ctor_get(v___x_4905_, 0);
lean_inc(v_name_4909_);
lean_dec_ref(v___x_4905_);
v___x_4910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_4911_ = lean_string_append(v___x_4910_, v_what_4906_);
v___x_4912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_4913_ = lean_string_append(v___x_4911_, v___x_4912_);
v___x_4914_ = 1;
v___x_4915_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4909_, v___x_4914_);
v___x_4916_ = lean_string_append(v___x_4913_, v___x_4915_);
v___x_4917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_4918_ = lean_string_append(v___x_4916_, v___x_4917_);
v___x_4919_ = lean_string_append(v___x_4918_, v___x_4915_);
lean_dec_ref(v___x_4915_);
v___x_4920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_4921_ = lean_string_append(v___x_4919_, v___x_4920_);
v___x_4922_ = 2;
v___x_4923_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4923_, 0, v___x_4921_);
lean_ctor_set_uint8(v___x_4923_, sizeof(void*)*1, v___x_4922_);
lean_inc_ref(v___y_4907_);
v___x_4924_ = lean_apply_2(v___y_4907_, v___x_4923_, lean_box(0));
v___x_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4924_);
return v___x_4925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_4926_, lean_object* v_what_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4926_, v_what_4927_, v___y_4928_);
lean_dec_ref(v___y_4928_);
lean_dec_ref(v_what_4927_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_4934_, lean_object* v_as_4935_, size_t v_i_4936_, size_t v_stop_4937_, lean_object* v_b_4938_, lean_object* v___y_4939_){
_start:
{
lean_object* v_a_4942_; lean_object* v___y_4947_; uint8_t v___x_4949_; 
v___x_4949_ = lean_usize_dec_eq(v_i_4936_, v_stop_4937_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4950_; lean_object* v_src_x3f_4951_; 
v___x_4950_ = lean_array_uget_borrowed(v_as_4935_, v_i_4936_);
v_src_x3f_4951_ = lean_ctor_get(v___x_4950_, 3);
if (lean_obj_tag(v_src_x3f_4951_) == 1)
{
lean_object* v_name_4952_; lean_object* v_val_4953_; lean_object* v___x_4954_; 
v_name_4952_ = lean_ctor_get(v___x_4950_, 0);
v_val_4953_ = lean_ctor_get(v_src_x3f_4951_, 0);
v___x_4954_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_4934_, v_name_4952_);
if (lean_obj_tag(v___x_4954_) == 1)
{
lean_object* v_val_4955_; lean_object* v___y_4957_; lean_object* v___y_4961_; 
v_val_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_val_4955_);
lean_dec_ref_known(v___x_4954_, 1);
if (lean_obj_tag(v_val_4953_) == 0)
{
lean_object* v_src_4964_; 
v_src_4964_ = lean_ctor_get(v_val_4955_, 4);
lean_inc_ref(v_src_4964_);
lean_dec(v_val_4955_);
if (lean_obj_tag(v_src_4964_) == 0)
{
lean_object* v___x_4965_; 
lean_dec_ref_known(v_src_4964_, 1);
v___x_4965_ = lean_box(0);
v_a_4942_ = v___x_4965_;
goto v___jp_4941_;
}
else
{
lean_dec_ref(v_src_4964_);
v___y_4961_ = v___y_4939_;
goto v___jp_4960_;
}
}
else
{
lean_object* v_src_4966_; 
v_src_4966_ = lean_ctor_get(v_val_4955_, 4);
lean_inc_ref(v_src_4966_);
lean_dec(v_val_4955_);
if (lean_obj_tag(v_src_4966_) == 1)
{
lean_object* v_url_4967_; lean_object* v_rev_4968_; lean_object* v_url_4969_; lean_object* v_inputRev_x3f_4970_; lean_object* v___y_4972_; uint8_t v___x_4979_; 
v_url_4967_ = lean_ctor_get(v_val_4953_, 0);
v_rev_4968_ = lean_ctor_get(v_val_4953_, 1);
v_url_4969_ = lean_ctor_get(v_src_4966_, 0);
lean_inc_ref(v_url_4969_);
v_inputRev_x3f_4970_ = lean_ctor_get(v_src_4966_, 2);
lean_inc(v_inputRev_x3f_4970_);
lean_dec_ref_known(v_src_4966_, 4);
v___x_4979_ = lean_string_dec_eq(v_url_4967_, v_url_4969_);
lean_dec_ref(v_url_4969_);
if (v___x_4979_ == 0)
{
goto v___jp_4976_;
}
else
{
if (v___x_4949_ == 0)
{
v___y_4972_ = v___y_4939_;
goto v___jp_4971_;
}
else
{
goto v___jp_4976_;
}
}
v___jp_4971_:
{
lean_object* v___x_4973_; uint8_t v___x_4974_; 
v___x_4973_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_4968_);
v___x_4974_ = l_Option_instDecidableEq___redArg(v___x_4973_, v_rev_4968_, v_inputRev_x3f_4970_);
if (v___x_4974_ == 0)
{
v___y_4957_ = v___y_4972_;
goto v___jp_4956_;
}
else
{
if (v___x_4949_ == 0)
{
lean_object* v___x_4975_; 
v___x_4975_ = lean_box(0);
v_a_4942_ = v___x_4975_;
goto v___jp_4941_;
}
else
{
v___y_4957_ = v___y_4972_;
goto v___jp_4956_;
}
}
}
v___jp_4976_:
{
lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_4950_);
v___x_4978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4950_, v___x_4977_, v___y_4939_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_dec_ref_known(v___x_4978_, 1);
v___y_4972_ = v___y_4939_;
goto v___jp_4971_;
}
else
{
lean_dec(v_inputRev_x3f_4970_);
return v___x_4978_;
}
}
}
else
{
lean_dec_ref(v_src_4966_);
v___y_4961_ = v___y_4939_;
goto v___jp_4960_;
}
}
v___jp_4956_:
{
lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_4950_);
v___x_4959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4950_, v___x_4958_, v___y_4957_);
v___y_4947_ = v___x_4959_;
goto v___jp_4946_;
}
v___jp_4960_:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_4950_);
v___x_4963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4950_, v___x_4962_, v___y_4961_);
v___y_4947_ = v___x_4963_;
goto v___jp_4946_;
}
}
else
{
lean_object* v___x_4980_; 
lean_dec(v___x_4954_);
v___x_4980_ = lean_box(0);
v_a_4942_ = v___x_4980_;
goto v___jp_4941_;
}
}
else
{
lean_object* v___x_4981_; 
v___x_4981_ = lean_box(0);
v_a_4942_ = v___x_4981_;
goto v___jp_4941_;
}
}
else
{
lean_object* v___x_4982_; 
v___x_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4982_, 0, v_b_4938_);
return v___x_4982_;
}
v___jp_4941_:
{
size_t v___x_4943_; size_t v___x_4944_; 
v___x_4943_ = ((size_t)1ULL);
v___x_4944_ = lean_usize_add(v_i_4936_, v___x_4943_);
v_i_4936_ = v___x_4944_;
v_b_4938_ = v_a_4942_;
goto _start;
}
v___jp_4946_:
{
if (lean_obj_tag(v___y_4947_) == 0)
{
lean_object* v_a_4948_; 
v_a_4948_ = lean_ctor_get(v___y_4947_, 0);
lean_inc(v_a_4948_);
lean_dec_ref_known(v___y_4947_, 1);
v_a_4942_ = v_a_4948_;
goto v___jp_4941_;
}
else
{
return v___y_4947_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_4983_, lean_object* v_as_4984_, lean_object* v_i_4985_, lean_object* v_stop_4986_, lean_object* v_b_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
size_t v_i_boxed_4990_; size_t v_stop_boxed_4991_; lean_object* v_res_4992_; 
v_i_boxed_4990_ = lean_unbox_usize(v_i_4985_);
lean_dec(v_i_4985_);
v_stop_boxed_4991_ = lean_unbox_usize(v_stop_4986_);
lean_dec(v_stop_4986_);
v_res_4992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4983_, v_as_4984_, v_i_boxed_4990_, v_stop_boxed_4991_, v_b_4987_, v___y_4988_);
lean_dec_ref(v___y_4988_);
lean_dec_ref(v_as_4984_);
lean_dec(v_pkgEntries_4983_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_4993_, lean_object* v_deps_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; uint8_t v___x_5000_; 
v___x_4997_ = lean_unsigned_to_nat(0u);
v___x_4998_ = lean_array_get_size(v_deps_4994_);
v___x_4999_ = lean_box(0);
v___x_5000_ = lean_nat_dec_lt(v___x_4997_, v___x_4998_);
if (v___x_5000_ == 0)
{
lean_object* v___x_5001_; 
v___x_5001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5001_, 0, v___x_4999_);
return v___x_5001_;
}
else
{
uint8_t v___x_5002_; 
v___x_5002_ = lean_nat_dec_le(v___x_4998_, v___x_4998_);
if (v___x_5002_ == 0)
{
if (v___x_5000_ == 0)
{
lean_object* v___x_5003_; 
v___x_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5003_, 0, v___x_4999_);
return v___x_5003_;
}
else
{
size_t v___x_5004_; size_t v___x_5005_; lean_object* v___x_5006_; 
v___x_5004_ = ((size_t)0ULL);
v___x_5005_ = lean_usize_of_nat(v___x_4998_);
v___x_5006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4993_, v_deps_4994_, v___x_5004_, v___x_5005_, v___x_4999_, v_a_4995_);
return v___x_5006_;
}
}
else
{
size_t v___x_5007_; size_t v___x_5008_; lean_object* v___x_5009_; 
v___x_5007_ = ((size_t)0ULL);
v___x_5008_ = lean_usize_of_nat(v___x_4998_);
v___x_5009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4993_, v_deps_4994_, v___x_5007_, v___x_5008_, v___x_4999_, v_a_4995_);
return v___x_5009_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_5010_, lean_object* v_deps_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_5010_, v_deps_5011_, v_a_5012_);
lean_dec_ref(v_a_5012_);
lean_dec_ref(v_deps_5011_);
lean_dec(v_pkgEntries_5010_);
return v_res_5014_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_5015_, lean_object* v_x_5016_){
_start:
{
if (lean_obj_tag(v_x_5015_) == 0)
{
if (lean_obj_tag(v_x_5016_) == 0)
{
uint8_t v___x_5017_; 
v___x_5017_ = 1;
return v___x_5017_;
}
else
{
uint8_t v___x_5018_; 
v___x_5018_ = 0;
return v___x_5018_;
}
}
else
{
if (lean_obj_tag(v_x_5016_) == 0)
{
uint8_t v___x_5019_; 
v___x_5019_ = 0;
return v___x_5019_;
}
else
{
lean_object* v_val_5020_; lean_object* v_val_5021_; uint8_t v___x_5022_; 
v_val_5020_ = lean_ctor_get(v_x_5015_, 0);
v_val_5021_ = lean_ctor_get(v_x_5016_, 0);
v___x_5022_ = lean_string_dec_eq(v_val_5020_, v_val_5021_);
return v___x_5022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_5023_, lean_object* v_x_5024_){
_start:
{
uint8_t v_res_5025_; lean_object* v_r_5026_; 
v_res_5025_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_5023_, v_x_5024_);
lean_dec(v_x_5024_);
lean_dec(v_x_5023_);
v_r_5026_ = lean_box(v_res_5025_);
return v_r_5026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_pkg_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v_leanOpts_5035_, uint8_t v_reconfigure_5036_, lean_object* v_as_5037_, size_t v_i_5038_, size_t v_stop_5039_, lean_object* v_b_5040_, lean_object* v___y_5041_){
_start:
{
uint8_t v___x_5043_; 
v___x_5043_ = lean_usize_dec_eq(v_i_5038_, v_stop_5039_);
if (v___x_5043_ == 0)
{
lean_object* v_ws_5044_; lean_object* v_depIdxs_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5175_; 
v_ws_5044_ = lean_ctor_get(v_b_5040_, 0);
v_depIdxs_5045_ = lean_ctor_get(v_b_5040_, 1);
v_isSharedCheck_5175_ = !lean_is_exclusive(v_b_5040_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5047_ = v_b_5040_;
v_isShared_5048_ = v_isSharedCheck_5175_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_depIdxs_5045_);
lean_inc(v_ws_5044_);
lean_dec(v_b_5040_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5175_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v_lakeEnv_5049_; lean_object* v_packages_5050_; size_t v___x_5051_; size_t v___x_5052_; lean_object* v___x_5053_; lean_object* v___f_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v_lakeEnv_5049_ = lean_ctor_get(v_ws_5044_, 0);
v_packages_5050_ = lean_ctor_get(v_ws_5044_, 4);
v___x_5051_ = ((size_t)1ULL);
v___x_5052_ = lean_usize_sub(v_i_5038_, v___x_5051_);
v___x_5053_ = lean_array_uget_borrowed(v_as_5037_, v___x_5052_);
lean_inc(v___x_5053_);
v___f_5054_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5054_, 0, v___x_5053_);
v___x_5055_ = lean_unsigned_to_nat(0u);
v___x_5056_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5054_, v_packages_5050_, v___x_5055_);
if (lean_obj_tag(v___x_5056_) == 1)
{
lean_object* v_val_5057_; lean_object* v___x_5058_; lean_object* v___x_5060_; 
v_val_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_val_5057_);
lean_dec_ref_known(v___x_5056_, 1);
v___x_5058_ = lean_array_push(v_depIdxs_5045_, v_val_5057_);
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 1, v___x_5058_);
v___x_5060_ = v___x_5047_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_ws_5044_);
lean_ctor_set(v_reuseFailAlloc_5062_, 1, v___x_5058_);
v___x_5060_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
v_i_5038_ = v___x_5052_;
v_b_5040_ = v___x_5060_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_5063_; lean_object* v_baseName_5064_; lean_object* v_name_5065_; lean_object* v_opts_5066_; uint8_t v___x_5067_; 
lean_dec(v___x_5056_);
v_wsIdx_5063_ = lean_ctor_get(v_pkg_5032_, 0);
v_baseName_5064_ = lean_ctor_get(v_pkg_5032_, 1);
v_name_5065_ = lean_ctor_get(v___x_5053_, 0);
v_opts_5066_ = lean_ctor_get(v___x_5053_, 4);
v___x_5067_ = lean_name_eq(v_baseName_5064_, v_name_5065_);
if (v___x_5067_ == 0)
{
lean_object* v___x_5068_; 
v___x_5068_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5033_, v_name_5065_);
if (lean_obj_tag(v___x_5068_) == 1)
{
lean_object* v_val_5069_; lean_object* v___x_5070_; lean_object* v_dir_5071_; lean_object* v___x_5072_; 
v_val_5069_ = lean_ctor_get(v___x_5068_, 0);
lean_inc(v_val_5069_);
lean_dec_ref_known(v___x_5068_, 1);
v___x_5070_ = lean_array_fget_borrowed(v_packages_5050_, v___x_5055_);
v_dir_5071_ = lean_ctor_get(v___x_5070_, 4);
lean_inc_ref(v___y_5034_);
lean_inc_ref(v_dir_5071_);
v___x_5072_ = l_Lake_PackageEntry_materialize(v_val_5069_, v_lakeEnv_5049_, v_dir_5071_, v___y_5034_, v___y_5041_);
if (lean_obj_tag(v___x_5072_) == 0)
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5129_; 
v_a_5073_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5075_ = v___x_5072_;
v_isShared_5076_ = v_isSharedCheck_5129_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5072_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5129_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5077_; lean_object* v_wsIdx_5078_; lean_object* v___x_5079_; 
v___x_5077_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_5078_ = lean_array_get_size(v_packages_5050_);
lean_inc_ref(v_leanOpts_5035_);
lean_inc(v_opts_5066_);
v___x_5079_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5044_, v_a_5073_, v_opts_5066_, v_leanOpts_5035_, v_reconfigure_5036_, v___x_5077_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v_a_5081_; lean_object* v___x_5082_; lean_object* v___x_5084_; 
lean_del_object(v___x_5075_);
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
v_a_5081_ = lean_ctor_get(v___x_5079_, 1);
lean_inc(v_a_5081_);
lean_dec_ref_known(v___x_5079_, 2);
v___x_5082_ = lean_array_push(v_depIdxs_5045_, v_wsIdx_5078_);
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 1, v___x_5082_);
lean_ctor_set(v___x_5047_, 0, v_a_5080_);
v___x_5084_ = v___x_5047_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5080_);
lean_ctor_set(v_reuseFailAlloc_5101_, 1, v___x_5082_);
v___x_5084_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
lean_object* v___x_5085_; uint8_t v___x_5086_; 
v___x_5085_ = lean_array_get_size(v_a_5081_);
v___x_5086_ = lean_nat_dec_lt(v___x_5055_, v___x_5085_);
if (v___x_5086_ == 0)
{
lean_dec(v_a_5081_);
v_i_5038_ = v___x_5052_;
v_b_5040_ = v___x_5084_;
goto _start;
}
else
{
lean_object* v___x_5088_; size_t v___x_5089_; size_t v___x_5090_; lean_object* v___x_5091_; 
v___x_5088_ = lean_box(0);
v___x_5089_ = ((size_t)0ULL);
v___x_5090_ = lean_usize_of_nat(v___x_5085_);
v___x_5091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5081_, v___x_5089_, v___x_5090_, v___x_5088_, v___y_5041_);
lean_dec(v_a_5081_);
if (lean_obj_tag(v___x_5091_) == 0)
{
lean_dec_ref_known(v___x_5091_, 1);
v_i_5038_ = v___x_5052_;
v_b_5040_ = v___x_5084_;
goto _start;
}
else
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
lean_dec_ref(v___x_5084_);
lean_dec_ref(v_leanOpts_5035_);
lean_dec_ref(v___y_5034_);
lean_dec_ref(v_pkg_5032_);
v_a_5093_ = lean_ctor_get(v___x_5091_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5091_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5091_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5091_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
}
}
else
{
lean_object* v_a_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; 
lean_del_object(v___x_5047_);
lean_dec_ref(v_depIdxs_5045_);
lean_dec_ref(v_leanOpts_5035_);
lean_dec_ref(v___y_5034_);
lean_dec_ref(v_pkg_5032_);
v_a_5102_ = lean_ctor_get(v___x_5079_, 1);
lean_inc(v_a_5102_);
lean_dec_ref_known(v___x_5079_, 2);
v___x_5103_ = lean_array_get_size(v_a_5102_);
v___x_5104_ = lean_nat_dec_lt(v___x_5055_, v___x_5103_);
if (v___x_5104_ == 0)
{
lean_object* v___x_5105_; lean_object* v___x_5107_; 
lean_dec(v_a_5102_);
v___x_5105_ = lean_box(0);
if (v_isShared_5076_ == 0)
{
lean_ctor_set_tag(v___x_5075_, 1);
lean_ctor_set(v___x_5075_, 0, v___x_5105_);
v___x_5107_ = v___x_5075_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5105_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
return v___x_5107_;
}
}
else
{
lean_object* v___x_5109_; size_t v___x_5110_; size_t v___x_5111_; lean_object* v___x_5112_; 
lean_del_object(v___x_5075_);
v___x_5109_ = lean_box(0);
v___x_5110_ = ((size_t)0ULL);
v___x_5111_ = lean_usize_of_nat(v___x_5103_);
v___x_5112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5102_, v___x_5110_, v___x_5111_, v___x_5109_, v___y_5041_);
lean_dec(v_a_5102_);
if (lean_obj_tag(v___x_5112_) == 0)
{
lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5119_ == 0)
{
lean_object* v_unused_5120_; 
v_unused_5120_ = lean_ctor_get(v___x_5112_, 0);
lean_dec(v_unused_5120_);
v___x_5114_ = v___x_5112_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_dec(v___x_5112_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
lean_ctor_set_tag(v___x_5114_, 1);
lean_ctor_set(v___x_5114_, 0, v___x_5109_);
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5109_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
v_a_5121_ = lean_ctor_get(v___x_5112_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5112_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5112_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5137_; 
lean_del_object(v___x_5047_);
lean_dec_ref(v_depIdxs_5045_);
lean_dec_ref(v_ws_5044_);
lean_dec_ref(v_leanOpts_5035_);
lean_dec_ref(v___y_5034_);
lean_dec_ref(v_pkg_5032_);
v_a_5130_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5132_ = v___x_5072_;
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5072_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v___x_5135_; 
if (v_isShared_5133_ == 0)
{
v___x_5135_ = v___x_5132_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5130_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
}
else
{
uint8_t v___x_5138_; 
lean_inc(v_baseName_5064_);
lean_inc(v_wsIdx_5063_);
lean_dec(v___x_5068_);
lean_del_object(v___x_5047_);
lean_dec_ref(v_depIdxs_5045_);
lean_dec_ref(v_ws_5044_);
lean_dec_ref(v_leanOpts_5035_);
lean_dec_ref(v___y_5034_);
lean_dec_ref(v_pkg_5032_);
v___x_5138_ = lean_nat_dec_eq(v_wsIdx_5063_, v___x_5055_);
lean_dec(v_wsIdx_5063_);
if (v___x_5138_ == 0)
{
lean_object* v___x_5139_; uint8_t v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; uint8_t v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5140_ = 1;
lean_inc(v_name_5065_);
v___x_5141_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5065_, v___x_5140_);
v___x_5142_ = lean_string_append(v___x_5139_, v___x_5141_);
lean_dec_ref(v___x_5141_);
v___x_5143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5144_ = lean_string_append(v___x_5142_, v___x_5143_);
v___x_5145_ = l_Lean_Name_toString(v_baseName_5064_, v___x_5138_);
v___x_5146_ = lean_string_append(v___x_5144_, v___x_5145_);
lean_dec_ref(v___x_5145_);
v___x_5147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5148_ = lean_string_append(v___x_5146_, v___x_5147_);
v___x_5149_ = 3;
v___x_5150_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5150_, 0, v___x_5148_);
lean_ctor_set_uint8(v___x_5150_, sizeof(void*)*1, v___x_5149_);
lean_inc_ref(v___y_5041_);
v___x_5151_ = lean_apply_2(v___y_5041_, v___x_5150_, lean_box(0));
v___x_5152_ = lean_box(0);
v___x_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5153_, 0, v___x_5152_);
return v___x_5153_;
}
else
{
lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; uint8_t v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; 
lean_dec(v_baseName_5064_);
v___x_5154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5065_);
v___x_5155_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5065_, v___x_5138_);
v___x_5156_ = lean_string_append(v___x_5154_, v___x_5155_);
v___x_5157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5158_ = lean_string_append(v___x_5156_, v___x_5157_);
v___x_5159_ = lean_string_append(v___x_5158_, v___x_5155_);
lean_dec_ref(v___x_5155_);
v___x_5160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5161_ = lean_string_append(v___x_5159_, v___x_5160_);
v___x_5162_ = 3;
v___x_5163_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5163_, 0, v___x_5161_);
lean_ctor_set_uint8(v___x_5163_, sizeof(void*)*1, v___x_5162_);
lean_inc_ref(v___y_5041_);
v___x_5164_ = lean_apply_2(v___y_5041_, v___x_5163_, lean_box(0));
v___x_5165_ = lean_box(0);
v___x_5166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5166_, 0, v___x_5165_);
return v___x_5166_;
}
}
}
else
{
lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
lean_inc(v_baseName_5064_);
lean_del_object(v___x_5047_);
lean_dec_ref(v_depIdxs_5045_);
lean_dec_ref(v_ws_5044_);
lean_dec_ref(v_leanOpts_5035_);
lean_dec_ref(v___y_5034_);
lean_dec_ref(v_pkg_5032_);
v___x_5167_ = l_Lean_Name_toString(v_baseName_5064_, v___x_5043_);
v___x_5168_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5169_ = lean_string_append(v___x_5167_, v___x_5168_);
v___x_5170_ = 3;
v___x_5171_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5171_, 0, v___x_5169_);
lean_ctor_set_uint8(v___x_5171_, sizeof(void*)*1, v___x_5170_);
lean_inc_ref(v___y_5041_);
v___x_5172_ = lean_apply_2(v___y_5041_, v___x_5171_, lean_box(0));
v___x_5173_ = lean_box(0);
v___x_5174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5174_, 0, v___x_5173_);
return v___x_5174_;
}
}
}
}
else
{
lean_object* v___x_5176_; 
lean_dec_ref(v_leanOpts_5035_);
lean_dec_ref(v___y_5034_);
lean_dec_ref(v_pkg_5032_);
v___x_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5176_, 0, v_b_5040_);
return v___x_5176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_pkg_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v_leanOpts_5180_, lean_object* v_reconfigure_5181_, lean_object* v_as_5182_, lean_object* v_i_5183_, lean_object* v_stop_5184_, lean_object* v_b_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
uint8_t v_reconfigure_boxed_5188_; size_t v_i_boxed_5189_; size_t v_stop_boxed_5190_; lean_object* v_res_5191_; 
v_reconfigure_boxed_5188_ = lean_unbox(v_reconfigure_5181_);
v_i_boxed_5189_ = lean_unbox_usize(v_i_5183_);
lean_dec(v_i_5183_);
v_stop_boxed_5190_ = lean_unbox_usize(v_stop_5184_);
lean_dec(v_stop_5184_);
v_res_5191_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5177_, v___y_5178_, v___y_5179_, v_leanOpts_5180_, v_reconfigure_boxed_5188_, v_as_5182_, v_i_boxed_5189_, v_stop_boxed_5190_, v_b_5185_, v___y_5186_);
lean_dec_ref(v___y_5186_);
lean_dec_ref(v_as_5182_);
lean_dec(v___y_5178_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_start_5192_, lean_object* v_pkg_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v_leanOpts_5196_, uint8_t v_reconfigure_5197_, lean_object* v_as_5198_, size_t v_i_5199_, size_t v_stop_5200_, lean_object* v_b_5201_, lean_object* v___y_5202_){
_start:
{
uint8_t v___x_5204_; 
v___x_5204_ = lean_usize_dec_eq(v_i_5199_, v_stop_5200_);
if (v___x_5204_ == 0)
{
lean_object* v_ws_5205_; lean_object* v_depIdxs_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5336_; 
v_ws_5205_ = lean_ctor_get(v_b_5201_, 0);
v_depIdxs_5206_ = lean_ctor_get(v_b_5201_, 1);
v_isSharedCheck_5336_ = !lean_is_exclusive(v_b_5201_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5208_ = v_b_5201_;
v_isShared_5209_ = v_isSharedCheck_5336_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_depIdxs_5206_);
lean_inc(v_ws_5205_);
lean_dec(v_b_5201_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5336_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v_lakeEnv_5210_; lean_object* v_packages_5211_; size_t v___x_5212_; size_t v___x_5213_; lean_object* v___x_5214_; lean_object* v___f_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; 
v_lakeEnv_5210_ = lean_ctor_get(v_ws_5205_, 0);
v_packages_5211_ = lean_ctor_get(v_ws_5205_, 4);
v___x_5212_ = ((size_t)1ULL);
v___x_5213_ = lean_usize_sub(v_i_5199_, v___x_5212_);
v___x_5214_ = lean_array_uget_borrowed(v_as_5198_, v___x_5213_);
lean_inc(v___x_5214_);
v___f_5215_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5215_, 0, v___x_5214_);
v___x_5216_ = lean_unsigned_to_nat(0u);
v___x_5217_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5215_, v_packages_5211_, v___x_5216_);
if (lean_obj_tag(v___x_5217_) == 1)
{
lean_object* v_val_5218_; lean_object* v___x_5219_; lean_object* v___x_5221_; 
v_val_5218_ = lean_ctor_get(v___x_5217_, 0);
lean_inc(v_val_5218_);
lean_dec_ref_known(v___x_5217_, 1);
v___x_5219_ = lean_array_push(v_depIdxs_5206_, v_val_5218_);
if (v_isShared_5209_ == 0)
{
lean_ctor_set(v___x_5208_, 1, v___x_5219_);
v___x_5221_ = v___x_5208_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_ws_5205_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v___x_5219_);
v___x_5221_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
lean_object* v___x_5222_; 
v___x_5222_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5193_, v___y_5194_, v___y_5195_, v_leanOpts_5196_, v_reconfigure_5197_, v_as_5198_, v___x_5213_, v_stop_5200_, v___x_5221_, v___y_5202_);
return v___x_5222_;
}
}
else
{
lean_object* v_wsIdx_5224_; lean_object* v_baseName_5225_; lean_object* v_name_5226_; lean_object* v_opts_5227_; uint8_t v___x_5228_; 
lean_dec(v___x_5217_);
v_wsIdx_5224_ = lean_ctor_get(v_pkg_5193_, 0);
v_baseName_5225_ = lean_ctor_get(v_pkg_5193_, 1);
v_name_5226_ = lean_ctor_get(v___x_5214_, 0);
v_opts_5227_ = lean_ctor_get(v___x_5214_, 4);
v___x_5228_ = lean_name_eq(v_baseName_5225_, v_name_5226_);
if (v___x_5228_ == 0)
{
lean_object* v___x_5229_; 
v___x_5229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5194_, v_name_5226_);
if (lean_obj_tag(v___x_5229_) == 1)
{
lean_object* v_val_5230_; lean_object* v___x_5231_; lean_object* v_dir_5232_; lean_object* v___x_5233_; 
v_val_5230_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_val_5230_);
lean_dec_ref_known(v___x_5229_, 1);
v___x_5231_ = lean_array_fget_borrowed(v_packages_5211_, v___x_5216_);
v_dir_5232_ = lean_ctor_get(v___x_5231_, 4);
lean_inc_ref(v___y_5195_);
lean_inc_ref(v_dir_5232_);
v___x_5233_ = l_Lake_PackageEntry_materialize(v_val_5230_, v_lakeEnv_5210_, v_dir_5232_, v___y_5195_, v___y_5202_);
if (lean_obj_tag(v___x_5233_) == 0)
{
lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5290_; 
v_a_5234_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5290_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5290_ == 0)
{
v___x_5236_ = v___x_5233_;
v_isShared_5237_ = v_isSharedCheck_5290_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5233_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5290_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5238_; lean_object* v_wsIdx_5239_; lean_object* v___x_5240_; 
v___x_5238_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_5239_ = lean_array_get_size(v_packages_5211_);
lean_inc_ref(v_leanOpts_5196_);
lean_inc(v_opts_5227_);
v___x_5240_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5205_, v_a_5234_, v_opts_5227_, v_leanOpts_5196_, v_reconfigure_5197_, v___x_5238_);
if (lean_obj_tag(v___x_5240_) == 0)
{
lean_object* v_a_5241_; lean_object* v_a_5242_; lean_object* v___x_5243_; lean_object* v___x_5245_; 
lean_del_object(v___x_5236_);
v_a_5241_ = lean_ctor_get(v___x_5240_, 0);
lean_inc(v_a_5241_);
v_a_5242_ = lean_ctor_get(v___x_5240_, 1);
lean_inc(v_a_5242_);
lean_dec_ref_known(v___x_5240_, 2);
v___x_5243_ = lean_array_push(v_depIdxs_5206_, v_wsIdx_5239_);
if (v_isShared_5209_ == 0)
{
lean_ctor_set(v___x_5208_, 1, v___x_5243_);
lean_ctor_set(v___x_5208_, 0, v_a_5241_);
v___x_5245_ = v___x_5208_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5241_);
lean_ctor_set(v_reuseFailAlloc_5262_, 1, v___x_5243_);
v___x_5245_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
lean_object* v___x_5246_; uint8_t v___x_5247_; 
v___x_5246_ = lean_array_get_size(v_a_5242_);
v___x_5247_ = lean_nat_dec_lt(v___x_5216_, v___x_5246_);
if (v___x_5247_ == 0)
{
lean_object* v___x_5248_; 
lean_dec(v_a_5242_);
v___x_5248_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5193_, v___y_5194_, v___y_5195_, v_leanOpts_5196_, v_reconfigure_5197_, v_as_5198_, v___x_5213_, v_stop_5200_, v___x_5245_, v___y_5202_);
return v___x_5248_;
}
else
{
lean_object* v___x_5249_; size_t v___x_5250_; size_t v___x_5251_; lean_object* v___x_5252_; 
v___x_5249_ = lean_box(0);
v___x_5250_ = ((size_t)0ULL);
v___x_5251_ = lean_usize_of_nat(v___x_5246_);
v___x_5252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5242_, v___x_5250_, v___x_5251_, v___x_5249_, v___y_5202_);
lean_dec(v_a_5242_);
if (lean_obj_tag(v___x_5252_) == 0)
{
lean_object* v___x_5253_; 
lean_dec_ref_known(v___x_5252_, 1);
v___x_5253_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5193_, v___y_5194_, v___y_5195_, v_leanOpts_5196_, v_reconfigure_5197_, v_as_5198_, v___x_5213_, v_stop_5200_, v___x_5245_, v___y_5202_);
return v___x_5253_;
}
else
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5261_; 
lean_dec_ref(v___x_5245_);
lean_dec_ref(v_leanOpts_5196_);
lean_dec_ref(v___y_5195_);
lean_dec_ref(v_pkg_5193_);
v_a_5254_ = lean_ctor_get(v___x_5252_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5252_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5256_ = v___x_5252_;
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5252_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
}
}
else
{
lean_object* v_a_5263_; lean_object* v___x_5264_; uint8_t v___x_5265_; 
lean_del_object(v___x_5208_);
lean_dec_ref(v_depIdxs_5206_);
lean_dec_ref(v_leanOpts_5196_);
lean_dec_ref(v___y_5195_);
lean_dec_ref(v_pkg_5193_);
v_a_5263_ = lean_ctor_get(v___x_5240_, 1);
lean_inc(v_a_5263_);
lean_dec_ref_known(v___x_5240_, 2);
v___x_5264_ = lean_array_get_size(v_a_5263_);
v___x_5265_ = lean_nat_dec_lt(v___x_5216_, v___x_5264_);
if (v___x_5265_ == 0)
{
lean_object* v___x_5266_; lean_object* v___x_5268_; 
lean_dec(v_a_5263_);
v___x_5266_ = lean_box(0);
if (v_isShared_5237_ == 0)
{
lean_ctor_set_tag(v___x_5236_, 1);
lean_ctor_set(v___x_5236_, 0, v___x_5266_);
v___x_5268_ = v___x_5236_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v___x_5266_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
else
{
lean_object* v___x_5270_; size_t v___x_5271_; size_t v___x_5272_; lean_object* v___x_5273_; 
lean_del_object(v___x_5236_);
v___x_5270_ = lean_box(0);
v___x_5271_ = ((size_t)0ULL);
v___x_5272_ = lean_usize_of_nat(v___x_5264_);
v___x_5273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5263_, v___x_5271_, v___x_5272_, v___x_5270_, v___y_5202_);
lean_dec(v_a_5263_);
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5280_; 
v_isSharedCheck_5280_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5280_ == 0)
{
lean_object* v_unused_5281_; 
v_unused_5281_ = lean_ctor_get(v___x_5273_, 0);
lean_dec(v_unused_5281_);
v___x_5275_ = v___x_5273_;
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
else
{
lean_dec(v___x_5273_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5278_; 
if (v_isShared_5276_ == 0)
{
lean_ctor_set_tag(v___x_5275_, 1);
lean_ctor_set(v___x_5275_, 0, v___x_5270_);
v___x_5278_ = v___x_5275_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5270_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
}
else
{
lean_object* v_a_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5289_; 
v_a_5282_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5284_ = v___x_5273_;
v_isShared_5285_ = v_isSharedCheck_5289_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_a_5282_);
lean_dec(v___x_5273_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5289_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
lean_object* v___x_5287_; 
if (v_isShared_5285_ == 0)
{
v___x_5287_ = v___x_5284_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_a_5282_);
v___x_5287_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5286_;
}
v_reusejp_5286_:
{
return v___x_5287_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5298_; 
lean_del_object(v___x_5208_);
lean_dec_ref(v_depIdxs_5206_);
lean_dec_ref(v_ws_5205_);
lean_dec_ref(v_leanOpts_5196_);
lean_dec_ref(v___y_5195_);
lean_dec_ref(v_pkg_5193_);
v_a_5291_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5293_ = v___x_5233_;
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_a_5291_);
lean_dec(v___x_5233_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5296_; 
if (v_isShared_5294_ == 0)
{
v___x_5296_ = v___x_5293_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
}
}
else
{
uint8_t v___x_5299_; 
lean_inc(v_baseName_5225_);
lean_inc(v_wsIdx_5224_);
lean_dec(v___x_5229_);
lean_del_object(v___x_5208_);
lean_dec_ref(v_depIdxs_5206_);
lean_dec_ref(v_ws_5205_);
lean_dec_ref(v_leanOpts_5196_);
lean_dec_ref(v___y_5195_);
lean_dec_ref(v_pkg_5193_);
v___x_5299_ = lean_nat_dec_eq(v_wsIdx_5224_, v___x_5216_);
lean_dec(v_wsIdx_5224_);
if (v___x_5299_ == 0)
{
lean_object* v___x_5300_; uint8_t v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; uint8_t v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; 
v___x_5300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5301_ = 1;
lean_inc(v_name_5226_);
v___x_5302_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5226_, v___x_5301_);
v___x_5303_ = lean_string_append(v___x_5300_, v___x_5302_);
lean_dec_ref(v___x_5302_);
v___x_5304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5305_ = lean_string_append(v___x_5303_, v___x_5304_);
v___x_5306_ = l_Lean_Name_toString(v_baseName_5225_, v___x_5299_);
v___x_5307_ = lean_string_append(v___x_5305_, v___x_5306_);
lean_dec_ref(v___x_5306_);
v___x_5308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5309_ = lean_string_append(v___x_5307_, v___x_5308_);
v___x_5310_ = 3;
v___x_5311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5311_, 0, v___x_5309_);
lean_ctor_set_uint8(v___x_5311_, sizeof(void*)*1, v___x_5310_);
lean_inc_ref(v___y_5202_);
v___x_5312_ = lean_apply_2(v___y_5202_, v___x_5311_, lean_box(0));
v___x_5313_ = lean_box(0);
v___x_5314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5314_, 0, v___x_5313_);
return v___x_5314_;
}
else
{
lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; uint8_t v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; 
lean_dec(v_baseName_5225_);
v___x_5315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5226_);
v___x_5316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5226_, v___x_5299_);
v___x_5317_ = lean_string_append(v___x_5315_, v___x_5316_);
v___x_5318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5319_ = lean_string_append(v___x_5317_, v___x_5318_);
v___x_5320_ = lean_string_append(v___x_5319_, v___x_5316_);
lean_dec_ref(v___x_5316_);
v___x_5321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5322_ = lean_string_append(v___x_5320_, v___x_5321_);
v___x_5323_ = 3;
v___x_5324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5324_, 0, v___x_5322_);
lean_ctor_set_uint8(v___x_5324_, sizeof(void*)*1, v___x_5323_);
lean_inc_ref(v___y_5202_);
v___x_5325_ = lean_apply_2(v___y_5202_, v___x_5324_, lean_box(0));
v___x_5326_ = lean_box(0);
v___x_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5326_);
return v___x_5327_;
}
}
}
else
{
lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; uint8_t v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; 
lean_inc(v_baseName_5225_);
lean_del_object(v___x_5208_);
lean_dec_ref(v_depIdxs_5206_);
lean_dec_ref(v_ws_5205_);
lean_dec_ref(v_leanOpts_5196_);
lean_dec_ref(v___y_5195_);
lean_dec_ref(v_pkg_5193_);
v___x_5328_ = l_Lean_Name_toString(v_baseName_5225_, v___x_5204_);
v___x_5329_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5330_ = lean_string_append(v___x_5328_, v___x_5329_);
v___x_5331_ = 3;
v___x_5332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5332_, 0, v___x_5330_);
lean_ctor_set_uint8(v___x_5332_, sizeof(void*)*1, v___x_5331_);
lean_inc_ref(v___y_5202_);
v___x_5333_ = lean_apply_2(v___y_5202_, v___x_5332_, lean_box(0));
v___x_5334_ = lean_box(0);
v___x_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5335_, 0, v___x_5334_);
return v___x_5335_;
}
}
}
}
else
{
lean_object* v___x_5337_; 
lean_dec_ref(v_leanOpts_5196_);
lean_dec_ref(v___y_5195_);
lean_dec_ref(v_pkg_5193_);
v___x_5337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5337_, 0, v_b_5201_);
return v___x_5337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_start_5338_, lean_object* v_pkg_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v_leanOpts_5342_, lean_object* v_reconfigure_5343_, lean_object* v_as_5344_, lean_object* v_i_5345_, lean_object* v_stop_5346_, lean_object* v_b_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
uint8_t v_reconfigure_boxed_5350_; size_t v_i_boxed_5351_; size_t v_stop_boxed_5352_; lean_object* v_res_5353_; 
v_reconfigure_boxed_5350_ = lean_unbox(v_reconfigure_5343_);
v_i_boxed_5351_ = lean_unbox_usize(v_i_5345_);
lean_dec(v_i_5345_);
v_stop_boxed_5352_ = lean_unbox_usize(v_stop_5346_);
lean_dec(v_stop_5346_);
v_res_5353_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5338_, v_pkg_5339_, v___y_5340_, v___y_5341_, v_leanOpts_5342_, v_reconfigure_boxed_5350_, v_as_5344_, v_i_boxed_5351_, v_stop_boxed_5352_, v_b_5347_, v___y_5348_);
lean_dec_ref(v___y_5348_);
lean_dec_ref(v_as_5344_);
lean_dec(v___y_5340_);
lean_dec(v_start_5338_);
return v_res_5353_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v_leanOpts_5356_, uint8_t v_reconfigure_5357_, lean_object* v_ws_5358_, lean_object* v_i_5359_, lean_object* v_next_5360_, lean_object* v___y_5361_){
_start:
{
lean_object* v_packages_5363_; lean_object* v_pkg_5364_; lean_object* v_ws_5366_; lean_object* v_depIdxs_5367_; lean_object* v___y_5368_; lean_object* v_____x_5378_; lean_object* v___y_5379_; lean_object* v_depConfigs_5382_; lean_object* v_start_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v_s_5386_; lean_object* v___x_5387_; uint8_t v___x_5388_; 
v_packages_5363_ = lean_ctor_get(v_ws_5358_, 4);
v_pkg_5364_ = lean_array_fget(v_packages_5363_, v_i_5359_);
lean_dec(v_i_5359_);
v_depConfigs_5382_ = lean_ctor_get(v_pkg_5364_, 12);
v_start_5383_ = lean_array_get_size(v_packages_5363_);
v___x_5384_ = lean_array_get_size(v_depConfigs_5382_);
v___x_5385_ = lean_mk_empty_array_with_capacity(v___x_5384_);
lean_inc_ref(v___x_5385_);
lean_inc_ref(v_ws_5358_);
v_s_5386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5386_, 0, v_ws_5358_);
lean_ctor_set(v_s_5386_, 1, v___x_5385_);
v___x_5387_ = lean_unsigned_to_nat(0u);
v___x_5388_ = lean_nat_dec_le(v___x_5384_, v___x_5384_);
if (v___x_5388_ == 0)
{
uint8_t v___x_5389_; 
v___x_5389_ = lean_nat_dec_lt(v___x_5387_, v___x_5384_);
if (v___x_5389_ == 0)
{
lean_object* v_ws_5390_; lean_object* v_packages_5391_; lean_object* v___x_5392_; uint8_t v___x_5393_; 
lean_dec_ref_known(v_s_5386_, 2);
v_ws_5390_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5358_, v_pkg_5364_, v___x_5385_);
v_packages_5391_ = lean_ctor_get(v_ws_5390_, 4);
lean_inc_ref(v_packages_5391_);
v___x_5392_ = lean_array_get_size(v_packages_5391_);
lean_dec_ref(v_packages_5391_);
v___x_5393_ = lean_nat_dec_lt(v_next_5360_, v___x_5392_);
if (v___x_5393_ == 0)
{
lean_object* v___x_5394_; 
lean_dec(v_next_5360_);
lean_dec_ref(v_leanOpts_5356_);
lean_dec_ref(v___y_5355_);
v___x_5394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5394_, 0, v_ws_5390_);
return v___x_5394_;
}
else
{
lean_object* v___x_5395_; lean_object* v___x_5396_; 
v___x_5395_ = lean_unsigned_to_nat(1u);
v___x_5396_ = lean_nat_add(v_next_5360_, v___x_5395_);
v_ws_5358_ = v_ws_5390_;
v_i_5359_ = v_next_5360_;
v_next_5360_ = v___x_5396_;
goto _start;
}
}
else
{
size_t v___x_5398_; size_t v___x_5399_; lean_object* v___x_5400_; 
lean_dec_ref(v___x_5385_);
lean_dec_ref(v_ws_5358_);
v___x_5398_ = lean_usize_of_nat(v___x_5384_);
v___x_5399_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5356_);
lean_inc_ref(v___y_5355_);
lean_inc(v_pkg_5364_);
v___x_5400_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5383_, v_pkg_5364_, v___y_5354_, v___y_5355_, v_leanOpts_5356_, v_reconfigure_5357_, v_depConfigs_5382_, v___x_5398_, v___x_5399_, v_s_5386_, v___y_5361_);
if (lean_obj_tag(v___x_5400_) == 0)
{
lean_object* v_a_5401_; 
v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
lean_inc(v_a_5401_);
lean_dec_ref_known(v___x_5400_, 1);
v_____x_5378_ = v_a_5401_;
v___y_5379_ = v___y_5361_;
goto v___jp_5377_;
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5409_; 
lean_dec(v_pkg_5364_);
lean_dec(v_next_5360_);
lean_dec_ref(v_leanOpts_5356_);
lean_dec_ref(v___y_5355_);
v_a_5402_ = lean_ctor_get(v___x_5400_, 0);
v_isSharedCheck_5409_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5409_ == 0)
{
v___x_5404_ = v___x_5400_;
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_a_5402_);
lean_dec(v___x_5400_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5407_; 
if (v_isShared_5405_ == 0)
{
v___x_5407_ = v___x_5404_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5402_);
v___x_5407_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
return v___x_5407_;
}
}
}
}
}
else
{
uint8_t v___x_5410_; 
v___x_5410_ = lean_nat_dec_lt(v___x_5387_, v___x_5384_);
if (v___x_5410_ == 0)
{
lean_dec_ref_known(v_s_5386_, 2);
v_ws_5366_ = v_ws_5358_;
v_depIdxs_5367_ = v___x_5385_;
v___y_5368_ = v___y_5361_;
goto v___jp_5365_;
}
else
{
size_t v___x_5411_; size_t v___x_5412_; lean_object* v___x_5413_; 
lean_dec_ref(v___x_5385_);
lean_dec_ref(v_ws_5358_);
v___x_5411_ = lean_usize_of_nat(v___x_5384_);
v___x_5412_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5356_);
lean_inc_ref(v___y_5355_);
lean_inc(v_pkg_5364_);
v___x_5413_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5383_, v_pkg_5364_, v___y_5354_, v___y_5355_, v_leanOpts_5356_, v_reconfigure_5357_, v_depConfigs_5382_, v___x_5411_, v___x_5412_, v_s_5386_, v___y_5361_);
if (lean_obj_tag(v___x_5413_) == 0)
{
lean_object* v_a_5414_; 
v_a_5414_ = lean_ctor_get(v___x_5413_, 0);
lean_inc(v_a_5414_);
lean_dec_ref_known(v___x_5413_, 1);
v_____x_5378_ = v_a_5414_;
v___y_5379_ = v___y_5361_;
goto v___jp_5377_;
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
lean_dec(v_pkg_5364_);
lean_dec(v_next_5360_);
lean_dec_ref(v_leanOpts_5356_);
lean_dec_ref(v___y_5355_);
v_a_5415_ = lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5417_ = v___x_5413_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5413_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_a_5415_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
}
v___jp_5365_:
{
lean_object* v_ws_5369_; lean_object* v_packages_5370_; lean_object* v___x_5371_; uint8_t v___x_5372_; 
v_ws_5369_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5366_, v_pkg_5364_, v_depIdxs_5367_);
v_packages_5370_ = lean_ctor_get(v_ws_5369_, 4);
lean_inc_ref(v_packages_5370_);
v___x_5371_ = lean_array_get_size(v_packages_5370_);
lean_dec_ref(v_packages_5370_);
v___x_5372_ = lean_nat_dec_lt(v_next_5360_, v___x_5371_);
if (v___x_5372_ == 0)
{
lean_object* v___x_5373_; 
lean_dec(v_next_5360_);
lean_dec_ref(v_leanOpts_5356_);
lean_dec_ref(v___y_5355_);
v___x_5373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5373_, 0, v_ws_5369_);
return v___x_5373_;
}
else
{
lean_object* v___x_5374_; lean_object* v___x_5375_; 
v___x_5374_ = lean_unsigned_to_nat(1u);
v___x_5375_ = lean_nat_add(v_next_5360_, v___x_5374_);
v_ws_5358_ = v_ws_5369_;
v_i_5359_ = v_next_5360_;
v_next_5360_ = v___x_5375_;
v___y_5361_ = v___y_5368_;
goto _start;
}
}
v___jp_5377_:
{
lean_object* v_ws_5380_; lean_object* v_depIdxs_5381_; 
v_ws_5380_ = lean_ctor_get(v_____x_5378_, 0);
lean_inc_ref(v_ws_5380_);
v_depIdxs_5381_ = lean_ctor_get(v_____x_5378_, 1);
lean_inc_ref(v_depIdxs_5381_);
lean_dec_ref(v_____x_5378_);
v_ws_5366_ = v_ws_5380_;
v_depIdxs_5367_ = v_depIdxs_5381_;
v___y_5368_ = v___y_5379_;
goto v___jp_5365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v_leanOpts_5425_, lean_object* v_reconfigure_5426_, lean_object* v_ws_5427_, lean_object* v_i_5428_, lean_object* v_next_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_){
_start:
{
uint8_t v_reconfigure_boxed_5432_; lean_object* v_res_5433_; 
v_reconfigure_boxed_5432_ = lean_unbox(v_reconfigure_5426_);
v_res_5433_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5423_, v___y_5424_, v_leanOpts_5425_, v_reconfigure_boxed_5432_, v_ws_5427_, v_i_5428_, v_next_5429_, v___y_5430_);
lean_dec_ref(v___y_5430_);
lean_dec(v___y_5423_);
return v_res_5433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(lean_object* v_as_5434_, size_t v_i_5435_, size_t v_stop_5436_, lean_object* v_b_5437_){
_start:
{
uint8_t v___x_5438_; 
v___x_5438_ = lean_usize_dec_eq(v_i_5435_, v_stop_5436_);
if (v___x_5438_ == 0)
{
lean_object* v___x_5439_; lean_object* v_name_5440_; lean_object* v___x_5441_; size_t v___x_5442_; size_t v___x_5443_; 
v___x_5439_ = lean_array_uget_borrowed(v_as_5434_, v_i_5435_);
v_name_5440_ = lean_ctor_get(v___x_5439_, 0);
lean_inc(v___x_5439_);
lean_inc(v_name_5440_);
v___x_5441_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5440_, v___x_5439_, v_b_5437_);
v___x_5442_ = ((size_t)1ULL);
v___x_5443_ = lean_usize_add(v_i_5435_, v___x_5442_);
v_i_5435_ = v___x_5443_;
v_b_5437_ = v___x_5441_;
goto _start;
}
else
{
return v_b_5437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2___boxed(lean_object* v_as_5445_, lean_object* v_i_5446_, lean_object* v_stop_5447_, lean_object* v_b_5448_){
_start:
{
size_t v_i_boxed_5449_; size_t v_stop_boxed_5450_; lean_object* v_res_5451_; 
v_i_boxed_5449_ = lean_unbox_usize(v_i_5446_);
lean_dec(v_i_5446_);
v_stop_boxed_5450_ = lean_unbox_usize(v_stop_5447_);
lean_dec(v_stop_5447_);
v_res_5451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5445_, v_i_boxed_5449_, v_stop_boxed_5450_, v_b_5448_);
lean_dec_ref(v_as_5445_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5452_, size_t v_i_5453_, size_t v_stop_5454_, lean_object* v_b_5455_){
_start:
{
uint8_t v___x_5456_; 
v___x_5456_ = lean_usize_dec_eq(v_i_5453_, v_stop_5454_);
if (v___x_5456_ == 0)
{
lean_object* v___x_5457_; lean_object* v_name_5458_; lean_object* v___x_5459_; size_t v___x_5460_; size_t v___x_5461_; lean_object* v___x_5462_; 
v___x_5457_ = lean_array_uget_borrowed(v_as_5452_, v_i_5453_);
v_name_5458_ = lean_ctor_get(v___x_5457_, 0);
lean_inc(v___x_5457_);
lean_inc(v_name_5458_);
v___x_5459_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5458_, v___x_5457_, v_b_5455_);
v___x_5460_ = ((size_t)1ULL);
v___x_5461_ = lean_usize_add(v_i_5453_, v___x_5460_);
v___x_5462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5452_, v___x_5461_, v_stop_5454_, v___x_5459_);
return v___x_5462_;
}
else
{
return v_b_5455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5463_, lean_object* v_i_5464_, lean_object* v_stop_5465_, lean_object* v_b_5466_){
_start:
{
size_t v_i_boxed_5467_; size_t v_stop_boxed_5468_; lean_object* v_res_5469_; 
v_i_boxed_5467_ = lean_unbox_usize(v_i_5464_);
lean_dec(v_i_5464_);
v_stop_boxed_5468_ = lean_unbox_usize(v_stop_5465_);
lean_dec(v_stop_5465_);
v_res_5469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5463_, v_i_boxed_5467_, v_stop_boxed_5468_, v_b_5466_);
lean_dec_ref(v_as_5463_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5479_, lean_object* v_manifest_5480_, lean_object* v_leanOpts_5481_, uint8_t v_reconfigure_5482_, lean_object* v_overrides_5483_, lean_object* v_a_5484_){
_start:
{
lean_object* v___y_5487_; lean_object* v___y_5488_; lean_object* v___y_5489_; lean_object* v___y_5490_; lean_object* v___y_5491_; lean_object* v___y_5504_; lean_object* v___y_5505_; lean_object* v___y_5506_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v___y_5510_; lean_object* v___y_5518_; lean_object* v___y_5519_; lean_object* v___y_5520_; lean_object* v___y_5521_; lean_object* v___y_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5535_; lean_object* v___y_5536_; lean_object* v___y_5537_; lean_object* v___y_5538_; lean_object* v_packagesDir_x3f_5581_; lean_object* v_packages_5582_; lean_object* v___y_5584_; lean_object* v___y_5585_; lean_object* v___y_5598_; lean_object* v___x_5606_; lean_object* v___x_5607_; uint8_t v___x_5608_; 
v_packagesDir_x3f_5581_ = lean_ctor_get(v_manifest_5480_, 2);
lean_inc(v_packagesDir_x3f_5581_);
v_packages_5582_ = lean_ctor_get(v_manifest_5480_, 3);
lean_inc_ref(v_packages_5582_);
lean_dec_ref(v_manifest_5480_);
v___x_5606_ = lean_array_get_size(v_packages_5582_);
v___x_5607_ = lean_unsigned_to_nat(0u);
v___x_5608_ = lean_nat_dec_eq(v___x_5606_, v___x_5607_);
if (v___x_5608_ == 0)
{
lean_object* v_packages_5609_; lean_object* v___x_5610_; lean_object* v_config_5611_; lean_object* v_toWorkspaceConfig_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; uint8_t v___x_5616_; 
v_packages_5609_ = lean_ctor_get(v_ws_5479_, 4);
v___x_5610_ = lean_array_fget_borrowed(v_packages_5609_, v___x_5607_);
v_config_5611_ = lean_ctor_get(v___x_5610_, 6);
v_toWorkspaceConfig_5612_ = lean_ctor_get(v_config_5611_, 0);
lean_inc_ref(v_toWorkspaceConfig_5612_);
v___x_5613_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5612_);
v___x_5614_ = l_Lake_mkRelPathString(v___x_5613_);
v___x_5615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5614_);
v___x_5616_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5581_, v___x_5615_);
lean_dec_ref_known(v___x_5615_, 1);
if (v___x_5616_ == 0)
{
lean_object* v___x_5617_; lean_object* v___x_5618_; 
v___x_5617_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5484_);
v___x_5618_ = lean_apply_2(v_a_5484_, v___x_5617_, lean_box(0));
v___y_5598_ = v_a_5484_;
goto v___jp_5597_;
}
else
{
v___y_5598_ = v_a_5484_;
goto v___jp_5597_;
}
}
else
{
v___y_5598_ = v_a_5484_;
goto v___jp_5597_;
}
v___jp_5486_:
{
lean_object* v___x_5492_; lean_object* v___x_5493_; 
v___x_5492_ = lean_array_get_size(v___y_5488_);
lean_dec_ref(v___y_5488_);
v___x_5493_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5491_, v___y_5487_, v_leanOpts_5481_, v_reconfigure_5482_, v_ws_5479_, v___y_5489_, v___x_5492_, v___y_5490_);
lean_dec(v___y_5491_);
if (lean_obj_tag(v___x_5493_) == 0)
{
lean_object* v_a_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5502_; 
v_a_5494_ = lean_ctor_get(v___x_5493_, 0);
v_isSharedCheck_5502_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5502_ == 0)
{
v___x_5496_ = v___x_5493_;
v_isShared_5497_ = v_isSharedCheck_5502_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_a_5494_);
lean_dec(v___x_5493_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5502_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5498_; lean_object* v___x_5500_; 
v___x_5498_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_a_5494_);
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 0, v___x_5498_);
v___x_5500_ = v___x_5496_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v___x_5498_);
v___x_5500_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
return v___x_5500_;
}
}
}
else
{
return v___x_5493_;
}
}
v___jp_5503_:
{
if (lean_obj_tag(v___y_5510_) == 0)
{
lean_dec_ref(v___y_5507_);
v___y_5487_ = v___y_5504_;
v___y_5488_ = v___y_5505_;
v___y_5489_ = v___y_5508_;
v___y_5490_ = v___y_5509_;
v___y_5491_ = v___y_5510_;
goto v___jp_5486_;
}
else
{
lean_object* v___x_5511_; uint8_t v___x_5512_; 
v___x_5511_ = lean_array_get_size(v___y_5507_);
lean_dec_ref(v___y_5507_);
v___x_5512_ = lean_nat_dec_eq(v___x_5511_, v___y_5506_);
if (v___x_5512_ == 0)
{
lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; 
lean_dec(v___y_5508_);
lean_dec_ref(v___y_5505_);
lean_dec_ref(v___y_5504_);
lean_dec_ref(v_leanOpts_5481_);
lean_dec_ref(v_ws_5479_);
v___x_5513_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5509_);
v___x_5514_ = lean_apply_2(v___y_5509_, v___x_5513_, lean_box(0));
v___x_5515_ = lean_box(0);
v___x_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5516_, 0, v___x_5515_);
return v___x_5516_;
}
else
{
v___y_5487_ = v___y_5504_;
v___y_5488_ = v___y_5505_;
v___y_5489_ = v___y_5508_;
v___y_5490_ = v___y_5509_;
v___y_5491_ = v___y_5510_;
goto v___jp_5486_;
}
}
}
v___jp_5517_:
{
lean_object* v___x_5525_; uint8_t v___x_5526_; 
v___x_5525_ = lean_array_get_size(v_overrides_5483_);
v___x_5526_ = lean_nat_dec_lt(v___y_5520_, v___x_5525_);
if (v___x_5526_ == 0)
{
v___y_5504_ = v___y_5518_;
v___y_5505_ = v___y_5519_;
v___y_5506_ = v___y_5520_;
v___y_5507_ = v___y_5521_;
v___y_5508_ = v___y_5522_;
v___y_5509_ = v___y_5523_;
v___y_5510_ = v___y_5524_;
goto v___jp_5503_;
}
else
{
uint8_t v___x_5527_; 
v___x_5527_ = lean_nat_dec_le(v___x_5525_, v___x_5525_);
if (v___x_5527_ == 0)
{
if (v___x_5526_ == 0)
{
v___y_5504_ = v___y_5518_;
v___y_5505_ = v___y_5519_;
v___y_5506_ = v___y_5520_;
v___y_5507_ = v___y_5521_;
v___y_5508_ = v___y_5522_;
v___y_5509_ = v___y_5523_;
v___y_5510_ = v___y_5524_;
goto v___jp_5503_;
}
else
{
size_t v___x_5528_; size_t v___x_5529_; lean_object* v___x_5530_; 
v___x_5528_ = ((size_t)0ULL);
v___x_5529_ = lean_usize_of_nat(v___x_5525_);
v___x_5530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5483_, v___x_5528_, v___x_5529_, v___y_5524_);
v___y_5504_ = v___y_5518_;
v___y_5505_ = v___y_5519_;
v___y_5506_ = v___y_5520_;
v___y_5507_ = v___y_5521_;
v___y_5508_ = v___y_5522_;
v___y_5509_ = v___y_5523_;
v___y_5510_ = v___x_5530_;
goto v___jp_5503_;
}
}
else
{
size_t v___x_5531_; size_t v___x_5532_; lean_object* v___x_5533_; 
v___x_5531_ = ((size_t)0ULL);
v___x_5532_ = lean_usize_of_nat(v___x_5525_);
v___x_5533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5483_, v___x_5531_, v___x_5532_, v___y_5524_);
v___y_5504_ = v___y_5518_;
v___y_5505_ = v___y_5519_;
v___y_5506_ = v___y_5520_;
v___y_5507_ = v___y_5521_;
v___y_5508_ = v___y_5522_;
v___y_5509_ = v___y_5523_;
v___y_5510_ = v___x_5533_;
goto v___jp_5503_;
}
}
}
v___jp_5534_:
{
lean_object* v_packages_5539_; lean_object* v___x_5540_; lean_object* v_wsIdx_5541_; lean_object* v_dir_5542_; lean_object* v_depConfigs_5543_; lean_object* v___x_5544_; 
v_packages_5539_ = lean_ctor_get(v_ws_5479_, 4);
v___x_5540_ = lean_array_fget_borrowed(v_packages_5539_, v___y_5536_);
v_wsIdx_5541_ = lean_ctor_get(v___x_5540_, 0);
v_dir_5542_ = lean_ctor_get(v___x_5540_, 4);
v_depConfigs_5543_ = lean_ctor_get(v___x_5540_, 12);
v___x_5544_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5538_, v_depConfigs_5543_, v___y_5537_);
if (lean_obj_tag(v___x_5544_) == 0)
{
lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; 
lean_dec_ref_known(v___x_5544_, 1);
v___x_5545_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5542_);
v___x_5546_ = l_Lake_joinRelative(v_dir_5542_, v___x_5545_);
v___x_5547_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5548_ = l_Lake_joinRelative(v___x_5546_, v___x_5547_);
v___x_5549_ = l_Lake_Manifest_tryLoadEntries(v___x_5548_);
if (lean_obj_tag(v___x_5549_) == 0)
{
lean_object* v_a_5550_; lean_object* v___x_5551_; uint8_t v___x_5552_; 
v_a_5550_ = lean_ctor_get(v___x_5549_, 0);
lean_inc(v_a_5550_);
lean_dec_ref_known(v___x_5549_, 1);
v___x_5551_ = lean_array_get_size(v_a_5550_);
v___x_5552_ = lean_nat_dec_lt(v___y_5536_, v___x_5551_);
if (v___x_5552_ == 0)
{
lean_dec(v_a_5550_);
lean_inc(v_wsIdx_5541_);
lean_inc_ref(v_depConfigs_5543_);
lean_inc_ref(v_packages_5539_);
v___y_5518_ = v___y_5535_;
v___y_5519_ = v_packages_5539_;
v___y_5520_ = v___y_5536_;
v___y_5521_ = v_depConfigs_5543_;
v___y_5522_ = v_wsIdx_5541_;
v___y_5523_ = v___y_5537_;
v___y_5524_ = v___y_5538_;
goto v___jp_5517_;
}
else
{
uint8_t v___x_5553_; 
v___x_5553_ = lean_nat_dec_le(v___x_5551_, v___x_5551_);
if (v___x_5553_ == 0)
{
if (v___x_5552_ == 0)
{
lean_dec(v_a_5550_);
lean_inc(v_wsIdx_5541_);
lean_inc_ref(v_depConfigs_5543_);
lean_inc_ref(v_packages_5539_);
v___y_5518_ = v___y_5535_;
v___y_5519_ = v_packages_5539_;
v___y_5520_ = v___y_5536_;
v___y_5521_ = v_depConfigs_5543_;
v___y_5522_ = v_wsIdx_5541_;
v___y_5523_ = v___y_5537_;
v___y_5524_ = v___y_5538_;
goto v___jp_5517_;
}
else
{
size_t v___x_5554_; size_t v___x_5555_; lean_object* v___x_5556_; 
v___x_5554_ = ((size_t)0ULL);
v___x_5555_ = lean_usize_of_nat(v___x_5551_);
v___x_5556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5550_, v___x_5554_, v___x_5555_, v___y_5538_);
lean_dec(v_a_5550_);
lean_inc(v_wsIdx_5541_);
lean_inc_ref(v_depConfigs_5543_);
lean_inc_ref(v_packages_5539_);
v___y_5518_ = v___y_5535_;
v___y_5519_ = v_packages_5539_;
v___y_5520_ = v___y_5536_;
v___y_5521_ = v_depConfigs_5543_;
v___y_5522_ = v_wsIdx_5541_;
v___y_5523_ = v___y_5537_;
v___y_5524_ = v___x_5556_;
goto v___jp_5517_;
}
}
else
{
size_t v___x_5557_; size_t v___x_5558_; lean_object* v___x_5559_; 
v___x_5557_ = ((size_t)0ULL);
v___x_5558_ = lean_usize_of_nat(v___x_5551_);
v___x_5559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5550_, v___x_5557_, v___x_5558_, v___y_5538_);
lean_dec(v_a_5550_);
lean_inc(v_wsIdx_5541_);
lean_inc_ref(v_depConfigs_5543_);
lean_inc_ref(v_packages_5539_);
v___y_5518_ = v___y_5535_;
v___y_5519_ = v_packages_5539_;
v___y_5520_ = v___y_5536_;
v___y_5521_ = v_depConfigs_5543_;
v___y_5522_ = v_wsIdx_5541_;
v___y_5523_ = v___y_5537_;
v___y_5524_ = v___x_5559_;
goto v___jp_5517_;
}
}
}
else
{
lean_object* v_a_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5572_; 
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5535_);
lean_dec_ref(v_leanOpts_5481_);
lean_dec_ref(v_ws_5479_);
v_a_5560_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5562_ = v___x_5549_;
v_isShared_5563_ = v_isSharedCheck_5572_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_a_5560_);
lean_dec(v___x_5549_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5572_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5564_; uint8_t v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5570_; 
v___x_5564_ = lean_io_error_to_string(v_a_5560_);
v___x_5565_ = 3;
v___x_5566_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5566_, 0, v___x_5564_);
lean_ctor_set_uint8(v___x_5566_, sizeof(void*)*1, v___x_5565_);
lean_inc_ref(v___y_5537_);
v___x_5567_ = lean_apply_2(v___y_5537_, v___x_5566_, lean_box(0));
v___x_5568_ = lean_box(0);
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 0, v___x_5568_);
v___x_5570_ = v___x_5562_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5568_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
}
else
{
lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5580_; 
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5535_);
lean_dec_ref(v_leanOpts_5481_);
lean_dec_ref(v_ws_5479_);
v_a_5573_ = lean_ctor_get(v___x_5544_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v___x_5544_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5575_ = v___x_5544_;
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5544_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5578_; 
if (v_isShared_5576_ == 0)
{
v___x_5578_ = v___x_5575_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
v___x_5578_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
return v___x_5578_;
}
}
}
}
v___jp_5583_:
{
lean_object* v_pkgEntries_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; uint8_t v___x_5589_; 
v_pkgEntries_5586_ = lean_box(1);
v___x_5587_ = lean_unsigned_to_nat(0u);
v___x_5588_ = lean_array_get_size(v_packages_5582_);
v___x_5589_ = lean_nat_dec_lt(v___x_5587_, v___x_5588_);
if (v___x_5589_ == 0)
{
lean_dec_ref(v_packages_5582_);
v___y_5535_ = v___y_5585_;
v___y_5536_ = v___x_5587_;
v___y_5537_ = v___y_5584_;
v___y_5538_ = v_pkgEntries_5586_;
goto v___jp_5534_;
}
else
{
uint8_t v___x_5590_; 
v___x_5590_ = lean_nat_dec_le(v___x_5588_, v___x_5588_);
if (v___x_5590_ == 0)
{
if (v___x_5589_ == 0)
{
lean_dec_ref(v_packages_5582_);
v___y_5535_ = v___y_5585_;
v___y_5536_ = v___x_5587_;
v___y_5537_ = v___y_5584_;
v___y_5538_ = v_pkgEntries_5586_;
goto v___jp_5534_;
}
else
{
size_t v___x_5591_; size_t v___x_5592_; lean_object* v___x_5593_; 
v___x_5591_ = ((size_t)0ULL);
v___x_5592_ = lean_usize_of_nat(v___x_5588_);
v___x_5593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5582_, v___x_5591_, v___x_5592_, v_pkgEntries_5586_);
lean_dec_ref(v_packages_5582_);
v___y_5535_ = v___y_5585_;
v___y_5536_ = v___x_5587_;
v___y_5537_ = v___y_5584_;
v___y_5538_ = v___x_5593_;
goto v___jp_5534_;
}
}
else
{
size_t v___x_5594_; size_t v___x_5595_; lean_object* v___x_5596_; 
v___x_5594_ = ((size_t)0ULL);
v___x_5595_ = lean_usize_of_nat(v___x_5588_);
v___x_5596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5582_, v___x_5594_, v___x_5595_, v_pkgEntries_5586_);
lean_dec_ref(v_packages_5582_);
v___y_5535_ = v___y_5585_;
v___y_5536_ = v___x_5587_;
v___y_5537_ = v___y_5584_;
v___y_5538_ = v___x_5596_;
goto v___jp_5534_;
}
}
}
v___jp_5597_:
{
if (lean_obj_tag(v_packagesDir_x3f_5581_) == 0)
{
lean_object* v_packages_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v_config_5602_; lean_object* v_toWorkspaceConfig_5603_; lean_object* v___x_5604_; 
v_packages_5599_ = lean_ctor_get(v_ws_5479_, 4);
v___x_5600_ = lean_unsigned_to_nat(0u);
v___x_5601_ = lean_array_fget_borrowed(v_packages_5599_, v___x_5600_);
v_config_5602_ = lean_ctor_get(v___x_5601_, 6);
v_toWorkspaceConfig_5603_ = lean_ctor_get(v_config_5602_, 0);
lean_inc_ref(v_toWorkspaceConfig_5603_);
v___x_5604_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5603_);
v___y_5584_ = v___y_5598_;
v___y_5585_ = v___x_5604_;
goto v___jp_5583_;
}
else
{
lean_object* v_val_5605_; 
v_val_5605_ = lean_ctor_get(v_packagesDir_x3f_5581_, 0);
lean_inc(v_val_5605_);
lean_dec_ref_known(v_packagesDir_x3f_5581_, 1);
v___y_5584_ = v___y_5598_;
v___y_5585_ = v_val_5605_;
goto v___jp_5583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5619_, lean_object* v_manifest_5620_, lean_object* v_leanOpts_5621_, lean_object* v_reconfigure_5622_, lean_object* v_overrides_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_){
_start:
{
uint8_t v_reconfigure_boxed_5626_; lean_object* v_res_5627_; 
v_reconfigure_boxed_5626_ = lean_unbox(v_reconfigure_5622_);
v_res_5627_ = l_Lake_Workspace_materializeDeps(v_ws_5619_, v_manifest_5620_, v_leanOpts_5621_, v_reconfigure_boxed_5626_, v_overrides_5623_, v_a_5624_);
lean_dec_ref(v_a_5624_);
lean_dec_ref(v_overrides_5623_);
return v_res_5627_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v_leanOpts_5630_, uint8_t v_reconfigure_5631_, lean_object* v_ws_5632_, lean_object* v_i_5633_, lean_object* v_i__lt_5634_, lean_object* v_next_5635_, lean_object* v_lt__next_5636_, lean_object* v___y_5637_){
_start:
{
lean_object* v___x_5639_; 
v___x_5639_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5628_, v___y_5629_, v_leanOpts_5630_, v_reconfigure_5631_, v_ws_5632_, v_i_5633_, v_next_5635_, v___y_5637_);
return v___x_5639_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v_leanOpts_5642_, lean_object* v_reconfigure_5643_, lean_object* v_ws_5644_, lean_object* v_i_5645_, lean_object* v_i__lt_5646_, lean_object* v_next_5647_, lean_object* v_lt__next_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_){
_start:
{
uint8_t v_reconfigure_boxed_5651_; lean_object* v_res_5652_; 
v_reconfigure_boxed_5651_ = lean_unbox(v_reconfigure_5643_);
v_res_5652_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5640_, v___y_5641_, v_leanOpts_5642_, v_reconfigure_boxed_5651_, v_ws_5644_, v_i_5645_, v_i__lt_5646_, v_next_5647_, v_lt__next_5648_, v___y_5649_);
lean_dec_ref(v___y_5649_);
lean_dec(v___y_5640_);
return v_res_5652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(lean_object* v_start_5653_, lean_object* v_pkg_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v_leanOpts_5657_, uint8_t v_reconfigure_5658_, lean_object* v_as_5659_, size_t v_i_5660_, size_t v_stop_5661_, lean_object* v_b_5662_, lean_object* v___y_5663_){
_start:
{
lean_object* v___x_5665_; 
v___x_5665_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5654_, v___y_5655_, v___y_5656_, v_leanOpts_5657_, v_reconfigure_5658_, v_as_5659_, v_i_5660_, v_stop_5661_, v_b_5662_, v___y_5663_);
return v___x_5665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_start_5666_, lean_object* v_pkg_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v_leanOpts_5670_, lean_object* v_reconfigure_5671_, lean_object* v_as_5672_, lean_object* v_i_5673_, lean_object* v_stop_5674_, lean_object* v_b_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_){
_start:
{
uint8_t v_reconfigure_boxed_5678_; size_t v_i_boxed_5679_; size_t v_stop_boxed_5680_; lean_object* v_res_5681_; 
v_reconfigure_boxed_5678_ = lean_unbox(v_reconfigure_5671_);
v_i_boxed_5679_ = lean_unbox_usize(v_i_5673_);
lean_dec(v_i_5673_);
v_stop_boxed_5680_ = lean_unbox_usize(v_stop_5674_);
lean_dec(v_stop_5674_);
v_res_5681_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(v_start_5666_, v_pkg_5667_, v___y_5668_, v___y_5669_, v_leanOpts_5670_, v_reconfigure_boxed_5678_, v_as_5672_, v_i_boxed_5679_, v_stop_boxed_5680_, v_b_5675_, v___y_5676_);
lean_dec_ref(v___y_5676_);
lean_dec_ref(v_as_5672_);
lean_dec(v___y_5668_);
lean_dec(v_start_5666_);
return v_res_5681_;
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

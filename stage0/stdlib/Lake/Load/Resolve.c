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
v___x_1832_ = lean_array_get_size(v___y_1829_);
v___x_1833_ = lean_nat_dec_lt(v___y_1828_, v___x_1832_);
if (v___x_1833_ == 0)
{
v___y_1769_ = v___y_1830_;
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
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1829_, v___x_1835_, v___x_1836_, v___x_1834_, v_a_1762_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_dec_ref_known(v___x_1837_, 1);
v___y_1769_ = v___y_1830_;
v_fst_1770_ = v_val_1831_;
v_snd_1771_ = v_a_1761_;
goto v___jp_1768_;
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref(v_val_1831_);
lean_dec_ref(v___y_1830_);
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
v___y_1828_ = v___x_1848_;
v___y_1829_ = v___x_1849_;
v___y_1830_ = v___y_1847_;
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
v___y_1828_ = v___x_1848_;
v___y_1829_ = v___x_1849_;
v___y_1830_ = v___y_1847_;
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
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11(void){
_start:
{
uint32_t v___x_2238_; uint8_t v___x_2239_; 
v___x_2238_ = 4;
v___x_2239_ = lean_uint32_to_uint8(v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2256_, lean_object* v_rootDeps_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___y_2261_; lean_object* v___y_2267_; uint8_t v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2275_; uint8_t v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; uint8_t v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v_lakeEnv_2297_; lean_object* v_lakeArgs_x3f_2298_; lean_object* v_packages_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v_baseName_2302_; lean_object* v_dir_2303_; lean_object* v_config_2304_; lean_object* v___x_2305_; lean_object* v_rootToolchainFile_2306_; uint8_t v___y_2308_; uint8_t v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2452_; uint8_t v___y_2453_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_lakeEnv_2297_ = lean_ctor_get(v_ws_2256_, 0);
lean_inc_ref(v_lakeEnv_2297_);
v_lakeArgs_x3f_2298_ = lean_ctor_get(v_ws_2256_, 3);
lean_inc(v_lakeArgs_x3f_2298_);
v_packages_2299_ = lean_ctor_get(v_ws_2256_, 4);
lean_inc_ref(v_packages_2299_);
lean_dec_ref(v_ws_2256_);
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = lean_array_fget(v_packages_2299_, v___x_2300_);
lean_dec_ref(v_packages_2299_);
v_baseName_2302_ = lean_ctor_get(v___x_2301_, 1);
lean_inc(v_baseName_2302_);
v_dir_2303_ = lean_ctor_get(v___x_2301_, 4);
lean_inc_ref_n(v_dir_2303_, 3);
v_config_2304_ = lean_ctor_get(v___x_2301_, 6);
lean_inc_ref(v_config_2304_);
lean_dec(v___x_2301_);
v___x_2305_ = l_Lake_toolchainFileName;
v_rootToolchainFile_2306_ = l_Lake_joinRelative(v_dir_2303_, v___x_2305_);
v___x_2457_ = l_System_FilePath_join(v_dir_2303_, v___x_2305_);
v___x_2458_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2457_);
lean_dec_ref(v___x_2457_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2517_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2517_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2517_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v_src_2464_; lean_object* v_tc_x3f_2465_; lean_object* v_clashes_2466_; uint8_t v_fixed_2467_; lean_object* v___y_2491_; uint8_t v_fixedToolchain_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v_fixedToolchain_2505_ = lean_ctor_get_uint8(v_config_2304_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_2304_);
v___x_2506_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_2507_ = lean_array_get_size(v_rootDeps_2257_);
v___x_2508_ = lean_nat_dec_lt(v___x_2300_, v___x_2507_);
if (v___x_2508_ == 0)
{
lean_dec_ref(v_dir_2303_);
lean_inc(v_a_2459_);
v_src_2464_ = v_baseName_2302_;
v_tc_x3f_2465_ = v_a_2459_;
v_clashes_2466_ = v___x_2506_;
v_fixed_2467_ = v_fixedToolchain_2505_;
goto v___jp_2463_;
}
else
{
lean_object* v___x_2509_; uint8_t v___x_2510_; 
lean_inc(v_a_2459_);
lean_inc(v_baseName_2302_);
v___x_2509_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2509_, 0, v_baseName_2302_);
lean_ctor_set(v___x_2509_, 1, v_a_2459_);
lean_ctor_set(v___x_2509_, 2, v___x_2506_);
lean_ctor_set_uint8(v___x_2509_, sizeof(void*)*3, v_fixedToolchain_2505_);
v___x_2510_ = lean_nat_dec_le(v___x_2507_, v___x_2507_);
if (v___x_2510_ == 0)
{
if (v___x_2508_ == 0)
{
lean_dec_ref_known(v___x_2509_, 3);
lean_dec_ref(v_dir_2303_);
lean_inc(v_a_2459_);
v_src_2464_ = v_baseName_2302_;
v_tc_x3f_2465_ = v_a_2459_;
v_clashes_2466_ = v___x_2506_;
v_fixed_2467_ = v_fixedToolchain_2505_;
goto v___jp_2463_;
}
else
{
size_t v___x_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
lean_dec(v_baseName_2302_);
v___x_2511_ = ((size_t)0ULL);
v___x_2512_ = lean_usize_of_nat(v___x_2507_);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2303_, v_rootDeps_2257_, v___x_2511_, v___x_2512_, v___x_2509_, v_a_2258_);
v___y_2491_ = v___x_2513_;
goto v___jp_2490_;
}
}
else
{
size_t v___x_2514_; size_t v___x_2515_; lean_object* v___x_2516_; 
lean_dec(v_baseName_2302_);
v___x_2514_ = ((size_t)0ULL);
v___x_2515_ = lean_usize_of_nat(v___x_2507_);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2303_, v_rootDeps_2257_, v___x_2514_, v___x_2515_, v___x_2509_, v_a_2258_);
v___y_2491_ = v___x_2516_;
goto v___jp_2490_;
}
}
v___jp_2463_:
{
lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = lean_array_get_size(v_clashes_2466_);
v___x_2469_ = lean_nat_dec_lt(v___x_2300_, v___x_2468_);
if (v___x_2469_ == 0)
{
lean_dec_ref(v_clashes_2466_);
lean_dec(v_src_2464_);
if (lean_obj_tag(v_tc_x3f_2465_) == 1)
{
if (lean_obj_tag(v_a_2459_) == 0)
{
lean_object* v_val_2470_; 
lean_del_object(v___x_2461_);
v_val_2470_ = lean_ctor_get(v_tc_x3f_2465_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v_tc_x3f_2465_, 1);
v___y_2452_ = v_val_2470_;
v___y_2453_ = v___x_2469_;
goto v___jp_2451_;
}
else
{
lean_object* v_val_2471_; lean_object* v_val_2472_; uint8_t v___x_2473_; 
v_val_2471_ = lean_ctor_get(v_tc_x3f_2465_, 0);
lean_inc_n(v_val_2471_, 2);
lean_dec_ref_known(v_tc_x3f_2465_, 1);
v_val_2472_ = lean_ctor_get(v_a_2459_, 0);
lean_inc(v_val_2472_);
lean_dec_ref_known(v_a_2459_, 1);
v___x_2473_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2472_, v_val_2471_);
if (v___x_2473_ == 0)
{
lean_del_object(v___x_2461_);
v___y_2452_ = v_val_2471_;
v___y_2453_ = v___x_2473_;
goto v___jp_2451_;
}
else
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
lean_dec(v_val_2471_);
lean_dec_ref(v_rootToolchainFile_2306_);
lean_dec(v_lakeArgs_x3f_2298_);
lean_dec_ref(v_lakeEnv_2297_);
v___x_2474_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2258_);
v___x_2475_ = lean_apply_2(v_a_2258_, v___x_2474_, lean_box(0));
v___x_2476_ = lean_box(0);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2476_);
v___x_2478_ = v___x_2461_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
lean_dec(v_tc_x3f_2465_);
lean_dec(v_a_2459_);
lean_dec_ref(v_rootToolchainFile_2306_);
lean_dec(v_lakeArgs_x3f_2298_);
lean_dec_ref(v_lakeEnv_2297_);
v___x_2480_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2258_);
v___x_2481_ = lean_apply_2(v_a_2258_, v___x_2480_, lean_box(0));
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2481_);
v___x_2483_ = v___x_2461_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
else
{
lean_del_object(v___x_2461_);
lean_dec(v_a_2459_);
lean_dec_ref(v_rootToolchainFile_2306_);
lean_dec(v_lakeArgs_x3f_2298_);
lean_dec_ref(v_lakeEnv_2297_);
if (lean_obj_tag(v_tc_x3f_2465_) == 1)
{
if (v_fixed_2467_ == 0)
{
lean_object* v_val_2485_; lean_object* v___x_2486_; 
v_val_2485_ = lean_ctor_get(v_tc_x3f_2465_, 0);
lean_inc(v_val_2485_);
lean_dec_ref_known(v_tc_x3f_2465_, 1);
v___x_2486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2289_ = v___x_2469_;
v___y_2290_ = v___x_2468_;
v___y_2291_ = v_clashes_2466_;
v___y_2292_ = v_val_2485_;
v___y_2293_ = v_src_2464_;
v___y_2294_ = v___x_2486_;
goto v___jp_2288_;
}
else
{
lean_object* v_val_2487_; lean_object* v___x_2488_; 
v_val_2487_ = lean_ctor_get(v_tc_x3f_2465_, 0);
lean_inc(v_val_2487_);
lean_dec_ref_known(v_tc_x3f_2465_, 1);
v___x_2488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2289_ = v___x_2469_;
v___y_2290_ = v___x_2468_;
v___y_2291_ = v_clashes_2466_;
v___y_2292_ = v_val_2487_;
v___y_2293_ = v_src_2464_;
v___y_2294_ = v___x_2488_;
goto v___jp_2288_;
}
}
else
{
lean_object* v___x_2489_; 
lean_dec(v_tc_x3f_2465_);
lean_dec(v_src_2464_);
v___x_2489_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_2267_ = v___x_2468_;
v___y_2268_ = v___x_2469_;
v___y_2269_ = v_clashes_2466_;
v___y_2270_ = v___x_2489_;
goto v___jp_2266_;
}
}
}
v___jp_2490_:
{
if (lean_obj_tag(v___y_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v_src_2493_; lean_object* v_tc_x3f_2494_; lean_object* v_clashes_2495_; uint8_t v_fixed_2496_; 
v_a_2492_ = lean_ctor_get(v___y_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___y_2491_, 1);
v_src_2493_ = lean_ctor_get(v_a_2492_, 0);
lean_inc(v_src_2493_);
v_tc_x3f_2494_ = lean_ctor_get(v_a_2492_, 1);
lean_inc(v_tc_x3f_2494_);
v_clashes_2495_ = lean_ctor_get(v_a_2492_, 2);
lean_inc_ref(v_clashes_2495_);
v_fixed_2496_ = lean_ctor_get_uint8(v_a_2492_, sizeof(void*)*3);
lean_dec(v_a_2492_);
v_src_2464_ = v_src_2493_;
v_tc_x3f_2465_ = v_tc_x3f_2494_;
v_clashes_2466_ = v_clashes_2495_;
v_fixed_2467_ = v_fixed_2496_;
goto v___jp_2463_;
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_del_object(v___x_2461_);
lean_dec(v_a_2459_);
lean_dec_ref(v_rootToolchainFile_2306_);
lean_dec(v_lakeArgs_x3f_2298_);
lean_dec_ref(v_lakeEnv_2297_);
v_a_2497_ = lean_ctor_get(v___y_2491_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___y_2491_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___y_2491_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___y_2491_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2530_; 
lean_dec_ref(v_rootToolchainFile_2306_);
lean_dec_ref(v_config_2304_);
lean_dec_ref(v_dir_2303_);
lean_dec(v_baseName_2302_);
lean_dec(v_lakeArgs_x3f_2298_);
lean_dec_ref(v_lakeEnv_2297_);
v_a_2518_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2520_ = v___x_2458_;
v_isShared_2521_ = v_isSharedCheck_2530_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2458_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2530_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; uint8_t v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2522_ = lean_io_error_to_string(v_a_2518_);
v___x_2523_ = 3;
v___x_2524_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2524_, 0, v___x_2522_);
lean_ctor_set_uint8(v___x_2524_, sizeof(void*)*1, v___x_2523_);
lean_inc_ref(v_a_2258_);
v___x_2525_ = lean_apply_2(v_a_2258_, v___x_2524_, lean_box(0));
v___x_2526_ = lean_box(0);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2526_);
v___x_2528_ = v___x_2520_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
v___jp_2260_:
{
uint8_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2262_ = 2;
v___x_2263_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2263_, 0, v___y_2261_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*1, v___x_2262_);
lean_inc_ref(v_a_2258_);
v___x_2264_ = lean_apply_2(v_a_2258_, v___x_2263_, lean_box(0));
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
v___jp_2266_:
{
if (v___y_2268_ == 0)
{
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2267_);
v___y_2261_ = v___y_2270_;
goto v___jp_2260_;
}
else
{
size_t v___x_2271_; size_t v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = lean_usize_of_nat(v___y_2267_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2267_, v___y_2269_, v___x_2271_, v___x_2272_, v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2267_);
v___y_2261_ = v___x_2273_;
goto v___jp_2260_;
}
}
v___jp_2274_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_inc_ref(v___y_2280_);
v___x_2282_ = lean_string_append(v___y_2280_, v___y_2281_);
lean_dec_ref(v___y_2281_);
v___x_2283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2284_ = lean_string_append(v___x_2282_, v___x_2283_);
v___x_2285_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2279_, v___y_2276_);
v___x_2286_ = lean_string_append(v___x_2284_, v___x_2285_);
lean_dec_ref(v___x_2285_);
v___x_2287_ = lean_string_append(v___x_2286_, v___y_2278_);
v___y_2267_ = v___y_2275_;
v___y_2268_ = v___y_2276_;
v___y_2269_ = v___y_2277_;
v___y_2270_ = v___x_2287_;
goto v___jp_2266_;
}
v___jp_2288_:
{
lean_object* v___x_2295_; lean_object* v_toString_2296_; 
v___x_2295_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_2296_ = lean_ctor_get(v___y_2292_, 0);
lean_inc_ref(v_toString_2296_);
lean_dec_ref(v___y_2292_);
v___y_2275_ = v___y_2290_;
v___y_2276_ = v___y_2289_;
v___y_2277_ = v___y_2291_;
v___y_2278_ = v___y_2294_;
v___y_2279_ = v___y_2293_;
v___y_2280_ = v___x_2295_;
v___y_2281_ = v_toString_2296_;
goto v___jp_2274_;
}
v___jp_2307_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_inc_ref(v___y_2310_);
v___x_2312_ = lean_string_append(v___y_2310_, v___y_2311_);
v___x_2313_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2314_ = lean_string_append(v___x_2312_, v___x_2313_);
v___x_2315_ = 1;
v___x_2316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*1, v___x_2315_);
lean_inc_ref(v_a_2258_);
v___x_2317_ = lean_apply_2(v_a_2258_, v___x_2316_, lean_box(0));
v___x_2318_ = l_IO_FS_writeFile(v_rootToolchainFile_2306_, v___y_2311_);
lean_dec_ref(v_rootToolchainFile_2306_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_dec_ref_known(v___x_2318_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2298_) == 1)
{
lean_object* v_elan_x3f_2319_; 
v_elan_x3f_2319_ = lean_ctor_get(v_lakeEnv_2297_, 2);
if (lean_obj_tag(v_elan_x3f_2319_) == 1)
{
lean_object* v_val_2320_; lean_object* v_val_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v_elan_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_val_2320_ = lean_ctor_get(v_lakeArgs_x3f_2298_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v_lakeArgs_x3f_2298_, 1);
v_val_2321_ = lean_ctor_get(v_elan_x3f_2319_, 0);
v___x_2322_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_2258_);
v___x_2323_ = lean_apply_2(v_a_2258_, v___x_2322_, lean_box(0));
v___x_2324_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_2325_ = lean_ctor_get(v_val_2321_, 1);
lean_inc_ref(v_elan_2325_);
v___x_2326_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_2327_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_2328_ = lean_array_push(v___x_2327_, v___y_2311_);
v___x_2329_ = lean_array_push(v___x_2328_, v___x_2326_);
v___x_2330_ = l_Array_append___redArg(v___x_2329_, v_val_2320_);
lean_dec(v_val_2320_);
v___x_2331_ = lean_box(0);
v___x_2332_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2297_);
v___x_2333_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2333_, 0, v___x_2324_);
lean_ctor_set(v___x_2333_, 1, v_elan_2325_);
lean_ctor_set(v___x_2333_, 2, v___x_2330_);
lean_ctor_set(v___x_2333_, 3, v___x_2331_);
lean_ctor_set(v___x_2333_, 4, v___x_2332_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*5, v___y_2309_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*5 + 1, v___y_2308_);
v___x_2334_ = lean_io_process_spawn(v___x_2333_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = lean_io_process_child_wait(v___x_2324_, v_a_2335_);
lean_dec(v_a_2335_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; uint32_t v___x_2338_; uint8_t v___x_2339_; lean_object* v___x_2340_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = lean_unbox_uint32(v_a_2337_);
lean_dec(v_a_2337_);
v___x_2339_ = lean_uint32_to_uint8(v___x_2338_);
v___x_2340_ = lean_io_exit(v___x_2339_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2361_; 
v_a_2349_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2351_ = v___x_2340_;
v_isShared_2352_ = v_isSharedCheck_2361_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2340_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2361_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2353_ = lean_io_error_to_string(v_a_2349_);
v___x_2354_ = 3;
v___x_2355_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set_uint8(v___x_2355_, sizeof(void*)*1, v___x_2354_);
lean_inc_ref(v_a_2258_);
v___x_2356_ = lean_apply_2(v_a_2258_, v___x_2355_, lean_box(0));
v___x_2357_ = lean_box(0);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2357_);
v___x_2359_ = v___x_2351_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2374_; 
v_a_2362_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2364_ = v___x_2336_;
v_isShared_2365_ = v_isSharedCheck_2374_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2336_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2374_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2366_ = lean_io_error_to_string(v_a_2362_);
v___x_2367_ = 3;
v___x_2368_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*1, v___x_2367_);
lean_inc_ref(v_a_2258_);
v___x_2369_ = lean_apply_2(v_a_2258_, v___x_2368_, lean_box(0));
v___x_2370_ = lean_box(0);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2370_);
v___x_2372_ = v___x_2364_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2387_; 
v_a_2375_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2377_ = v___x_2334_;
v_isShared_2378_ = v_isSharedCheck_2387_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2334_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2387_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2379_ = lean_io_error_to_string(v_a_2375_);
v___x_2380_ = 3;
v___x_2381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*1, v___x_2380_);
lean_inc_ref(v_a_2258_);
v___x_2382_ = lean_apply_2(v_a_2258_, v___x_2381_, lean_box(0));
v___x_2383_ = lean_box(0);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2383_);
v___x_2385_ = v___x_2377_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; 
lean_dec_ref_known(v_lakeArgs_x3f_2298_, 1);
lean_dec_ref(v___y_2311_);
lean_dec_ref(v_lakeEnv_2297_);
v___x_2388_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_2258_);
v___x_2389_ = lean_apply_2(v_a_2258_, v___x_2388_, lean_box(0));
v___x_2390_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11);
v___x_2391_ = lean_io_exit(v___x_2390_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2412_; 
v_a_2400_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2402_ = v___x_2391_;
v_isShared_2403_ = v_isSharedCheck_2412_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2391_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2412_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2404_ = lean_io_error_to_string(v_a_2400_);
v___x_2405_ = 3;
v___x_2406_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*1, v___x_2405_);
lean_inc_ref(v_a_2258_);
v___x_2407_ = lean_apply_2(v_a_2258_, v___x_2406_, lean_box(0));
v___x_2408_ = lean_box(0);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2408_);
v___x_2410_ = v___x_2402_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; 
lean_dec_ref(v___y_2311_);
lean_dec(v_lakeArgs_x3f_2298_);
lean_dec_ref(v_lakeEnv_2297_);
v___x_2413_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
lean_inc_ref(v_a_2258_);
v___x_2414_ = lean_apply_2(v_a_2258_, v___x_2413_, lean_box(0));
v___x_2415_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11);
v___x_2416_ = lean_io_exit(v___x_2415_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2437_; 
v_a_2425_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2427_ = v___x_2416_;
v_isShared_2428_ = v_isSharedCheck_2437_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2416_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2437_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; uint8_t v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2429_ = lean_io_error_to_string(v_a_2425_);
v___x_2430_ = 3;
v___x_2431_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set_uint8(v___x_2431_, sizeof(void*)*1, v___x_2430_);
lean_inc_ref(v_a_2258_);
v___x_2432_ = lean_apply_2(v_a_2258_, v___x_2431_, lean_box(0));
v___x_2433_ = lean_box(0);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2433_);
v___x_2435_ = v___x_2427_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2450_; 
lean_dec_ref(v___y_2311_);
lean_dec(v_lakeArgs_x3f_2298_);
lean_dec_ref(v_lakeEnv_2297_);
v_a_2438_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2440_ = v___x_2318_;
v_isShared_2441_ = v_isSharedCheck_2450_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2318_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2450_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; uint8_t v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2442_ = lean_io_error_to_string(v_a_2438_);
v___x_2443_ = 3;
v___x_2444_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2444_, 0, v___x_2442_);
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*1, v___x_2443_);
lean_inc_ref(v_a_2258_);
v___x_2445_ = lean_apply_2(v_a_2258_, v___x_2444_, lean_box(0));
v___x_2446_ = lean_box(0);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2446_);
v___x_2448_ = v___x_2440_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
v___jp_2451_:
{
uint8_t v___x_2454_; lean_object* v___x_2455_; lean_object* v_toString_2456_; 
v___x_2454_ = 1;
v___x_2455_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_2456_ = lean_ctor_get(v___y_2452_, 0);
lean_inc_ref(v_toString_2456_);
lean_dec_ref(v___y_2452_);
v___y_2308_ = v___y_2453_;
v___y_2309_ = v___x_2454_;
v___y_2310_ = v___x_2455_;
v___y_2311_ = v_toString_2456_;
goto v___jp_2307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2531_, lean_object* v_rootDeps_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2531_, v_rootDeps_2532_, v_a_2533_);
lean_dec_ref(v_a_2533_);
lean_dec_ref(v_rootDeps_2532_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2536_, lean_object* v_dep_2537_, lean_object* v_ws_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2538_, v_pkg_2536_, v_dep_2537_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v_fst_2544_; lean_object* v_snd_2545_; lean_object* v___x_2546_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v___x_2542_, 1);
v_fst_2544_ = lean_ctor_get(v_a_2543_, 0);
lean_inc_n(v_fst_2544_, 2);
v_snd_2545_ = lean_ctor_get(v_a_2543_, 1);
lean_inc(v_snd_2545_);
lean_dec(v_a_2543_);
v___x_2546_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2544_, v_snd_2545_, v_a_2540_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2563_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2563_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2563_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v_snd_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2561_; 
v_snd_2551_ = lean_ctor_get(v_a_2547_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_a_2547_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v_a_2547_, 0);
lean_dec(v_unused_2562_);
v___x_2553_ = v_a_2547_;
v_isShared_2554_ = v_isSharedCheck_2561_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_snd_2551_);
lean_dec(v_a_2547_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2561_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v_fst_2544_);
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_fst_2544_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_snd_2551_);
v___x_2556_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2558_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2556_);
v___x_2558_ = v___x_2549_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec(v_fst_2544_);
v_a_2564_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2546_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2546_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2572_, lean_object* v_dep_2573_, lean_object* v_ws_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2572_, v_dep_2573_, v_ws_2574_, v_a_2575_, v_a_2576_);
lean_dec_ref(v_a_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2579_, lean_object* v_ws_2580_, lean_object* v_pkg_2581_, lean_object* v_dep_2582_, lean_object* v_a_2583_){
_start:
{
uint8_t v___y_2586_; lean_object* v___y_2587_; lean_object* v_name_2617_; lean_object* v___x_2618_; 
v_name_2617_ = lean_ctor_get(v_dep_2582_, 0);
v___x_2618_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2583_, v_name_2617_);
if (lean_obj_tag(v___x_2618_) == 1)
{
lean_object* v_val_2619_; lean_object* v_lakeEnv_2620_; lean_object* v_packages_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v_config_2624_; lean_object* v_dir_2625_; lean_object* v_toWorkspaceConfig_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec_ref(v_dep_2582_);
lean_dec_ref(v_pkg_2581_);
v_val_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_val_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v_lakeEnv_2620_ = lean_ctor_get(v_ws_2580_, 0);
lean_inc_ref(v_lakeEnv_2620_);
v_packages_2621_ = lean_ctor_get(v_ws_2580_, 4);
lean_inc_ref(v_packages_2621_);
lean_dec_ref(v_ws_2580_);
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_array_fget(v_packages_2621_, v___x_2622_);
lean_dec_ref(v_packages_2621_);
v_config_2624_ = lean_ctor_get(v___x_2623_, 6);
lean_inc_ref(v_config_2624_);
v_dir_2625_ = lean_ctor_get(v___x_2623_, 4);
lean_inc_ref(v_dir_2625_);
lean_dec(v___x_2623_);
v_toWorkspaceConfig_2626_ = lean_ctor_get(v_config_2624_, 0);
lean_inc_ref(v_toWorkspaceConfig_2626_);
lean_dec_ref(v_config_2624_);
v___x_2627_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2626_);
v___x_2628_ = l_Lake_PackageEntry_materialize(v_val_2619_, v_lakeEnv_2620_, v_dir_2625_, v___x_2627_, v___y_2579_);
lean_dec_ref(v_lakeEnv_2620_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2637_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2637_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2637_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v_a_2629_);
lean_ctor_set(v___x_2633_, 1, v_a_2583_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2633_);
v___x_2635_ = v___x_2631_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_a_2583_);
v_a_2638_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2628_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2628_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_wsIdx_2646_; lean_object* v_relDir_2647_; uint8_t v___y_2649_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
lean_dec(v___x_2618_);
v_wsIdx_2646_ = lean_ctor_get(v_pkg_2581_, 0);
lean_inc(v_wsIdx_2646_);
v_relDir_2647_ = lean_ctor_get(v_pkg_2581_, 5);
lean_inc_ref(v_relDir_2647_);
lean_dec_ref(v_pkg_2581_);
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = lean_nat_dec_eq(v_wsIdx_2646_, v___x_2653_);
lean_dec(v_wsIdx_2646_);
if (v___x_2654_ == 0)
{
uint8_t v___x_2655_; 
v___x_2655_ = 1;
v___y_2649_ = v___x_2655_;
goto v___jp_2648_;
}
else
{
uint8_t v___x_2656_; 
v___x_2656_ = 0;
v___y_2649_ = v___x_2656_;
goto v___jp_2648_;
}
v___jp_2648_:
{
lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2651_ = lean_string_dec_eq(v_relDir_2647_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lake_joinRelative(v_relDir_2647_, v___x_2650_);
v___y_2586_ = v___y_2649_;
v___y_2587_ = v___x_2652_;
goto v___jp_2585_;
}
else
{
v___y_2586_ = v___y_2649_;
v___y_2587_ = v_relDir_2647_;
goto v___jp_2585_;
}
}
}
v___jp_2585_:
{
lean_object* v_lakeEnv_2588_; lean_object* v_packages_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v_config_2592_; lean_object* v_dir_2593_; lean_object* v_toWorkspaceConfig_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_lakeEnv_2588_ = lean_ctor_get(v_ws_2580_, 0);
lean_inc_ref(v_lakeEnv_2588_);
v_packages_2589_ = lean_ctor_get(v_ws_2580_, 4);
lean_inc_ref(v_packages_2589_);
lean_dec_ref(v_ws_2580_);
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = lean_array_fget(v_packages_2589_, v___x_2590_);
lean_dec_ref(v_packages_2589_);
v_config_2592_ = lean_ctor_get(v___x_2591_, 6);
lean_inc_ref(v_config_2592_);
v_dir_2593_ = lean_ctor_get(v___x_2591_, 4);
lean_inc_ref(v_dir_2593_);
lean_dec(v___x_2591_);
v_toWorkspaceConfig_2594_ = lean_ctor_get(v_config_2592_, 0);
lean_inc_ref(v_toWorkspaceConfig_2594_);
lean_dec_ref(v_config_2592_);
v___x_2595_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2594_);
v___x_2596_ = l_Lake_Dependency_materialize(v_dep_2582_, v___y_2586_, v_lakeEnv_2588_, v_dir_2593_, v___x_2595_, v___y_2587_, v___y_2579_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2608_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2608_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2608_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v_manifestEntry_2601_; lean_object* v_name_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
v_manifestEntry_2601_ = lean_ctor_get(v_a_2597_, 4);
v_name_2602_ = lean_ctor_get(v_manifestEntry_2601_, 0);
lean_inc_ref(v_manifestEntry_2601_);
lean_inc(v_name_2602_);
v___x_2603_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2602_, v_manifestEntry_2601_, v_a_2583_);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v_a_2597_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2604_);
v___x_2606_ = v___x_2599_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_a_2583_);
v_a_2609_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2596_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2596_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2657_, lean_object* v_ws_2658_, lean_object* v_pkg_2659_, lean_object* v_dep_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2657_, v_ws_2658_, v_pkg_2659_, v_dep_2660_, v_a_2661_);
lean_dec_ref(v___y_2657_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2664_, lean_object* v_dep_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v_manifestEntry_2668_; lean_object* v_pkgDir_2669_; lean_object* v_name_2670_; lean_object* v_manifestFile_x3f_2671_; lean_object* v___y_2673_; lean_object* v_fst_2674_; lean_object* v_snd_2675_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v_val_2727_; lean_object* v___y_2743_; 
v_manifestEntry_2668_ = lean_ctor_get(v_dep_2665_, 4);
v_pkgDir_2669_ = lean_ctor_get(v_dep_2665_, 0);
v_name_2670_ = lean_ctor_get(v_manifestEntry_2668_, 0);
v_manifestFile_x3f_2671_ = lean_ctor_get(v_manifestEntry_2668_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2671_) == 0)
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2669_);
v___x_2764_ = l_Lake_joinRelative(v_pkgDir_2669_, v___x_2763_);
v___y_2743_ = v___x_2764_;
goto v___jp_2742_;
}
else
{
lean_object* v_val_2765_; lean_object* v___x_2766_; 
v_val_2765_ = lean_ctor_get(v_manifestFile_x3f_2671_, 0);
lean_inc(v_val_2765_);
lean_inc_ref(v_pkgDir_2669_);
v___x_2766_ = l_Lake_joinRelative(v_pkgDir_2669_, v_val_2765_);
v___y_2743_ = v___x_2766_;
goto v___jp_2742_;
}
v___jp_2672_:
{
if (lean_obj_tag(v_fst_2674_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2705_; 
lean_inc(v_name_2670_);
lean_dec_ref(v_dep_2665_);
v_a_2676_ = lean_ctor_get(v_fst_2674_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_fst_2674_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2678_ = v_fst_2674_;
v_isShared_2679_ = v_isSharedCheck_2705_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v_fst_2674_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2705_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
if (lean_obj_tag(v_a_2676_) == 11)
{
uint8_t v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_dec_ref_known(v_a_2676_, 2);
v___x_2680_ = 0;
v___x_2681_ = l_Lean_Name_toString(v_name_2670_, v___x_2680_);
v___x_2682_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2683_ = lean_string_append(v___x_2681_, v___x_2682_);
v___x_2684_ = lean_string_append(v___x_2683_, v___y_2673_);
lean_dec_ref(v___y_2673_);
v___x_2685_ = 2;
v___x_2686_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set_uint8(v___x_2686_, sizeof(void*)*1, v___x_2685_);
v___x_2687_ = lean_apply_2(v___y_2664_, v___x_2686_, lean_box(0));
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
lean_ctor_set(v___x_2688_, 1, v_snd_2675_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2688_);
v___x_2690_ = v___x_2678_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
else
{
uint8_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
lean_dec_ref(v___y_2673_);
v___x_2692_ = 0;
v___x_2693_ = l_Lean_Name_toString(v_name_2670_, v___x_2692_);
v___x_2694_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2695_ = lean_string_append(v___x_2693_, v___x_2694_);
v___x_2696_ = lean_io_error_to_string(v_a_2676_);
v___x_2697_ = lean_string_append(v___x_2695_, v___x_2696_);
lean_dec_ref(v___x_2696_);
v___x_2698_ = 2;
v___x_2699_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*1, v___x_2698_);
v___x_2700_ = lean_apply_2(v___y_2664_, v___x_2699_, lean_box(0));
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v_snd_2675_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2701_);
v___x_2703_ = v___x_2678_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___y_2664_);
v_a_2706_ = lean_ctor_get(v_fst_2674_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_fst_2674_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2708_ = v_fst_2674_;
v_isShared_2709_ = v_isSharedCheck_2722_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v_fst_2674_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2722_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v_packages_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v_packages_2710_ = lean_ctor_get(v_a_2706_, 3);
lean_inc_ref(v_packages_2710_);
lean_dec(v_a_2706_);
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = lean_array_get_size(v_packages_2710_);
v___x_2713_ = lean_box(0);
v___x_2714_ = lean_nat_dec_lt(v___x_2711_, v___x_2712_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
lean_dec_ref(v_packages_2710_);
lean_dec_ref(v_dep_2665_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v_snd_2675_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set_tag(v___x_2708_, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2715_);
v___x_2717_ = v___x_2708_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
else
{
size_t v___x_2719_; size_t v___x_2720_; lean_object* v___x_2721_; 
lean_del_object(v___x_2708_);
v___x_2719_ = ((size_t)0ULL);
v___x_2720_ = lean_usize_of_nat(v___x_2712_);
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2665_, v_packages_2710_, v___x_2719_, v___x_2720_, v___x_2713_, v_snd_2675_);
lean_dec_ref(v_packages_2710_);
return v___x_2721_;
}
}
}
}
v___jp_2723_:
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = lean_array_get_size(v___y_2724_);
v___x_2729_ = lean_nat_dec_lt(v___y_2725_, v___x_2728_);
if (v___x_2729_ == 0)
{
v___y_2673_ = v___y_2726_;
v_fst_2674_ = v_val_2727_;
v_snd_2675_ = v_a_2666_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2730_; size_t v___x_2731_; size_t v___x_2732_; lean_object* v___x_2733_; 
v___x_2730_ = lean_box(0);
v___x_2731_ = ((size_t)0ULL);
v___x_2732_ = lean_usize_of_nat(v___x_2728_);
v___x_2733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2724_, v___x_2731_, v___x_2732_, v___x_2730_, v___y_2664_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_dec_ref_known(v___x_2733_, 1);
v___y_2673_ = v___y_2726_;
v_fst_2674_ = v_val_2727_;
v_snd_2675_ = v_a_2666_;
goto v___jp_2672_;
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec_ref(v_val_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_a_2666_);
lean_dec_ref(v_dep_2665_);
lean_dec_ref(v___y_2664_);
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
v___jp_2742_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = lean_unsigned_to_nat(0u);
v___x_2745_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2743_);
v___x_2746_ = l_Lake_Manifest_load(v___y_2743_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set_tag(v___x_2749_, 1);
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2744_;
v___y_2726_ = v___y_2743_;
v_val_2727_ = v___x_2752_;
goto v___jp_2723_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_a_2755_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2746_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2746_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set_tag(v___x_2757_, 0);
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2744_;
v___y_2726_ = v___y_2743_;
v_val_2727_ = v___x_2760_;
goto v___jp_2723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2767_, lean_object* v_dep_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2767_, v_dep_2768_, v_a_2769_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2776_, v___y_2774_, v___y_2772_, v___y_2773_, v___y_2775_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v_fst_2780_; lean_object* v_snd_2781_; lean_object* v___x_2782_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v_fst_2780_ = lean_ctor_get(v_a_2779_, 0);
lean_inc_n(v_fst_2780_, 2);
v_snd_2781_ = lean_ctor_get(v_a_2779_, 1);
lean_inc(v_snd_2781_);
lean_dec(v_a_2779_);
v___x_2782_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2776_, v_fst_2780_, v_snd_2781_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2799_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2799_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2799_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v_snd_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2797_; 
v_snd_2787_ = lean_ctor_get(v_a_2783_, 1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_a_2783_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; 
v_unused_2798_ = lean_ctor_get(v_a_2783_, 0);
lean_dec(v_unused_2798_);
v___x_2789_ = v_a_2783_;
v_isShared_2790_ = v_isSharedCheck_2797_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_snd_2787_);
lean_dec(v_a_2783_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2797_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 0, v_fst_2780_);
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_fst_2780_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_snd_2787_);
v___x_2792_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2794_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2792_);
v___x_2794_ = v___x_2785_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_fst_2780_);
v_a_2800_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2782_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2782_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
else
{
lean_dec_ref(v___y_2776_);
return v___x_2778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(lean_object* v_toUpdate_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v_entries_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___y_2823_; 
if (lean_obj_tag(v_toUpdate_2815_) == 0)
{
lean_object* v_depConfigs_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v_depConfigs_2865_ = lean_ctor_get(v___x_2816_, 12);
v___x_2866_ = l_Lean_NameSet_empty;
v___x_2867_ = lean_array_get_size(v_depConfigs_2865_);
v___x_2868_ = lean_nat_dec_lt(v___x_2817_, v___x_2867_);
if (v___x_2868_ == 0)
{
v___y_2823_ = v___x_2866_;
goto v___jp_2822_;
}
else
{
size_t v___x_2869_; size_t v___x_2870_; lean_object* v___x_2871_; 
v___x_2869_ = ((size_t)0ULL);
v___x_2870_ = lean_usize_of_nat(v___x_2867_);
v___x_2871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_2865_, v___x_2869_, v___x_2870_, v___x_2866_);
v___y_2823_ = v___x_2871_;
goto v___jp_2822_;
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v___y_2819_);
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
return v___x_2874_;
}
v___jp_2822_:
{
size_t v_sz_2824_; size_t v___x_2825_; lean_object* v___x_2826_; 
v_sz_2824_ = lean_array_size(v_entries_2818_);
v___x_2825_ = ((size_t)0ULL);
v___x_2826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_entries_2818_, v_sz_2824_, v___x_2825_, v___y_2823_, v___y_2819_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v_fst_2828_; lean_object* v_snd_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
v_fst_2828_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_fst_2828_);
v_snd_2829_ = lean_ctor_get(v_a_2827_, 1);
lean_inc(v_snd_2829_);
lean_dec(v_a_2827_);
v___x_2830_ = lean_box(0);
v___x_2831_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_2828_, v___x_2830_, v_toUpdate_2815_, v_snd_2829_, v___y_2820_);
lean_dec(v_fst_2828_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2848_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2848_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2848_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v_snd_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2846_; 
v_snd_2836_ = lean_ctor_get(v_a_2832_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_a_2832_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v_a_2832_, 0);
lean_dec(v_unused_2847_);
v___x_2838_ = v_a_2832_;
v_isShared_2839_ = v_isSharedCheck_2846_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_snd_2836_);
lean_dec(v_a_2832_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2846_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2830_);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_snd_2836_);
v___x_2841_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2843_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2841_);
v___x_2843_ = v___x_2834_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
v_a_2849_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2831_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2831_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v_toUpdate_2815_);
v_a_2857_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2826_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2826_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0___boxed(lean_object* v_toUpdate_2875_, lean_object* v___x_2876_, lean_object* v___x_2877_, lean_object* v_entries_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2875_, v___x_2876_, v___x_2877_, v_entries_2878_, v___y_2879_, v___y_2880_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v_entries_2878_);
lean_dec(v___x_2877_);
lean_dec_ref(v___x_2876_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2883_, lean_object* v_ws_2884_, lean_object* v_toUpdate_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___y_2889_; lean_object* v___y_2894_; lean_object* v_fst_2895_; lean_object* v_snd_2896_; lean_object* v_packages_2915_; lean_object* v___x_2916_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v_val_2921_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___x_2957_; lean_object* v_baseName_2958_; lean_object* v_dir_2959_; lean_object* v_config_2960_; lean_object* v_relManifestFile_2961_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; uint8_t v_fst_2966_; lean_object* v_snd_2967_; lean_object* v_packagesDir_x3f_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; uint8_t v___x_3011_; lean_object* v_rootName_3012_; lean_object* v_fst_3014_; lean_object* v_snd_3015_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v_val_3082_; lean_object* v___x_3096_; 
v_packages_2915_ = lean_ctor_get(v_ws_2884_, 4);
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2957_ = lean_array_fget_borrowed(v_packages_2915_, v___x_2916_);
v_baseName_2958_ = lean_ctor_get(v___x_2957_, 1);
v_dir_2959_ = lean_ctor_get(v___x_2957_, 4);
v_config_2960_ = lean_ctor_get(v___x_2957_, 6);
v_relManifestFile_2961_ = lean_ctor_get(v___x_2957_, 9);
v___x_3011_ = 0;
lean_inc(v_baseName_2958_);
v_rootName_3012_ = l_Lean_Name_toString(v_baseName_2958_, v___x_3011_);
lean_inc_ref(v_relManifestFile_2961_);
lean_inc_ref(v_dir_2959_);
v___x_3079_ = l_Lake_joinRelative(v_dir_2959_, v_relManifestFile_2961_);
v___x_3080_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_3096_ = l_Lake_Manifest_load(v___x_3079_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
lean_ctor_set_tag(v___x_3099_, 1);
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
v_val_3082_ = v___x_3102_;
goto v___jp_3081_;
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
v_a_3105_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3096_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3096_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set_tag(v___x_3107_, 0);
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
v_val_3082_ = v___x_3110_;
goto v___jp_3081_;
}
}
}
v___jp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
lean_ctor_set(v___x_2891_, 1, v___y_2889_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
return v___x_2892_;
}
v___jp_2893_:
{
if (lean_obj_tag(v_fst_2895_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_snd_2896_);
v_a_2897_ = lean_ctor_get(v_fst_2895_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_fst_2895_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2899_ = v_fst_2895_;
v_isShared_2900_ = v_isSharedCheck_2911_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v_fst_2895_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2911_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2901_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2902_ = lean_io_error_to_string(v_a_2897_);
v___x_2903_ = lean_string_append(v___x_2901_, v___x_2902_);
lean_dec_ref(v___x_2902_);
v___x_2904_ = 3;
v___x_2905_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*1, v___x_2904_);
lean_inc_ref(v___y_2894_);
v___x_2906_ = lean_apply_2(v___y_2894_, v___x_2905_, lean_box(0));
v___x_2907_ = lean_box(0);
if (v_isShared_2900_ == 0)
{
lean_ctor_set_tag(v___x_2899_, 1);
lean_ctor_set(v___x_2899_, 0, v___x_2907_);
v___x_2909_ = v___x_2899_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
lean_dec_ref(v_fst_2895_);
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v_snd_2896_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
return v___x_2914_;
}
}
v___jp_2917_:
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = lean_array_get_size(v___y_2920_);
v___x_2923_ = lean_nat_dec_lt(v___x_2916_, v___x_2922_);
if (v___x_2923_ == 0)
{
v___y_2894_ = v___y_2919_;
v_fst_2895_ = v_val_2921_;
v_snd_2896_ = v___y_2918_;
goto v___jp_2893_;
}
else
{
lean_object* v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; lean_object* v___x_2927_; 
v___x_2924_ = lean_box(0);
v___x_2925_ = ((size_t)0ULL);
v___x_2926_ = lean_usize_of_nat(v___x_2922_);
v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2920_, v___x_2925_, v___x_2926_, v___x_2924_, v___y_2919_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_dec_ref_known(v___x_2927_, 1);
v___y_2894_ = v___y_2919_;
v_fst_2895_ = v_val_2921_;
v_snd_2896_ = v___y_2918_;
goto v___jp_2893_;
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec_ref(v_val_2921_);
lean_dec(v___y_2918_);
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
v___jp_2936_:
{
if (lean_obj_tag(v___y_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_a_2941_ = lean_ctor_get(v___y_2940_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___y_2940_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___y_2940_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___y_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set_tag(v___x_2943_, 1);
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
v___y_2918_ = v___y_2937_;
v___y_2919_ = v___y_2938_;
v___y_2920_ = v___y_2939_;
v_val_2921_ = v___x_2946_;
goto v___jp_2917_;
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_a_2949_ = lean_ctor_get(v___y_2940_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___y_2940_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___y_2940_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___y_2940_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 0);
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
v___y_2918_ = v___y_2937_;
v___y_2919_ = v___y_2938_;
v___y_2920_ = v___y_2939_;
v_val_2921_ = v___x_2954_;
goto v___jp_2917_;
}
}
}
}
v___jp_2962_:
{
lean_object* v_toWorkspaceConfig_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_toWorkspaceConfig_2968_ = lean_ctor_get(v_config_2960_, 0);
v___x_2969_ = l_System_FilePath_normalize(v___y_2964_);
lean_inc_ref(v_toWorkspaceConfig_2968_);
v___x_2970_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2968_);
lean_inc_ref(v___x_2970_);
v___x_2971_ = l_System_FilePath_normalize(v___x_2970_);
v___x_2972_ = lean_string_dec_eq(v___x_2969_, v___x_2971_);
lean_dec_ref(v___x_2971_);
lean_dec_ref(v___x_2969_);
if (v___x_2972_ == 0)
{
if (v_fst_2966_ == 0)
{
lean_dec_ref(v___x_2970_);
lean_dec_ref(v___y_2965_);
v___y_2889_ = v_snd_2967_;
goto v___jp_2888_;
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2973_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2974_ = lean_string_append(v___x_2973_, v___y_2965_);
v___x_2975_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2976_ = lean_string_append(v___x_2974_, v___x_2975_);
lean_inc_ref(v_dir_2959_);
v___x_2977_ = l_Lake_joinRelative(v_dir_2959_, v___x_2970_);
v___x_2978_ = lean_string_append(v___x_2976_, v___x_2977_);
v___x_2979_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2980_ = lean_string_append(v___x_2978_, v___x_2979_);
v___x_2981_ = 1;
v___x_2982_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set_uint8(v___x_2982_, sizeof(void*)*1, v___x_2981_);
lean_inc_ref(v___y_2963_);
v___x_2983_ = lean_apply_2(v___y_2963_, v___x_2982_, lean_box(0));
v___x_2984_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2977_);
v___x_2985_ = l_Lake_createParentDirs(v___x_2977_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v___x_2986_; 
lean_dec_ref_known(v___x_2985_, 1);
v___x_2986_ = lean_io_rename(v___y_2965_, v___x_2977_);
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___y_2965_);
v___y_2937_ = v_snd_2967_;
v___y_2938_ = v___y_2963_;
v___y_2939_ = v___x_2984_;
v___y_2940_ = v___x_2986_;
goto v___jp_2936_;
}
else
{
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___y_2965_);
v___y_2937_ = v_snd_2967_;
v___y_2938_ = v___y_2963_;
v___y_2939_ = v___x_2984_;
v___y_2940_ = v___x_2985_;
goto v___jp_2936_;
}
}
}
else
{
lean_dec_ref(v___x_2970_);
lean_dec_ref(v___y_2965_);
v___y_2889_ = v_snd_2967_;
goto v___jp_2888_;
}
}
v___jp_2987_:
{
if (lean_obj_tag(v_packagesDir_x3f_2988_) == 1)
{
lean_object* v_val_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; uint8_t v___x_2995_; 
v_val_2991_ = lean_ctor_get(v_packagesDir_x3f_2988_, 0);
lean_inc_n(v_val_2991_, 2);
lean_dec_ref_known(v_packagesDir_x3f_2988_, 1);
lean_inc_ref(v_dir_2959_);
v___x_2992_ = l_Lake_joinRelative(v_dir_2959_, v_val_2991_);
v___x_2993_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2994_ = l_System_FilePath_pathExists(v___x_2992_);
v___x_2995_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2995_ == 0)
{
v___y_2963_ = v___y_2990_;
v___y_2964_ = v_val_2991_;
v___y_2965_ = v___x_2992_;
v_fst_2966_ = v___x_2994_;
v_snd_2967_ = v___y_2989_;
goto v___jp_2962_;
}
else
{
lean_object* v___x_2996_; size_t v___x_2997_; size_t v___x_2998_; lean_object* v___x_2999_; 
v___x_2996_ = lean_box(0);
v___x_2997_ = ((size_t)0ULL);
v___x_2998_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_2999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_2993_, v___x_2997_, v___x_2998_, v___x_2996_, v___y_2990_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_dec_ref_known(v___x_2999_, 1);
v___y_2963_ = v___y_2990_;
v___y_2964_ = v_val_2991_;
v___y_2965_ = v___x_2992_;
v_fst_2966_ = v___x_2994_;
v_snd_2967_ = v___y_2989_;
goto v___jp_2962_;
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref(v___x_2992_);
lean_dec(v_val_2991_);
lean_dec(v___y_2989_);
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2999_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2999_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec(v_packagesDir_x3f_2988_);
v___x_3008_ = lean_box(0);
v___x_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set(v___x_3009_, 1, v___y_2989_);
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
return v___x_3010_;
}
}
v___jp_3013_:
{
if (lean_obj_tag(v_fst_3014_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3063_; 
v_a_3016_ = lean_ctor_get(v_fst_3014_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_fst_3014_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3018_ = v_fst_3014_;
v_isShared_3019_ = v_isSharedCheck_3063_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v_fst_3014_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3063_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
if (lean_obj_tag(v_a_3016_) == 11)
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
lean_dec_ref_known(v_a_3016_, 2);
lean_del_object(v___x_3018_);
v___x_3020_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_3021_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2885_, v___x_2957_, v___x_2916_, v___x_3020_, v_snd_3015_, v_a_2883_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3043_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3043_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3043_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_snd_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3041_; 
v_snd_3026_ = lean_ctor_get(v_a_3022_, 1);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_a_3022_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v_a_3022_, 0);
lean_dec(v_unused_3042_);
v___x_3028_ = v_a_3022_;
v_isShared_3029_ = v_isSharedCheck_3041_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_snd_3026_);
lean_dec(v_a_3022_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3041_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
v___x_3030_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8));
v___x_3031_ = lean_string_append(v_rootName_3012_, v___x_3030_);
v___x_3032_ = 1;
v___x_3033_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3033_, 0, v___x_3031_);
lean_ctor_set_uint8(v___x_3033_, sizeof(void*)*1, v___x_3032_);
lean_inc_ref(v_a_2883_);
v___x_3034_ = lean_apply_2(v_a_2883_, v___x_3033_, lean_box(0));
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3034_);
v___x_3036_ = v___x_3028_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3034_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v_snd_3026_);
v___x_3036_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3038_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3036_);
v___x_3038_ = v___x_3024_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_3012_);
return v___x_3021_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2885_) == 0)
{
lean_object* v___x_3044_; uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
lean_dec_ref_known(v_toUpdate_2885_, 5);
lean_dec(v_snd_3015_);
lean_dec_ref(v_rootName_3012_);
v___x_3044_ = lean_io_error_to_string(v_a_3016_);
v___x_3045_ = 3;
v___x_3046_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*1, v___x_3045_);
lean_inc_ref(v_a_2883_);
v___x_3047_ = lean_apply_2(v_a_2883_, v___x_3046_, lean_box(0));
v___x_3048_ = lean_box(0);
if (v_isShared_3019_ == 0)
{
lean_ctor_set_tag(v___x_3018_, 1);
lean_ctor_set(v___x_3018_, 0, v___x_3048_);
v___x_3050_ = v___x_3018_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3052_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_3053_ = lean_string_append(v_rootName_3012_, v___x_3052_);
v___x_3054_ = lean_io_error_to_string(v_a_3016_);
v___x_3055_ = lean_string_append(v___x_3053_, v___x_3054_);
lean_dec_ref(v___x_3054_);
v___x_3056_ = 2;
v___x_3057_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3057_, 0, v___x_3055_);
lean_ctor_set_uint8(v___x_3057_, sizeof(void*)*1, v___x_3056_);
lean_inc_ref(v_a_2883_);
v___x_3058_ = lean_apply_2(v_a_2883_, v___x_3057_, lean_box(0));
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v_snd_3015_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v___x_3059_);
v___x_3061_ = v___x_3018_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v_packagesDir_x3f_3065_; lean_object* v_packages_3066_; lean_object* v___x_3067_; 
lean_dec_ref(v_rootName_3012_);
v_a_3064_ = lean_ctor_get(v_fst_3014_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v_fst_3014_, 1);
v_packagesDir_x3f_3065_ = lean_ctor_get(v_a_3064_, 2);
lean_inc(v_packagesDir_x3f_3065_);
v_packages_3066_ = lean_ctor_get(v_a_3064_, 3);
lean_inc_ref(v_packages_3066_);
lean_dec(v_a_3064_);
lean_inc(v_toUpdate_2885_);
v___x_3067_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2885_, v___x_2957_, v___x_2916_, v_packages_3066_, v_snd_3015_, v_a_2883_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
if (lean_obj_tag(v_toUpdate_2885_) == 0)
{
lean_object* v_snd_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v_snd_3069_ = lean_ctor_get(v_a_3068_, 1);
lean_inc(v_snd_3069_);
lean_dec(v_a_3068_);
v___x_3070_ = lean_array_get_size(v_packages_3066_);
v___x_3071_ = lean_nat_dec_lt(v___x_2916_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_dec_ref_known(v_toUpdate_2885_, 5);
lean_dec_ref(v_packages_3066_);
v_packagesDir_x3f_2988_ = v_packagesDir_x3f_3065_;
v___y_2989_ = v_snd_3069_;
v___y_2990_ = v_a_2883_;
goto v___jp_2987_;
}
else
{
lean_object* v___x_3072_; size_t v___x_3073_; size_t v___x_3074_; lean_object* v___x_3075_; 
v___x_3072_ = lean_box(0);
v___x_3073_ = ((size_t)0ULL);
v___x_3074_ = lean_usize_of_nat(v___x_3070_);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_2885_, v_packages_3066_, v___x_3073_, v___x_3074_, v___x_3072_, v_snd_3069_);
lean_dec_ref(v_packages_3066_);
lean_dec_ref_known(v_toUpdate_2885_, 5);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v_snd_3077_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref_known(v___x_3075_, 1);
v_snd_3077_ = lean_ctor_get(v_a_3076_, 1);
lean_inc(v_snd_3077_);
lean_dec(v_a_3076_);
v_packagesDir_x3f_2988_ = v_packagesDir_x3f_3065_;
v___y_2989_ = v_snd_3077_;
v___y_2990_ = v_a_2883_;
goto v___jp_2987_;
}
else
{
lean_dec(v_packagesDir_x3f_3065_);
return v___x_3075_;
}
}
}
else
{
lean_object* v_snd_3078_; 
lean_dec_ref(v_packages_3066_);
v_snd_3078_ = lean_ctor_get(v_a_3068_, 1);
lean_inc(v_snd_3078_);
lean_dec(v_a_3068_);
v_packagesDir_x3f_2988_ = v_packagesDir_x3f_3065_;
v___y_2989_ = v_snd_3078_;
v___y_2990_ = v_a_2883_;
goto v___jp_2987_;
}
}
else
{
lean_dec_ref(v_packages_3066_);
lean_dec(v_packagesDir_x3f_3065_);
lean_dec(v_toUpdate_2885_);
return v___x_3067_;
}
}
}
v___jp_3081_:
{
uint8_t v___x_3083_; 
v___x_3083_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_3083_ == 0)
{
v_fst_3014_ = v_val_3082_;
v_snd_3015_ = v_a_2886_;
goto v___jp_3013_;
}
else
{
lean_object* v___x_3084_; size_t v___x_3085_; size_t v___x_3086_; lean_object* v___x_3087_; 
v___x_3084_ = lean_box(0);
v___x_3085_ = ((size_t)0ULL);
v___x_3086_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_3087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_3080_, v___x_3085_, v___x_3086_, v___x_3084_, v_a_2883_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_dec_ref_known(v___x_3087_, 1);
v_fst_3014_ = v_val_3082_;
v_snd_3015_ = v_a_2886_;
goto v___jp_3013_;
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec_ref(v_val_3082_);
lean_dec_ref(v_rootName_3012_);
lean_dec(v_a_2886_);
lean_dec(v_toUpdate_2885_);
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3087_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_3113_, lean_object* v_ws_3114_, lean_object* v_toUpdate_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_3113_, v_ws_3114_, v_toUpdate_3115_, v_a_3116_);
lean_dec_ref(v_ws_3114_);
lean_dec_ref(v_a_3113_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_a_3119_, lean_object* v_ws_3120_, lean_object* v_rootDeps_3121_){
_start:
{
lean_object* v___y_3124_; lean_object* v___y_3130_; lean_object* v___y_3131_; uint8_t v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; uint8_t v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; uint8_t v___y_3156_; lean_object* v___y_3157_; lean_object* v_lakeEnv_3160_; lean_object* v_lakeArgs_x3f_3161_; lean_object* v_packages_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v_baseName_3165_; lean_object* v_dir_3166_; lean_object* v_config_3167_; lean_object* v___x_3168_; lean_object* v_rootToolchainFile_3169_; uint8_t v___y_3171_; uint8_t v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3317_; uint8_t v___y_3318_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_lakeEnv_3160_ = lean_ctor_get(v_ws_3120_, 0);
lean_inc_ref(v_lakeEnv_3160_);
v_lakeArgs_x3f_3161_ = lean_ctor_get(v_ws_3120_, 3);
lean_inc(v_lakeArgs_x3f_3161_);
v_packages_3162_ = lean_ctor_get(v_ws_3120_, 4);
lean_inc_ref(v_packages_3162_);
lean_dec_ref(v_ws_3120_);
v___x_3163_ = lean_unsigned_to_nat(0u);
v___x_3164_ = lean_array_fget(v_packages_3162_, v___x_3163_);
lean_dec_ref(v_packages_3162_);
v_baseName_3165_ = lean_ctor_get(v___x_3164_, 1);
lean_inc(v_baseName_3165_);
v_dir_3166_ = lean_ctor_get(v___x_3164_, 4);
lean_inc_ref_n(v_dir_3166_, 3);
v_config_3167_ = lean_ctor_get(v___x_3164_, 6);
lean_inc_ref(v_config_3167_);
lean_dec(v___x_3164_);
v___x_3168_ = l_Lake_toolchainFileName;
v_rootToolchainFile_3169_ = l_Lake_joinRelative(v_dir_3166_, v___x_3168_);
v___x_3322_ = l_System_FilePath_join(v_dir_3166_, v___x_3168_);
v___x_3323_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3322_);
lean_dec_ref(v___x_3322_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3376_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3326_ = v___x_3323_;
v_isShared_3327_ = v_isSharedCheck_3376_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3376_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v_src_3329_; lean_object* v_tc_x3f_3330_; lean_object* v_clashes_3331_; uint8_t v_fixed_3332_; uint8_t v_fixedToolchain_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v_fixedToolchain_3355_ = lean_ctor_get_uint8(v_config_3167_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_3167_);
v___x_3356_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_3357_ = lean_array_get_size(v_rootDeps_3121_);
v___x_3358_ = lean_nat_dec_lt(v___x_3163_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_dec_ref(v_dir_3166_);
lean_inc(v_a_3324_);
v_src_3329_ = v_baseName_3165_;
v_tc_x3f_3330_ = v_a_3324_;
v_clashes_3331_ = v___x_3356_;
v_fixed_3332_ = v_fixedToolchain_3355_;
goto v___jp_3328_;
}
else
{
lean_object* v___x_3359_; size_t v___x_3360_; size_t v___x_3361_; lean_object* v___x_3362_; 
lean_inc(v_a_3324_);
v___x_3359_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3359_, 0, v_baseName_3165_);
lean_ctor_set(v___x_3359_, 1, v_a_3324_);
lean_ctor_set(v___x_3359_, 2, v___x_3356_);
lean_ctor_set_uint8(v___x_3359_, sizeof(void*)*3, v_fixedToolchain_3355_);
v___x_3360_ = ((size_t)0ULL);
v___x_3361_ = lean_usize_of_nat(v___x_3357_);
v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3166_, v_rootDeps_3121_, v___x_3360_, v___x_3361_, v___x_3359_, v_a_3119_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v_src_3364_; lean_object* v_tc_x3f_3365_; lean_object* v_clashes_3366_; uint8_t v_fixed_3367_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v_src_3364_ = lean_ctor_get(v_a_3363_, 0);
lean_inc(v_src_3364_);
v_tc_x3f_3365_ = lean_ctor_get(v_a_3363_, 1);
lean_inc(v_tc_x3f_3365_);
v_clashes_3366_ = lean_ctor_get(v_a_3363_, 2);
lean_inc_ref(v_clashes_3366_);
v_fixed_3367_ = lean_ctor_get_uint8(v_a_3363_, sizeof(void*)*3);
lean_dec(v_a_3363_);
v_src_3329_ = v_src_3364_;
v_tc_x3f_3330_ = v_tc_x3f_3365_;
v_clashes_3331_ = v_clashes_3366_;
v_fixed_3332_ = v_fixed_3367_;
goto v___jp_3328_;
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_del_object(v___x_3326_);
lean_dec(v_a_3324_);
lean_dec_ref(v_rootToolchainFile_3169_);
lean_dec(v_lakeArgs_x3f_3161_);
lean_dec_ref(v_lakeEnv_3160_);
v_a_3368_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3362_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3362_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
v___jp_3328_:
{
lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3333_ = lean_array_get_size(v_clashes_3331_);
v___x_3334_ = lean_nat_dec_lt(v___x_3163_, v___x_3333_);
if (v___x_3334_ == 0)
{
lean_dec_ref(v_clashes_3331_);
lean_dec(v_src_3329_);
if (lean_obj_tag(v_tc_x3f_3330_) == 1)
{
if (lean_obj_tag(v_a_3324_) == 0)
{
lean_object* v_val_3335_; 
lean_del_object(v___x_3326_);
v_val_3335_ = lean_ctor_get(v_tc_x3f_3330_, 0);
lean_inc(v_val_3335_);
lean_dec_ref_known(v_tc_x3f_3330_, 1);
v___y_3317_ = v_val_3335_;
v___y_3318_ = v___x_3334_;
goto v___jp_3316_;
}
else
{
lean_object* v_val_3336_; lean_object* v_val_3337_; uint8_t v___x_3338_; 
v_val_3336_ = lean_ctor_get(v_tc_x3f_3330_, 0);
lean_inc_n(v_val_3336_, 2);
lean_dec_ref_known(v_tc_x3f_3330_, 1);
v_val_3337_ = lean_ctor_get(v_a_3324_, 0);
lean_inc(v_val_3337_);
lean_dec_ref_known(v_a_3324_, 1);
v___x_3338_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3337_, v_val_3336_);
if (v___x_3338_ == 0)
{
lean_del_object(v___x_3326_);
v___y_3317_ = v_val_3336_;
v___y_3318_ = v___x_3338_;
goto v___jp_3316_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3343_; 
lean_dec(v_val_3336_);
lean_dec_ref(v_rootToolchainFile_3169_);
lean_dec(v_lakeArgs_x3f_3161_);
lean_dec_ref(v_lakeEnv_3160_);
v___x_3339_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_3119_);
v___x_3340_ = lean_apply_2(v_a_3119_, v___x_3339_, lean_box(0));
v___x_3341_ = lean_box(0);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3341_);
v___x_3343_ = v___x_3326_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
else
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
lean_dec(v_tc_x3f_3330_);
lean_dec(v_a_3324_);
lean_dec_ref(v_rootToolchainFile_3169_);
lean_dec(v_lakeArgs_x3f_3161_);
lean_dec_ref(v_lakeEnv_3160_);
v___x_3345_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_3119_);
v___x_3346_ = lean_apply_2(v_a_3119_, v___x_3345_, lean_box(0));
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3346_);
v___x_3348_ = v___x_3326_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
else
{
lean_del_object(v___x_3326_);
lean_dec(v_a_3324_);
lean_dec_ref(v_rootToolchainFile_3169_);
lean_dec(v_lakeArgs_x3f_3161_);
lean_dec_ref(v_lakeEnv_3160_);
if (lean_obj_tag(v_tc_x3f_3330_) == 1)
{
if (v_fixed_3332_ == 0)
{
lean_object* v_val_3350_; lean_object* v___x_3351_; 
v_val_3350_ = lean_ctor_get(v_tc_x3f_3330_, 0);
lean_inc(v_val_3350_);
lean_dec_ref_known(v_tc_x3f_3330_, 1);
v___x_3351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3152_ = v_src_3329_;
v___y_3153_ = v___x_3333_;
v___y_3154_ = v_clashes_3331_;
v___y_3155_ = v_val_3350_;
v___y_3156_ = v___x_3334_;
v___y_3157_ = v___x_3351_;
goto v___jp_3151_;
}
else
{
lean_object* v_val_3352_; lean_object* v___x_3353_; 
v_val_3352_ = lean_ctor_get(v_tc_x3f_3330_, 0);
lean_inc(v_val_3352_);
lean_dec_ref_known(v_tc_x3f_3330_, 1);
v___x_3353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3152_ = v_src_3329_;
v___y_3153_ = v___x_3333_;
v___y_3154_ = v_clashes_3331_;
v___y_3155_ = v_val_3352_;
v___y_3156_ = v___x_3334_;
v___y_3157_ = v___x_3353_;
goto v___jp_3151_;
}
}
else
{
lean_object* v___x_3354_; 
lean_dec(v_tc_x3f_3330_);
lean_dec(v_src_3329_);
v___x_3354_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_3130_ = v___x_3333_;
v___y_3131_ = v_clashes_3331_;
v___y_3132_ = v___x_3334_;
v___y_3133_ = v___x_3354_;
goto v___jp_3129_;
}
}
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3389_; 
lean_dec_ref(v_rootToolchainFile_3169_);
lean_dec_ref(v_config_3167_);
lean_dec_ref(v_dir_3166_);
lean_dec(v_baseName_3165_);
lean_dec(v_lakeArgs_x3f_3161_);
lean_dec_ref(v_lakeEnv_3160_);
v_a_3377_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3379_ = v___x_3323_;
v_isShared_3380_ = v_isSharedCheck_3389_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3323_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3389_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3381_ = lean_io_error_to_string(v_a_3377_);
v___x_3382_ = 3;
v___x_3383_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set_uint8(v___x_3383_, sizeof(void*)*1, v___x_3382_);
lean_inc_ref(v_a_3119_);
v___x_3384_ = lean_apply_2(v_a_3119_, v___x_3383_, lean_box(0));
v___x_3385_ = lean_box(0);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3385_);
v___x_3387_ = v___x_3379_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
v___jp_3123_:
{
uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3125_ = 2;
v___x_3126_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3126_, 0, v___y_3124_);
lean_ctor_set_uint8(v___x_3126_, sizeof(void*)*1, v___x_3125_);
lean_inc_ref(v_a_3119_);
v___x_3127_ = lean_apply_2(v_a_3119_, v___x_3126_, lean_box(0));
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
return v___x_3128_;
}
v___jp_3129_:
{
if (v___y_3132_ == 0)
{
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
v___y_3124_ = v___y_3133_;
goto v___jp_3123_;
}
else
{
size_t v___x_3134_; size_t v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = ((size_t)0ULL);
v___x_3135_ = lean_usize_of_nat(v___y_3130_);
v___x_3136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3130_, v___y_3131_, v___x_3134_, v___x_3135_, v___y_3133_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
v___y_3124_ = v___x_3136_;
goto v___jp_3123_;
}
}
v___jp_3137_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_inc_ref(v___y_3143_);
v___x_3145_ = lean_string_append(v___y_3143_, v___y_3144_);
lean_dec_ref(v___y_3144_);
v___x_3146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3147_ = lean_string_append(v___x_3145_, v___x_3146_);
v___x_3148_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3139_, v___y_3142_);
v___x_3149_ = lean_string_append(v___x_3147_, v___x_3148_);
lean_dec_ref(v___x_3148_);
v___x_3150_ = lean_string_append(v___x_3149_, v___y_3138_);
v___y_3130_ = v___y_3140_;
v___y_3131_ = v___y_3141_;
v___y_3132_ = v___y_3142_;
v___y_3133_ = v___x_3150_;
goto v___jp_3129_;
}
v___jp_3151_:
{
lean_object* v___x_3158_; lean_object* v_toString_3159_; 
v___x_3158_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_3159_ = lean_ctor_get(v___y_3155_, 0);
lean_inc_ref(v_toString_3159_);
lean_dec_ref(v___y_3155_);
v___y_3138_ = v___y_3157_;
v___y_3139_ = v___y_3152_;
v___y_3140_ = v___y_3153_;
v___y_3141_ = v___y_3154_;
v___y_3142_ = v___y_3156_;
v___y_3143_ = v___x_3158_;
v___y_3144_ = v_toString_3159_;
goto v___jp_3137_;
}
v___jp_3170_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_inc_ref(v___y_3173_);
v___x_3175_ = lean_string_append(v___y_3173_, v___y_3174_);
v___x_3176_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_3177_ = lean_string_append(v___x_3175_, v___x_3176_);
v___x_3178_ = 1;
v___x_3179_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set_uint8(v___x_3179_, sizeof(void*)*1, v___x_3178_);
lean_inc_ref(v_a_3119_);
v___x_3180_ = lean_apply_2(v_a_3119_, v___x_3179_, lean_box(0));
v___x_3181_ = l_IO_FS_writeFile(v_rootToolchainFile_3169_, v___y_3174_);
lean_dec_ref(v_rootToolchainFile_3169_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_dec_ref_known(v___x_3181_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_3161_) == 1)
{
lean_object* v_elan_x3f_3182_; 
v_elan_x3f_3182_ = lean_ctor_get(v_lakeEnv_3160_, 2);
if (lean_obj_tag(v_elan_x3f_3182_) == 1)
{
lean_object* v_val_3183_; lean_object* v_val_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v_elan_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v_val_3183_ = lean_ctor_get(v_lakeArgs_x3f_3161_, 0);
lean_inc(v_val_3183_);
lean_dec_ref_known(v_lakeArgs_x3f_3161_, 1);
v_val_3184_ = lean_ctor_get(v_elan_x3f_3182_, 0);
v___x_3185_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_3119_);
v___x_3186_ = lean_apply_2(v_a_3119_, v___x_3185_, lean_box(0));
v___x_3187_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_3188_ = lean_ctor_get(v_val_3184_, 1);
lean_inc_ref(v_elan_3188_);
v___x_3189_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_3190_ = lean_unsigned_to_nat(4u);
v___x_3191_ = lean_mk_empty_array_with_capacity(v___x_3190_);
lean_dec_ref(v___x_3191_);
v___x_3192_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_3193_ = lean_array_push(v___x_3192_, v___y_3174_);
v___x_3194_ = lean_array_push(v___x_3193_, v___x_3189_);
v___x_3195_ = l_Array_append___redArg(v___x_3194_, v_val_3183_);
lean_dec(v_val_3183_);
v___x_3196_ = lean_box(0);
v___x_3197_ = l_Lake_Env_noToolchainVars(v_lakeEnv_3160_);
v___x_3198_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3198_, 0, v___x_3187_);
lean_ctor_set(v___x_3198_, 1, v_elan_3188_);
lean_ctor_set(v___x_3198_, 2, v___x_3195_);
lean_ctor_set(v___x_3198_, 3, v___x_3196_);
lean_ctor_set(v___x_3198_, 4, v___x_3197_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*5, v___y_3171_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*5 + 1, v___y_3172_);
v___x_3199_ = lean_io_process_spawn(v___x_3198_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3201_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = lean_io_process_child_wait(v___x_3187_, v_a_3200_);
lean_dec(v_a_3200_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; uint32_t v___x_3203_; uint8_t v___x_3204_; lean_object* v___x_3205_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref_known(v___x_3201_, 1);
v___x_3203_ = lean_unbox_uint32(v_a_3202_);
lean_dec(v_a_3202_);
v___x_3204_ = lean_uint32_to_uint8(v___x_3203_);
v___x_3205_ = lean_io_exit(v___x_3204_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3226_; 
v_a_3214_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3216_ = v___x_3205_;
v_isShared_3217_ = v_isSharedCheck_3226_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3205_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3226_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; uint8_t v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3218_ = lean_io_error_to_string(v_a_3214_);
v___x_3219_ = 3;
v___x_3220_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set_uint8(v___x_3220_, sizeof(void*)*1, v___x_3219_);
lean_inc_ref(v_a_3119_);
v___x_3221_ = lean_apply_2(v_a_3119_, v___x_3220_, lean_box(0));
v___x_3222_ = lean_box(0);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3222_);
v___x_3224_ = v___x_3216_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3239_; 
v_a_3227_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3229_ = v___x_3201_;
v_isShared_3230_ = v_isSharedCheck_3239_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3201_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3239_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3231_ = lean_io_error_to_string(v_a_3227_);
v___x_3232_ = 3;
v___x_3233_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3233_, 0, v___x_3231_);
lean_ctor_set_uint8(v___x_3233_, sizeof(void*)*1, v___x_3232_);
lean_inc_ref(v_a_3119_);
v___x_3234_ = lean_apply_2(v_a_3119_, v___x_3233_, lean_box(0));
v___x_3235_ = lean_box(0);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3235_);
v___x_3237_ = v___x_3229_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3252_; 
v_a_3240_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3242_ = v___x_3199_;
v_isShared_3243_ = v_isSharedCheck_3252_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3199_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3252_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; uint8_t v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3244_ = lean_io_error_to_string(v_a_3240_);
v___x_3245_ = 3;
v___x_3246_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*1, v___x_3245_);
lean_inc_ref(v_a_3119_);
v___x_3247_ = lean_apply_2(v_a_3119_, v___x_3246_, lean_box(0));
v___x_3248_ = lean_box(0);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3248_);
v___x_3250_ = v___x_3242_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; 
lean_dec_ref_known(v_lakeArgs_x3f_3161_, 1);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v_lakeEnv_3160_);
v___x_3253_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_3119_);
v___x_3254_ = lean_apply_2(v_a_3119_, v___x_3253_, lean_box(0));
v___x_3255_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11);
v___x_3256_ = lean_io_exit(v___x_3255_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3277_; 
v_a_3265_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3267_ = v___x_3256_;
v_isShared_3268_ = v_isSharedCheck_3277_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3256_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3277_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; uint8_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3269_ = lean_io_error_to_string(v_a_3265_);
v___x_3270_ = 3;
v___x_3271_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3271_, 0, v___x_3269_);
lean_ctor_set_uint8(v___x_3271_, sizeof(void*)*1, v___x_3270_);
lean_inc_ref(v_a_3119_);
v___x_3272_ = lean_apply_2(v_a_3119_, v___x_3271_, lean_box(0));
v___x_3273_ = lean_box(0);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 0, v___x_3273_);
v___x_3275_ = v___x_3267_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; lean_object* v___x_3281_; 
lean_dec_ref(v___y_3174_);
lean_dec(v_lakeArgs_x3f_3161_);
lean_dec_ref(v_lakeEnv_3160_);
v___x_3278_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
lean_inc_ref(v_a_3119_);
v___x_3279_ = lean_apply_2(v_a_3119_, v___x_3278_, lean_box(0));
v___x_3280_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__11);
v___x_3281_ = lean_io_exit(v___x_3280_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3302_; 
v_a_3290_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3292_ = v___x_3281_;
v_isShared_3293_ = v_isSharedCheck_3302_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3281_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3302_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3294_ = lean_io_error_to_string(v_a_3290_);
v___x_3295_ = 3;
v___x_3296_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3296_, 0, v___x_3294_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*1, v___x_3295_);
lean_inc_ref(v_a_3119_);
v___x_3297_ = lean_apply_2(v_a_3119_, v___x_3296_, lean_box(0));
v___x_3298_ = lean_box(0);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3298_);
v___x_3300_ = v___x_3292_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3315_; 
lean_dec_ref(v___y_3174_);
lean_dec(v_lakeArgs_x3f_3161_);
lean_dec_ref(v_lakeEnv_3160_);
v_a_3303_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3305_ = v___x_3181_;
v_isShared_3306_ = v_isSharedCheck_3315_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3181_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3315_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3307_ = lean_io_error_to_string(v_a_3303_);
v___x_3308_ = 3;
v___x_3309_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*1, v___x_3308_);
lean_inc_ref(v_a_3119_);
v___x_3310_ = lean_apply_2(v_a_3119_, v___x_3309_, lean_box(0));
v___x_3311_ = lean_box(0);
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 0, v___x_3311_);
v___x_3313_ = v___x_3305_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
v___jp_3316_:
{
uint8_t v___x_3319_; lean_object* v___x_3320_; lean_object* v_toString_3321_; 
v___x_3319_ = 1;
v___x_3320_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_3321_ = lean_ctor_get(v___y_3317_, 0);
lean_inc_ref(v_toString_3321_);
lean_dec_ref(v___y_3317_);
v___y_3171_ = v___x_3319_;
v___y_3172_ = v___y_3318_;
v___y_3173_ = v___x_3320_;
v___y_3174_ = v_toString_3321_;
goto v___jp_3170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_a_3390_, lean_object* v_ws_3391_, lean_object* v_rootDeps_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3390_, v_ws_3391_, v_rootDeps_3392_);
lean_dec_ref(v_rootDeps_3392_);
lean_dec_ref(v_a_3390_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(lean_object* v_msg_3395_){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = lean_box(1);
v___x_3397_ = lean_panic_fn_borrowed(v___x_3396_, v_msg_3395_);
return v___x_3397_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3401_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3402_ = lean_unsigned_to_nat(35u);
v___x_3403_ = lean_unsigned_to_nat(182u);
v___x_3404_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3405_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3406_ = l_mkPanicMessageWithDecl(v___x_3405_, v___x_3404_, v___x_3403_, v___x_3402_, v___x_3401_);
return v___x_3406_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3407_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3408_ = lean_unsigned_to_nat(21u);
v___x_3409_ = lean_unsigned_to_nat(183u);
v___x_3410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3411_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3412_ = l_mkPanicMessageWithDecl(v___x_3411_, v___x_3410_, v___x_3409_, v___x_3408_, v___x_3407_);
return v___x_3412_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3416_ = lean_unsigned_to_nat(35u);
v___x_3417_ = lean_unsigned_to_nat(276u);
v___x_3418_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3419_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3420_ = l_mkPanicMessageWithDecl(v___x_3419_, v___x_3418_, v___x_3417_, v___x_3416_, v___x_3415_);
return v___x_3420_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3421_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3422_ = lean_unsigned_to_nat(21u);
v___x_3423_ = lean_unsigned_to_nat(277u);
v___x_3424_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3425_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3426_ = l_mkPanicMessageWithDecl(v___x_3425_, v___x_3424_, v___x_3423_, v___x_3422_, v___x_3421_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(lean_object* v_k_3427_, lean_object* v_v_3428_, lean_object* v_t_3429_){
_start:
{
if (lean_obj_tag(v_t_3429_) == 0)
{
lean_object* v_size_3430_; lean_object* v_k_3431_; lean_object* v_v_3432_; lean_object* v_l_3433_; lean_object* v_r_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3790_; 
v_size_3430_ = lean_ctor_get(v_t_3429_, 0);
v_k_3431_ = lean_ctor_get(v_t_3429_, 1);
v_v_3432_ = lean_ctor_get(v_t_3429_, 2);
v_l_3433_ = lean_ctor_get(v_t_3429_, 3);
v_r_3434_ = lean_ctor_get(v_t_3429_, 4);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_t_3429_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3436_ = v_t_3429_;
v_isShared_3437_ = v_isSharedCheck_3790_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_r_3434_);
lean_inc(v_l_3433_);
lean_inc(v_v_3432_);
lean_inc(v_k_3431_);
lean_inc(v_size_3430_);
lean_dec(v_t_3429_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3790_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
uint8_t v___x_3438_; 
v___x_3438_ = lean_string_compare(v_k_3427_, v_k_3431_);
switch(v___x_3438_)
{
case 0:
{
lean_object* v___x_3439_; 
lean_dec(v_size_3430_);
v___x_3439_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3427_, v_v_3428_, v_l_3433_);
if (lean_obj_tag(v_r_3434_) == 0)
{
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_size_3440_; lean_object* v_size_3441_; lean_object* v_k_3442_; lean_object* v_v_3443_; lean_object* v_l_3444_; lean_object* v_r_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v_size_3440_ = lean_ctor_get(v_r_3434_, 0);
v_size_3441_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_size_3441_);
v_k_3442_ = lean_ctor_get(v___x_3439_, 1);
lean_inc(v_k_3442_);
v_v_3443_ = lean_ctor_get(v___x_3439_, 2);
lean_inc(v_v_3443_);
v_l_3444_ = lean_ctor_get(v___x_3439_, 3);
lean_inc(v_l_3444_);
v_r_3445_ = lean_ctor_get(v___x_3439_, 4);
lean_inc(v_r_3445_);
v___x_3446_ = lean_unsigned_to_nat(3u);
v___x_3447_ = lean_nat_mul(v___x_3446_, v_size_3440_);
v___x_3448_ = lean_nat_dec_lt(v___x_3447_, v_size_3441_);
lean_dec(v___x_3447_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3453_; 
lean_dec(v_r_3445_);
lean_dec(v_l_3444_);
lean_dec(v_v_3443_);
lean_dec(v_k_3442_);
v___x_3449_ = lean_unsigned_to_nat(1u);
v___x_3450_ = lean_nat_add(v___x_3449_, v_size_3441_);
lean_dec(v_size_3441_);
v___x_3451_ = lean_nat_add(v___x_3450_, v_size_3440_);
lean_dec(v___x_3450_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 3, v___x_3439_);
lean_ctor_set(v___x_3436_, 0, v___x_3451_);
v___x_3453_ = v___x_3436_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3454_, 3, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3454_, 4, v_r_3434_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
else
{
lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3526_; 
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3526_ == 0)
{
lean_object* v_unused_3527_; lean_object* v_unused_3528_; lean_object* v_unused_3529_; lean_object* v_unused_3530_; lean_object* v_unused_3531_; 
v_unused_3527_ = lean_ctor_get(v___x_3439_, 4);
lean_dec(v_unused_3527_);
v_unused_3528_ = lean_ctor_get(v___x_3439_, 3);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v___x_3439_, 2);
lean_dec(v_unused_3529_);
v_unused_3530_ = lean_ctor_get(v___x_3439_, 1);
lean_dec(v_unused_3530_);
v_unused_3531_ = lean_ctor_get(v___x_3439_, 0);
lean_dec(v_unused_3531_);
v___x_3456_ = v___x_3439_;
v_isShared_3457_ = v_isSharedCheck_3526_;
goto v_resetjp_3455_;
}
else
{
lean_dec(v___x_3439_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3526_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
if (lean_obj_tag(v_l_3444_) == 0)
{
if (lean_obj_tag(v_r_3445_) == 0)
{
lean_object* v_size_3458_; lean_object* v_size_3459_; lean_object* v_k_3460_; lean_object* v_v_3461_; lean_object* v_l_3462_; lean_object* v_r_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; 
v_size_3458_ = lean_ctor_get(v_l_3444_, 0);
v_size_3459_ = lean_ctor_get(v_r_3445_, 0);
v_k_3460_ = lean_ctor_get(v_r_3445_, 1);
v_v_3461_ = lean_ctor_get(v_r_3445_, 2);
v_l_3462_ = lean_ctor_get(v_r_3445_, 3);
v_r_3463_ = lean_ctor_get(v_r_3445_, 4);
v___x_3464_ = lean_unsigned_to_nat(2u);
v___x_3465_ = lean_nat_mul(v___x_3464_, v_size_3458_);
v___x_3466_ = lean_nat_dec_lt(v_size_3459_, v___x_3465_);
lean_dec(v___x_3465_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3496_; 
lean_inc(v_r_3463_);
lean_inc(v_l_3462_);
lean_inc(v_v_3461_);
lean_inc(v_k_3460_);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_r_3445_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; lean_object* v_unused_3498_; lean_object* v_unused_3499_; lean_object* v_unused_3500_; lean_object* v_unused_3501_; 
v_unused_3497_ = lean_ctor_get(v_r_3445_, 4);
lean_dec(v_unused_3497_);
v_unused_3498_ = lean_ctor_get(v_r_3445_, 3);
lean_dec(v_unused_3498_);
v_unused_3499_ = lean_ctor_get(v_r_3445_, 2);
lean_dec(v_unused_3499_);
v_unused_3500_ = lean_ctor_get(v_r_3445_, 1);
lean_dec(v_unused_3500_);
v_unused_3501_ = lean_ctor_get(v_r_3445_, 0);
lean_dec(v_unused_3501_);
v___x_3468_ = v_r_3445_;
v_isShared_3469_ = v_isSharedCheck_3496_;
goto v_resetjp_3467_;
}
else
{
lean_dec(v_r_3445_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3496_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___x_3484_; lean_object* v___y_3486_; 
v___x_3470_ = lean_unsigned_to_nat(1u);
v___x_3471_ = lean_nat_add(v___x_3470_, v_size_3441_);
lean_dec(v_size_3441_);
v___x_3472_ = lean_nat_add(v___x_3471_, v_size_3440_);
lean_dec(v___x_3471_);
v___x_3484_ = lean_nat_add(v___x_3470_, v_size_3458_);
if (lean_obj_tag(v_l_3462_) == 0)
{
lean_object* v_size_3494_; 
v_size_3494_ = lean_ctor_get(v_l_3462_, 0);
lean_inc(v_size_3494_);
v___y_3486_ = v_size_3494_;
goto v___jp_3485_;
}
else
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_unsigned_to_nat(0u);
v___y_3486_ = v___x_3495_;
goto v___jp_3485_;
}
v___jp_3473_:
{
lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3477_ = lean_nat_add(v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec(v___y_3475_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 4, v_r_3434_);
lean_ctor_set(v___x_3468_, 3, v_r_3463_);
lean_ctor_set(v___x_3468_, 2, v_v_3432_);
lean_ctor_set(v___x_3468_, 1, v_k_3431_);
lean_ctor_set(v___x_3468_, 0, v___x_3477_);
v___x_3479_ = v___x_3468_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3483_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3483_, 3, v_r_3463_);
lean_ctor_set(v_reuseFailAlloc_3483_, 4, v_r_3434_);
v___x_3479_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3481_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 4, v___x_3479_);
lean_ctor_set(v___x_3456_, 3, v___y_3474_);
lean_ctor_set(v___x_3456_, 2, v_v_3461_);
lean_ctor_set(v___x_3456_, 1, v_k_3460_);
lean_ctor_set(v___x_3456_, 0, v___x_3472_);
v___x_3481_ = v___x_3456_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_k_3460_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v_v_3461_);
lean_ctor_set(v_reuseFailAlloc_3482_, 3, v___y_3474_);
lean_ctor_set(v_reuseFailAlloc_3482_, 4, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
v___jp_3485_:
{
lean_object* v___x_3487_; lean_object* v___x_3489_; 
v___x_3487_ = lean_nat_add(v___x_3484_, v___y_3486_);
lean_dec(v___y_3486_);
lean_dec(v___x_3484_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_l_3462_);
lean_ctor_set(v___x_3436_, 3, v_l_3444_);
lean_ctor_set(v___x_3436_, 2, v_v_3443_);
lean_ctor_set(v___x_3436_, 1, v_k_3442_);
lean_ctor_set(v___x_3436_, 0, v___x_3487_);
v___x_3489_ = v___x_3436_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3487_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_k_3442_);
lean_ctor_set(v_reuseFailAlloc_3493_, 2, v_v_3443_);
lean_ctor_set(v_reuseFailAlloc_3493_, 3, v_l_3444_);
lean_ctor_set(v_reuseFailAlloc_3493_, 4, v_l_3462_);
v___x_3489_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_nat_add(v___x_3470_, v_size_3440_);
if (lean_obj_tag(v_r_3463_) == 0)
{
lean_object* v_size_3491_; 
v_size_3491_ = lean_ctor_get(v_r_3463_, 0);
lean_inc(v_size_3491_);
v___y_3474_ = v___x_3489_;
v___y_3475_ = v___x_3490_;
v___y_3476_ = v_size_3491_;
goto v___jp_3473_;
}
else
{
lean_object* v___x_3492_; 
v___x_3492_ = lean_unsigned_to_nat(0u);
v___y_3474_ = v___x_3489_;
v___y_3475_ = v___x_3490_;
v___y_3476_ = v___x_3492_;
goto v___jp_3473_;
}
}
}
}
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_del_object(v___x_3436_);
v___x_3502_ = lean_unsigned_to_nat(1u);
v___x_3503_ = lean_nat_add(v___x_3502_, v_size_3441_);
lean_dec(v_size_3441_);
v___x_3504_ = lean_nat_add(v___x_3503_, v_size_3440_);
lean_dec(v___x_3503_);
v___x_3505_ = lean_nat_add(v___x_3502_, v_size_3440_);
v___x_3506_ = lean_nat_add(v___x_3505_, v_size_3459_);
lean_dec(v___x_3505_);
lean_inc_ref(v_r_3434_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 4, v_r_3434_);
lean_ctor_set(v___x_3456_, 3, v_r_3445_);
lean_ctor_set(v___x_3456_, 2, v_v_3432_);
lean_ctor_set(v___x_3456_, 1, v_k_3431_);
lean_ctor_set(v___x_3456_, 0, v___x_3506_);
v___x_3508_ = v___x_3456_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3506_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3521_, 3, v_r_3445_);
lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_r_3434_);
v___x_3508_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
v_isSharedCheck_3515_ = !lean_is_exclusive(v_r_3434_);
if (v_isSharedCheck_3515_ == 0)
{
lean_object* v_unused_3516_; lean_object* v_unused_3517_; lean_object* v_unused_3518_; lean_object* v_unused_3519_; lean_object* v_unused_3520_; 
v_unused_3516_ = lean_ctor_get(v_r_3434_, 4);
lean_dec(v_unused_3516_);
v_unused_3517_ = lean_ctor_get(v_r_3434_, 3);
lean_dec(v_unused_3517_);
v_unused_3518_ = lean_ctor_get(v_r_3434_, 2);
lean_dec(v_unused_3518_);
v_unused_3519_ = lean_ctor_get(v_r_3434_, 1);
lean_dec(v_unused_3519_);
v_unused_3520_ = lean_ctor_get(v_r_3434_, 0);
lean_dec(v_unused_3520_);
v___x_3510_ = v_r_3434_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_dec(v_r_3434_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 4, v___x_3508_);
lean_ctor_set(v___x_3510_, 3, v_l_3444_);
lean_ctor_set(v___x_3510_, 2, v_v_3443_);
lean_ctor_set(v___x_3510_, 1, v_k_3442_);
lean_ctor_set(v___x_3510_, 0, v___x_3504_);
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_k_3442_);
lean_ctor_set(v_reuseFailAlloc_3514_, 2, v_v_3443_);
lean_ctor_set(v_reuseFailAlloc_3514_, 3, v_l_3444_);
lean_ctor_set(v_reuseFailAlloc_3514_, 4, v___x_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_dec_ref_known(v_l_3444_, 5);
lean_del_object(v___x_3456_);
lean_dec(v_v_3443_);
lean_dec(v_k_3442_);
lean_dec(v_size_3441_);
lean_dec_ref_known(v_r_3434_, 5);
lean_del_object(v___x_3436_);
lean_dec(v_v_3432_);
lean_dec(v_k_3431_);
v___x_3522_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3);
v___x_3523_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3522_);
return v___x_3523_;
}
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_del_object(v___x_3456_);
lean_dec(v_r_3445_);
lean_dec(v_v_3443_);
lean_dec(v_k_3442_);
lean_dec(v_size_3441_);
lean_dec_ref_known(v_r_3434_, 5);
lean_del_object(v___x_3436_);
lean_dec(v_v_3432_);
lean_dec(v_k_3431_);
v___x_3524_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4);
v___x_3525_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3524_);
return v___x_3525_;
}
}
}
}
else
{
lean_object* v_size_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v_size_3532_ = lean_ctor_get(v_r_3434_, 0);
v___x_3533_ = lean_unsigned_to_nat(1u);
v___x_3534_ = lean_nat_add(v___x_3533_, v_size_3532_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 3, v___x_3439_);
lean_ctor_set(v___x_3436_, 0, v___x_3534_);
v___x_3536_ = v___x_3436_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3537_, 4, v_r_3434_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
else
{
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_l_3538_; 
v_l_3538_ = lean_ctor_get(v___x_3439_, 3);
lean_inc(v_l_3538_);
if (lean_obj_tag(v_l_3538_) == 0)
{
lean_object* v_r_3539_; 
v_r_3539_ = lean_ctor_get(v___x_3439_, 4);
lean_inc(v_r_3539_);
if (lean_obj_tag(v_r_3539_) == 0)
{
lean_object* v_size_3540_; lean_object* v_k_3541_; lean_object* v_v_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3556_; 
v_size_3540_ = lean_ctor_get(v___x_3439_, 0);
v_k_3541_ = lean_ctor_get(v___x_3439_, 1);
v_v_3542_ = lean_ctor_get(v___x_3439_, 2);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; lean_object* v_unused_3558_; 
v_unused_3557_ = lean_ctor_get(v___x_3439_, 4);
lean_dec(v_unused_3557_);
v_unused_3558_ = lean_ctor_get(v___x_3439_, 3);
lean_dec(v_unused_3558_);
v___x_3544_ = v___x_3439_;
v_isShared_3545_ = v_isSharedCheck_3556_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_v_3542_);
lean_inc(v_k_3541_);
lean_inc(v_size_3540_);
lean_dec(v___x_3439_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3556_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v_size_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3551_; 
v_size_3546_ = lean_ctor_get(v_r_3539_, 0);
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_add(v___x_3547_, v_size_3540_);
lean_dec(v_size_3540_);
v___x_3549_ = lean_nat_add(v___x_3547_, v_size_3546_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 4, v_r_3434_);
lean_ctor_set(v___x_3544_, 3, v_r_3539_);
lean_ctor_set(v___x_3544_, 2, v_v_3432_);
lean_ctor_set(v___x_3544_, 1, v_k_3431_);
lean_ctor_set(v___x_3544_, 0, v___x_3549_);
v___x_3551_ = v___x_3544_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3555_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3555_, 3, v_r_3539_);
lean_ctor_set(v_reuseFailAlloc_3555_, 4, v_r_3434_);
v___x_3551_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3553_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v___x_3551_);
lean_ctor_set(v___x_3436_, 3, v_l_3538_);
lean_ctor_set(v___x_3436_, 2, v_v_3542_);
lean_ctor_set(v___x_3436_, 1, v_k_3541_);
lean_ctor_set(v___x_3436_, 0, v___x_3548_);
v___x_3553_ = v___x_3436_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3548_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_k_3541_);
lean_ctor_set(v_reuseFailAlloc_3554_, 2, v_v_3542_);
lean_ctor_set(v_reuseFailAlloc_3554_, 3, v_l_3538_);
lean_ctor_set(v_reuseFailAlloc_3554_, 4, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_object* v_k_3559_; lean_object* v_v_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3572_; 
v_k_3559_ = lean_ctor_get(v___x_3439_, 1);
v_v_3560_ = lean_ctor_get(v___x_3439_, 2);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; lean_object* v_unused_3574_; lean_object* v_unused_3575_; 
v_unused_3573_ = lean_ctor_get(v___x_3439_, 4);
lean_dec(v_unused_3573_);
v_unused_3574_ = lean_ctor_get(v___x_3439_, 3);
lean_dec(v_unused_3574_);
v_unused_3575_ = lean_ctor_get(v___x_3439_, 0);
lean_dec(v_unused_3575_);
v___x_3562_ = v___x_3439_;
v_isShared_3563_ = v_isSharedCheck_3572_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_v_3560_);
lean_inc(v_k_3559_);
lean_dec(v___x_3439_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3572_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3567_; 
v___x_3564_ = lean_unsigned_to_nat(3u);
v___x_3565_ = lean_unsigned_to_nat(1u);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 3, v_r_3539_);
lean_ctor_set(v___x_3562_, 2, v_v_3432_);
lean_ctor_set(v___x_3562_, 1, v_k_3431_);
lean_ctor_set(v___x_3562_, 0, v___x_3565_);
v___x_3567_ = v___x_3562_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3571_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3571_, 3, v_r_3539_);
lean_ctor_set(v_reuseFailAlloc_3571_, 4, v_r_3539_);
v___x_3567_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3569_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v___x_3567_);
lean_ctor_set(v___x_3436_, 3, v_l_3538_);
lean_ctor_set(v___x_3436_, 2, v_v_3560_);
lean_ctor_set(v___x_3436_, 1, v_k_3559_);
lean_ctor_set(v___x_3436_, 0, v___x_3564_);
v___x_3569_ = v___x_3436_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_k_3559_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_v_3560_);
lean_ctor_set(v_reuseFailAlloc_3570_, 3, v_l_3538_);
lean_ctor_set(v_reuseFailAlloc_3570_, 4, v___x_3567_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
}
else
{
lean_object* v_r_3576_; 
v_r_3576_ = lean_ctor_get(v___x_3439_, 4);
lean_inc(v_r_3576_);
if (lean_obj_tag(v_r_3576_) == 0)
{
lean_object* v_k_3577_; lean_object* v_v_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3602_; 
v_k_3577_ = lean_ctor_get(v___x_3439_, 1);
v_v_3578_ = lean_ctor_get(v___x_3439_, 2);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3602_ == 0)
{
lean_object* v_unused_3603_; lean_object* v_unused_3604_; lean_object* v_unused_3605_; 
v_unused_3603_ = lean_ctor_get(v___x_3439_, 4);
lean_dec(v_unused_3603_);
v_unused_3604_ = lean_ctor_get(v___x_3439_, 3);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v___x_3439_, 0);
lean_dec(v_unused_3605_);
v___x_3580_ = v___x_3439_;
v_isShared_3581_ = v_isSharedCheck_3602_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_v_3578_);
lean_inc(v_k_3577_);
lean_dec(v___x_3439_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3602_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_k_3582_; lean_object* v_v_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3598_; 
v_k_3582_ = lean_ctor_get(v_r_3576_, 1);
v_v_3583_ = lean_ctor_get(v_r_3576_, 2);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_r_3576_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; lean_object* v_unused_3600_; lean_object* v_unused_3601_; 
v_unused_3599_ = lean_ctor_get(v_r_3576_, 4);
lean_dec(v_unused_3599_);
v_unused_3600_ = lean_ctor_get(v_r_3576_, 3);
lean_dec(v_unused_3600_);
v_unused_3601_ = lean_ctor_get(v_r_3576_, 0);
lean_dec(v_unused_3601_);
v___x_3585_ = v_r_3576_;
v_isShared_3586_ = v_isSharedCheck_3598_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_v_3583_);
lean_inc(v_k_3582_);
lean_dec(v_r_3576_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3598_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3590_; 
v___x_3587_ = lean_unsigned_to_nat(3u);
v___x_3588_ = lean_unsigned_to_nat(1u);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 4, v_l_3538_);
lean_ctor_set(v___x_3585_, 3, v_l_3538_);
lean_ctor_set(v___x_3585_, 2, v_v_3578_);
lean_ctor_set(v___x_3585_, 1, v_k_3577_);
lean_ctor_set(v___x_3585_, 0, v___x_3588_);
v___x_3590_ = v___x_3585_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_k_3577_);
lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_v_3578_);
lean_ctor_set(v_reuseFailAlloc_3597_, 3, v_l_3538_);
lean_ctor_set(v_reuseFailAlloc_3597_, 4, v_l_3538_);
v___x_3590_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3592_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 4, v_l_3538_);
lean_ctor_set(v___x_3580_, 2, v_v_3432_);
lean_ctor_set(v___x_3580_, 1, v_k_3431_);
lean_ctor_set(v___x_3580_, 0, v___x_3588_);
v___x_3592_ = v___x_3580_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_l_3538_);
lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_l_3538_);
v___x_3592_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3594_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v___x_3592_);
lean_ctor_set(v___x_3436_, 3, v___x_3590_);
lean_ctor_set(v___x_3436_, 2, v_v_3583_);
lean_ctor_set(v___x_3436_, 1, v_k_3582_);
lean_ctor_set(v___x_3436_, 0, v___x_3587_);
v___x_3594_ = v___x_3436_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_k_3582_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v_v_3583_);
lean_ctor_set(v_reuseFailAlloc_3595_, 3, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3595_, 4, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
}
else
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3606_ = lean_unsigned_to_nat(2u);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_r_3576_);
lean_ctor_set(v___x_3436_, 3, v___x_3439_);
lean_ctor_set(v___x_3436_, 0, v___x_3606_);
v___x_3608_ = v___x_3436_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3609_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3609_, 3, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3609_, 4, v_r_3576_);
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
else
{
lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3610_ = lean_unsigned_to_nat(1u);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v___x_3439_);
lean_ctor_set(v___x_3436_, 3, v___x_3439_);
lean_ctor_set(v___x_3436_, 0, v___x_3610_);
v___x_3612_ = v___x_3436_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3613_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3613_, 3, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3613_, 4, v___x_3439_);
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
case 1:
{
lean_object* v___x_3615_; 
lean_dec(v_v_3432_);
lean_dec(v_k_3431_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 2, v_v_3428_);
lean_ctor_set(v___x_3436_, 1, v_k_3427_);
v___x_3615_ = v___x_3436_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_size_3430_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3616_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3616_, 3, v_l_3433_);
lean_ctor_set(v_reuseFailAlloc_3616_, 4, v_r_3434_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
default: 
{
lean_object* v___x_3617_; 
lean_dec(v_size_3430_);
v___x_3617_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3427_, v_v_3428_, v_r_3434_);
if (lean_obj_tag(v_l_3433_) == 0)
{
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_size_3618_; lean_object* v_size_3619_; lean_object* v_k_3620_; lean_object* v_v_3621_; lean_object* v_l_3622_; lean_object* v_r_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; 
v_size_3618_ = lean_ctor_get(v_l_3433_, 0);
v_size_3619_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_size_3619_);
v_k_3620_ = lean_ctor_get(v___x_3617_, 1);
lean_inc(v_k_3620_);
v_v_3621_ = lean_ctor_get(v___x_3617_, 2);
lean_inc(v_v_3621_);
v_l_3622_ = lean_ctor_get(v___x_3617_, 3);
lean_inc(v_l_3622_);
v_r_3623_ = lean_ctor_get(v___x_3617_, 4);
lean_inc(v_r_3623_);
v___x_3624_ = lean_unsigned_to_nat(3u);
v___x_3625_ = lean_nat_mul(v___x_3624_, v_size_3618_);
v___x_3626_ = lean_nat_dec_lt(v___x_3625_, v_size_3619_);
lean_dec(v___x_3625_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3631_; 
lean_dec(v_r_3623_);
lean_dec(v_l_3622_);
lean_dec(v_v_3621_);
lean_dec(v_k_3620_);
v___x_3627_ = lean_unsigned_to_nat(1u);
v___x_3628_ = lean_nat_add(v___x_3627_, v_size_3618_);
v___x_3629_ = lean_nat_add(v___x_3628_, v_size_3619_);
lean_dec(v_size_3619_);
lean_dec(v___x_3628_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v___x_3617_);
lean_ctor_set(v___x_3436_, 0, v___x_3629_);
v___x_3631_ = v___x_3436_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3632_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3632_, 3, v_l_3433_);
lean_ctor_set(v_reuseFailAlloc_3632_, 4, v___x_3617_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
else
{
lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3702_; 
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3702_ == 0)
{
lean_object* v_unused_3703_; lean_object* v_unused_3704_; lean_object* v_unused_3705_; lean_object* v_unused_3706_; lean_object* v_unused_3707_; 
v_unused_3703_ = lean_ctor_get(v___x_3617_, 4);
lean_dec(v_unused_3703_);
v_unused_3704_ = lean_ctor_get(v___x_3617_, 3);
lean_dec(v_unused_3704_);
v_unused_3705_ = lean_ctor_get(v___x_3617_, 2);
lean_dec(v_unused_3705_);
v_unused_3706_ = lean_ctor_get(v___x_3617_, 1);
lean_dec(v_unused_3706_);
v_unused_3707_ = lean_ctor_get(v___x_3617_, 0);
lean_dec(v_unused_3707_);
v___x_3634_ = v___x_3617_;
v_isShared_3635_ = v_isSharedCheck_3702_;
goto v_resetjp_3633_;
}
else
{
lean_dec(v___x_3617_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3702_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
if (lean_obj_tag(v_l_3622_) == 0)
{
if (lean_obj_tag(v_r_3623_) == 0)
{
lean_object* v_size_3636_; lean_object* v_k_3637_; lean_object* v_v_3638_; lean_object* v_l_3639_; lean_object* v_r_3640_; lean_object* v_size_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v_size_3636_ = lean_ctor_get(v_l_3622_, 0);
v_k_3637_ = lean_ctor_get(v_l_3622_, 1);
v_v_3638_ = lean_ctor_get(v_l_3622_, 2);
v_l_3639_ = lean_ctor_get(v_l_3622_, 3);
v_r_3640_ = lean_ctor_get(v_l_3622_, 4);
v_size_3641_ = lean_ctor_get(v_r_3623_, 0);
v___x_3642_ = lean_unsigned_to_nat(2u);
v___x_3643_ = lean_nat_mul(v___x_3642_, v_size_3641_);
v___x_3644_ = lean_nat_dec_lt(v_size_3636_, v___x_3643_);
lean_dec(v___x_3643_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3673_; 
lean_inc(v_r_3640_);
lean_inc(v_l_3639_);
lean_inc(v_v_3638_);
lean_inc(v_k_3637_);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_l_3622_);
if (v_isSharedCheck_3673_ == 0)
{
lean_object* v_unused_3674_; lean_object* v_unused_3675_; lean_object* v_unused_3676_; lean_object* v_unused_3677_; lean_object* v_unused_3678_; 
v_unused_3674_ = lean_ctor_get(v_l_3622_, 4);
lean_dec(v_unused_3674_);
v_unused_3675_ = lean_ctor_get(v_l_3622_, 3);
lean_dec(v_unused_3675_);
v_unused_3676_ = lean_ctor_get(v_l_3622_, 2);
lean_dec(v_unused_3676_);
v_unused_3677_ = lean_ctor_get(v_l_3622_, 1);
lean_dec(v_unused_3677_);
v_unused_3678_ = lean_ctor_get(v_l_3622_, 0);
lean_dec(v_unused_3678_);
v___x_3646_ = v_l_3622_;
v_isShared_3647_ = v_isSharedCheck_3673_;
goto v_resetjp_3645_;
}
else
{
lean_dec(v_l_3622_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3673_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3663_; 
v___x_3648_ = lean_unsigned_to_nat(1u);
v___x_3649_ = lean_nat_add(v___x_3648_, v_size_3618_);
v___x_3650_ = lean_nat_add(v___x_3649_, v_size_3619_);
lean_dec(v_size_3619_);
if (lean_obj_tag(v_l_3639_) == 0)
{
lean_object* v_size_3671_; 
v_size_3671_ = lean_ctor_get(v_l_3639_, 0);
lean_inc(v_size_3671_);
v___y_3663_ = v_size_3671_;
goto v___jp_3662_;
}
else
{
lean_object* v___x_3672_; 
v___x_3672_ = lean_unsigned_to_nat(0u);
v___y_3663_ = v___x_3672_;
goto v___jp_3662_;
}
v___jp_3651_:
{
lean_object* v___x_3655_; lean_object* v___x_3657_; 
v___x_3655_ = lean_nat_add(v___y_3652_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec(v___y_3652_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 4, v_r_3623_);
lean_ctor_set(v___x_3646_, 3, v_r_3640_);
lean_ctor_set(v___x_3646_, 2, v_v_3621_);
lean_ctor_set(v___x_3646_, 1, v_k_3620_);
lean_ctor_set(v___x_3646_, 0, v___x_3655_);
v___x_3657_ = v___x_3646_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_k_3620_);
lean_ctor_set(v_reuseFailAlloc_3661_, 2, v_v_3621_);
lean_ctor_set(v_reuseFailAlloc_3661_, 3, v_r_3640_);
lean_ctor_set(v_reuseFailAlloc_3661_, 4, v_r_3623_);
v___x_3657_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3659_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 4, v___x_3657_);
lean_ctor_set(v___x_3634_, 3, v___y_3653_);
lean_ctor_set(v___x_3634_, 2, v_v_3638_);
lean_ctor_set(v___x_3634_, 1, v_k_3637_);
lean_ctor_set(v___x_3634_, 0, v___x_3650_);
v___x_3659_ = v___x_3634_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_k_3637_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_v_3638_);
lean_ctor_set(v_reuseFailAlloc_3660_, 3, v___y_3653_);
lean_ctor_set(v_reuseFailAlloc_3660_, 4, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
v___jp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = lean_nat_add(v___x_3649_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec(v___x_3649_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_l_3639_);
lean_ctor_set(v___x_3436_, 0, v___x_3664_);
v___x_3666_ = v___x_3436_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_l_3433_);
lean_ctor_set(v_reuseFailAlloc_3670_, 4, v_l_3639_);
v___x_3666_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; 
v___x_3667_ = lean_nat_add(v___x_3648_, v_size_3641_);
if (lean_obj_tag(v_r_3640_) == 0)
{
lean_object* v_size_3668_; 
v_size_3668_ = lean_ctor_get(v_r_3640_, 0);
lean_inc(v_size_3668_);
v___y_3652_ = v___x_3667_;
v___y_3653_ = v___x_3666_;
v___y_3654_ = v_size_3668_;
goto v___jp_3651_;
}
else
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_unsigned_to_nat(0u);
v___y_3652_ = v___x_3667_;
v___y_3653_ = v___x_3666_;
v___y_3654_ = v___x_3669_;
goto v___jp_3651_;
}
}
}
}
}
else
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3684_; 
lean_del_object(v___x_3436_);
v___x_3679_ = lean_unsigned_to_nat(1u);
v___x_3680_ = lean_nat_add(v___x_3679_, v_size_3618_);
v___x_3681_ = lean_nat_add(v___x_3680_, v_size_3619_);
lean_dec(v_size_3619_);
v___x_3682_ = lean_nat_add(v___x_3680_, v_size_3636_);
lean_dec(v___x_3680_);
lean_inc_ref(v_l_3433_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 4, v_l_3622_);
lean_ctor_set(v___x_3634_, 3, v_l_3433_);
lean_ctor_set(v___x_3634_, 2, v_v_3432_);
lean_ctor_set(v___x_3634_, 1, v_k_3431_);
lean_ctor_set(v___x_3634_, 0, v___x_3682_);
v___x_3684_ = v___x_3634_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3697_, 3, v_l_3433_);
lean_ctor_set(v_reuseFailAlloc_3697_, 4, v_l_3622_);
v___x_3684_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
v_isSharedCheck_3691_ = !lean_is_exclusive(v_l_3433_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; lean_object* v_unused_3693_; lean_object* v_unused_3694_; lean_object* v_unused_3695_; lean_object* v_unused_3696_; 
v_unused_3692_ = lean_ctor_get(v_l_3433_, 4);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_l_3433_, 3);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_l_3433_, 2);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_l_3433_, 1);
lean_dec(v_unused_3695_);
v_unused_3696_ = lean_ctor_get(v_l_3433_, 0);
lean_dec(v_unused_3696_);
v___x_3686_ = v_l_3433_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_dec(v_l_3433_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v_r_3623_);
lean_ctor_set(v___x_3686_, 3, v___x_3684_);
lean_ctor_set(v___x_3686_, 2, v_v_3621_);
lean_ctor_set(v___x_3686_, 1, v_k_3620_);
lean_ctor_set(v___x_3686_, 0, v___x_3681_);
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_k_3620_);
lean_ctor_set(v_reuseFailAlloc_3690_, 2, v_v_3621_);
lean_ctor_set(v_reuseFailAlloc_3690_, 3, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3690_, 4, v_r_3623_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
}
else
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec_ref_known(v_l_3622_, 5);
lean_del_object(v___x_3634_);
lean_dec(v_v_3621_);
lean_dec(v_k_3620_);
lean_dec(v_size_3619_);
lean_dec_ref_known(v_l_3433_, 5);
lean_del_object(v___x_3436_);
lean_dec(v_v_3432_);
lean_dec(v_k_3431_);
v___x_3698_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7);
v___x_3699_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3698_);
return v___x_3699_;
}
}
else
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
lean_del_object(v___x_3634_);
lean_dec(v_r_3623_);
lean_dec(v_v_3621_);
lean_dec(v_k_3620_);
lean_dec(v_size_3619_);
lean_dec_ref_known(v_l_3433_, 5);
lean_del_object(v___x_3436_);
lean_dec(v_v_3432_);
lean_dec(v_k_3431_);
v___x_3700_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8);
v___x_3701_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3700_);
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_size_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3712_; 
v_size_3708_ = lean_ctor_get(v_l_3433_, 0);
v___x_3709_ = lean_unsigned_to_nat(1u);
v___x_3710_ = lean_nat_add(v___x_3709_, v_size_3708_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v___x_3617_);
lean_ctor_set(v___x_3436_, 0, v___x_3710_);
v___x_3712_ = v___x_3436_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_l_3433_);
lean_ctor_set(v_reuseFailAlloc_3713_, 4, v___x_3617_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
else
{
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_l_3714_; 
v_l_3714_ = lean_ctor_get(v___x_3617_, 3);
lean_inc(v_l_3714_);
if (lean_obj_tag(v_l_3714_) == 0)
{
lean_object* v_r_3715_; 
v_r_3715_ = lean_ctor_get(v___x_3617_, 4);
lean_inc(v_r_3715_);
if (lean_obj_tag(v_r_3715_) == 0)
{
lean_object* v_size_3716_; lean_object* v_k_3717_; lean_object* v_v_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3732_; 
v_size_3716_ = lean_ctor_get(v___x_3617_, 0);
v_k_3717_ = lean_ctor_get(v___x_3617_, 1);
v_v_3718_ = lean_ctor_get(v___x_3617_, 2);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3732_ == 0)
{
lean_object* v_unused_3733_; lean_object* v_unused_3734_; 
v_unused_3733_ = lean_ctor_get(v___x_3617_, 4);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v___x_3617_, 3);
lean_dec(v_unused_3734_);
v___x_3720_ = v___x_3617_;
v_isShared_3721_ = v_isSharedCheck_3732_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_v_3718_);
lean_inc(v_k_3717_);
lean_inc(v_size_3716_);
lean_dec(v___x_3617_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3732_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v_size_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v_size_3722_ = lean_ctor_get(v_l_3714_, 0);
v___x_3723_ = lean_unsigned_to_nat(1u);
v___x_3724_ = lean_nat_add(v___x_3723_, v_size_3716_);
lean_dec(v_size_3716_);
v___x_3725_ = lean_nat_add(v___x_3723_, v_size_3722_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 4, v_l_3714_);
lean_ctor_set(v___x_3720_, 3, v_l_3433_);
lean_ctor_set(v___x_3720_, 2, v_v_3432_);
lean_ctor_set(v___x_3720_, 1, v_k_3431_);
lean_ctor_set(v___x_3720_, 0, v___x_3725_);
v___x_3727_ = v___x_3720_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3731_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3731_, 3, v_l_3433_);
lean_ctor_set(v_reuseFailAlloc_3731_, 4, v_l_3714_);
v___x_3727_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3729_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_r_3715_);
lean_ctor_set(v___x_3436_, 3, v___x_3727_);
lean_ctor_set(v___x_3436_, 2, v_v_3718_);
lean_ctor_set(v___x_3436_, 1, v_k_3717_);
lean_ctor_set(v___x_3436_, 0, v___x_3724_);
v___x_3729_ = v___x_3436_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_k_3717_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_v_3718_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v_r_3715_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_object* v_k_3735_; lean_object* v_v_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3760_; 
v_k_3735_ = lean_ctor_get(v___x_3617_, 1);
v_v_3736_ = lean_ctor_get(v___x_3617_, 2);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3760_ == 0)
{
lean_object* v_unused_3761_; lean_object* v_unused_3762_; lean_object* v_unused_3763_; 
v_unused_3761_ = lean_ctor_get(v___x_3617_, 4);
lean_dec(v_unused_3761_);
v_unused_3762_ = lean_ctor_get(v___x_3617_, 3);
lean_dec(v_unused_3762_);
v_unused_3763_ = lean_ctor_get(v___x_3617_, 0);
lean_dec(v_unused_3763_);
v___x_3738_ = v___x_3617_;
v_isShared_3739_ = v_isSharedCheck_3760_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_v_3736_);
lean_inc(v_k_3735_);
lean_dec(v___x_3617_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3760_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v_k_3740_; lean_object* v_v_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3756_; 
v_k_3740_ = lean_ctor_get(v_l_3714_, 1);
v_v_3741_ = lean_ctor_get(v_l_3714_, 2);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_l_3714_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; 
v_unused_3757_ = lean_ctor_get(v_l_3714_, 4);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_l_3714_, 3);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_l_3714_, 0);
lean_dec(v_unused_3759_);
v___x_3743_ = v_l_3714_;
v_isShared_3744_ = v_isSharedCheck_3756_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_v_3741_);
lean_inc(v_k_3740_);
lean_dec(v_l_3714_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3756_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3748_; 
v___x_3745_ = lean_unsigned_to_nat(3u);
v___x_3746_ = lean_unsigned_to_nat(1u);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 4, v_r_3715_);
lean_ctor_set(v___x_3743_, 3, v_r_3715_);
lean_ctor_set(v___x_3743_, 2, v_v_3432_);
lean_ctor_set(v___x_3743_, 1, v_k_3431_);
lean_ctor_set(v___x_3743_, 0, v___x_3746_);
v___x_3748_ = v___x_3743_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_r_3715_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v_r_3715_);
v___x_3748_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3750_; 
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 3, v_r_3715_);
lean_ctor_set(v___x_3738_, 0, v___x_3746_);
v___x_3750_ = v___x_3738_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v_k_3735_);
lean_ctor_set(v_reuseFailAlloc_3754_, 2, v_v_3736_);
lean_ctor_set(v_reuseFailAlloc_3754_, 3, v_r_3715_);
lean_ctor_set(v_reuseFailAlloc_3754_, 4, v_r_3715_);
v___x_3750_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3752_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v___x_3750_);
lean_ctor_set(v___x_3436_, 3, v___x_3748_);
lean_ctor_set(v___x_3436_, 2, v_v_3741_);
lean_ctor_set(v___x_3436_, 1, v_k_3740_);
lean_ctor_set(v___x_3436_, 0, v___x_3745_);
v___x_3752_ = v___x_3436_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_k_3740_);
lean_ctor_set(v_reuseFailAlloc_3753_, 2, v_v_3741_);
lean_ctor_set(v_reuseFailAlloc_3753_, 3, v___x_3748_);
lean_ctor_set(v_reuseFailAlloc_3753_, 4, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3764_; 
v_r_3764_ = lean_ctor_get(v___x_3617_, 4);
lean_inc(v_r_3764_);
if (lean_obj_tag(v_r_3764_) == 0)
{
lean_object* v_k_3765_; lean_object* v_v_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3778_; 
v_k_3765_ = lean_ctor_get(v___x_3617_, 1);
v_v_3766_ = lean_ctor_get(v___x_3617_, 2);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3778_ == 0)
{
lean_object* v_unused_3779_; lean_object* v_unused_3780_; lean_object* v_unused_3781_; 
v_unused_3779_ = lean_ctor_get(v___x_3617_, 4);
lean_dec(v_unused_3779_);
v_unused_3780_ = lean_ctor_get(v___x_3617_, 3);
lean_dec(v_unused_3780_);
v_unused_3781_ = lean_ctor_get(v___x_3617_, 0);
lean_dec(v_unused_3781_);
v___x_3768_ = v___x_3617_;
v_isShared_3769_ = v_isSharedCheck_3778_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_v_3766_);
lean_inc(v_k_3765_);
lean_dec(v___x_3617_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3778_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3770_ = lean_unsigned_to_nat(3u);
v___x_3771_ = lean_unsigned_to_nat(1u);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 4, v_l_3714_);
lean_ctor_set(v___x_3768_, 2, v_v_3432_);
lean_ctor_set(v___x_3768_, 1, v_k_3431_);
lean_ctor_set(v___x_3768_, 0, v___x_3771_);
v___x_3773_ = v___x_3768_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3777_, 3, v_l_3714_);
lean_ctor_set(v_reuseFailAlloc_3777_, 4, v_l_3714_);
v___x_3773_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3775_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_r_3764_);
lean_ctor_set(v___x_3436_, 3, v___x_3773_);
lean_ctor_set(v___x_3436_, 2, v_v_3766_);
lean_ctor_set(v___x_3436_, 1, v_k_3765_);
lean_ctor_set(v___x_3436_, 0, v___x_3770_);
v___x_3775_ = v___x_3436_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_k_3765_);
lean_ctor_set(v_reuseFailAlloc_3776_, 2, v_v_3766_);
lean_ctor_set(v_reuseFailAlloc_3776_, 3, v___x_3773_);
lean_ctor_set(v_reuseFailAlloc_3776_, 4, v_r_3764_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
else
{
lean_object* v___x_3782_; lean_object* v___x_3784_; 
v___x_3782_ = lean_unsigned_to_nat(2u);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v___x_3617_);
lean_ctor_set(v___x_3436_, 3, v_r_3764_);
lean_ctor_set(v___x_3436_, 0, v___x_3782_);
v___x_3784_ = v___x_3436_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3785_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3785_, 3, v_r_3764_);
lean_ctor_set(v_reuseFailAlloc_3785_, 4, v___x_3617_);
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
else
{
lean_object* v___x_3786_; lean_object* v___x_3788_; 
v___x_3786_ = lean_unsigned_to_nat(1u);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v___x_3617_);
lean_ctor_set(v___x_3436_, 3, v___x_3617_);
lean_ctor_set(v___x_3436_, 0, v___x_3786_);
v___x_3788_ = v___x_3436_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3789_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3789_, 3, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3789_, 4, v___x_3617_);
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
}
}
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_unsigned_to_nat(1u);
v___x_3792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
lean_ctor_set(v___x_3792_, 1, v_k_3427_);
lean_ctor_set(v___x_3792_, 2, v_v_3428_);
lean_ctor_set(v___x_3792_, 3, v_t_3429_);
lean_ctor_set(v___x_3792_, 4, v_t_3429_);
return v___x_3792_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(lean_object* v_init_3793_, lean_object* v_x_3794_){
_start:
{
if (lean_obj_tag(v_x_3794_) == 0)
{
lean_object* v_k_3795_; lean_object* v_v_3796_; lean_object* v_l_3797_; lean_object* v_r_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_k_3795_ = lean_ctor_get(v_x_3794_, 1);
lean_inc(v_k_3795_);
v_v_3796_ = lean_ctor_get(v_x_3794_, 2);
lean_inc(v_v_3796_);
v_l_3797_ = lean_ctor_get(v_x_3794_, 3);
lean_inc(v_l_3797_);
v_r_3798_ = lean_ctor_get(v_x_3794_, 4);
lean_inc(v_r_3798_);
lean_dec_ref_known(v_x_3794_, 5);
v___x_3799_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_3793_, v_l_3797_);
v___x_3800_ = 1;
v___x_3801_ = l_Lean_Name_toString(v_k_3795_, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3802_, 0, v_v_3796_);
v___x_3803_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v___x_3801_, v___x_3802_, v___x_3799_);
v_init_3793_ = v___x_3803_;
v_x_3794_ = v_r_3798_;
goto _start;
}
else
{
return v_init_3793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_m_3805_){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3806_ = lean_box(1);
v___x_3807_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v___x_3806_, v_m_3805_);
v___x_3808_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v___x_3811_, uint8_t v_updateToolchain_3812_, lean_object* v_ws_3813_, lean_object* v_dep_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_baseName_3818_; lean_object* v_name_3819_; lean_object* v_opts_3820_; uint8_t v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v_baseName_3818_ = lean_ctor_get(v___x_3811_, 1);
v_name_3819_ = lean_ctor_get(v_dep_3814_, 0);
v_opts_3820_ = lean_ctor_get(v_dep_3814_, 4);
v___x_3821_ = 0;
lean_inc(v_baseName_3818_);
v___x_3822_ = l_Lean_Name_toString(v_baseName_3818_, v___x_3821_);
v___x_3823_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3824_ = lean_string_append(v___x_3822_, v___x_3823_);
lean_inc(v_name_3819_);
v___x_3825_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3819_, v_updateToolchain_3812_);
v___x_3826_ = lean_string_append(v___x_3824_, v___x_3825_);
lean_dec_ref(v___x_3825_);
v___x_3827_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3828_ = lean_string_append(v___x_3826_, v___x_3827_);
lean_inc(v_opts_3820_);
v___x_3829_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_opts_3820_);
v___x_3830_ = lean_unsigned_to_nat(80u);
v___x_3831_ = l_Lean_Json_pretty(v___x_3829_, v___x_3830_);
v___x_3832_ = lean_string_append(v___x_3828_, v___x_3831_);
lean_dec_ref(v___x_3831_);
v___x_3833_ = 0;
v___x_3834_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3834_, 0, v___x_3832_);
lean_ctor_set_uint8(v___x_3834_, sizeof(void*)*1, v___x_3833_);
lean_inc_ref(v___y_3816_);
v___x_3835_ = lean_apply_2(v___y_3816_, v___x_3834_, lean_box(0));
v___x_3836_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3813_, v___x_3811_, v_dep_3814_, v___y_3815_, v___y_3816_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v___x_3837_, lean_object* v_updateToolchain_3838_, lean_object* v_ws_3839_, lean_object* v_dep_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
uint8_t v_updateToolchain_boxed_3844_; lean_object* v_res_3845_; 
v_updateToolchain_boxed_3844_ = lean_unbox(v_updateToolchain_3838_);
v_res_3845_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v___x_3837_, v_updateToolchain_boxed_3844_, v_ws_3839_, v_dep_3840_, v___y_3841_, v___y_3842_);
lean_dec_ref(v___y_3842_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_a_3846_, lean_object* v_b_3847_){
_start:
{
lean_object* v_next_3848_; 
v_next_3848_ = lean_ctor_get(v_a_3846_, 0);
lean_inc(v_next_3848_);
if (lean_obj_tag(v_next_3848_) == 0)
{
lean_dec_ref(v_a_3846_);
return v_b_3847_;
}
else
{
lean_object* v_upperBound_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3869_; 
v_upperBound_3849_ = lean_ctor_get(v_a_3846_, 1);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_a_3846_);
if (v_isSharedCheck_3869_ == 0)
{
lean_object* v_unused_3870_; 
v_unused_3870_ = lean_ctor_get(v_a_3846_, 0);
lean_dec(v_unused_3870_);
v___x_3851_ = v_a_3846_;
v_isShared_3852_ = v_isSharedCheck_3869_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_upperBound_3849_);
lean_dec(v_a_3846_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3869_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v_val_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3868_; 
v_val_3853_ = lean_ctor_get(v_next_3848_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_next_3848_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3855_ = v_next_3848_;
v_isShared_3856_ = v_isSharedCheck_3868_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_val_3853_);
lean_dec(v_next_3848_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3868_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
uint8_t v___x_3857_; 
v___x_3857_ = lean_nat_dec_lt(v_val_3853_, v_upperBound_3849_);
if (v___x_3857_ == 0)
{
lean_del_object(v___x_3855_);
lean_dec(v_val_3853_);
lean_del_object(v___x_3851_);
lean_dec(v_upperBound_3849_);
return v_b_3847_;
}
else
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3858_ = lean_unsigned_to_nat(1u);
v___x_3859_ = lean_nat_add(v_val_3853_, v___x_3858_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3859_);
v___x_3861_ = v___x_3855_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 0, v___x_3861_);
v___x_3863_ = v___x_3851_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v_upperBound_3849_);
v___x_3863_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_array_push(v_b_3847_, v_val_3853_);
v_a_3846_ = v___x_3863_;
v_b_3847_ = v___x_3864_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_n_3871_, lean_object* v_f_3872_, lean_object* v_xs_3873_, lean_object* v_k_3874_, lean_object* v_acc_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
uint8_t v___x_3879_; 
v___x_3879_ = lean_nat_dec_lt(v_k_3874_, v_n_3871_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
lean_dec(v_k_3874_);
lean_dec_ref(v_f_3872_);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v_acc_3875_);
lean_ctor_set(v___x_3880_, 1, v___y_3876_);
v___x_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
return v___x_3881_;
}
else
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = lean_array_fget_borrowed(v_xs_3873_, v_k_3874_);
lean_inc_ref(v_f_3872_);
lean_inc_ref(v___y_3877_);
lean_inc(v___x_3882_);
v___x_3883_ = lean_apply_4(v_f_3872_, v___x_3882_, v___y_3876_, v___y_3877_, lean_box(0));
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v_fst_3885_; lean_object* v_snd_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v_fst_3885_ = lean_ctor_get(v_a_3884_, 0);
lean_inc(v_fst_3885_);
v_snd_3886_ = lean_ctor_get(v_a_3884_, 1);
lean_inc(v_snd_3886_);
lean_dec(v_a_3884_);
v___x_3887_ = lean_unsigned_to_nat(1u);
v___x_3888_ = lean_nat_add(v_k_3874_, v___x_3887_);
lean_dec(v_k_3874_);
v___x_3889_ = lean_array_push(v_acc_3875_, v_fst_3885_);
v_k_3874_ = v___x_3888_;
v_acc_3875_ = v___x_3889_;
v___y_3876_ = v_snd_3886_;
goto _start;
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec_ref(v_acc_3875_);
lean_dec(v_k_3874_);
lean_dec_ref(v_f_3872_);
v_a_3891_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3883_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3883_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object* v_n_3899_, lean_object* v_f_3900_, lean_object* v_xs_3901_, lean_object* v_k_3902_, lean_object* v_acc_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_3899_, v_f_3900_, v_xs_3901_, v_k_3902_, v_acc_3903_, v___y_3904_, v___y_3905_);
lean_dec_ref(v___y_3905_);
lean_dec_ref(v_xs_3901_);
lean_dec(v_n_3899_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object* v_upperBound_3908_, lean_object* v_fst_3909_, lean_object* v___x_3910_, lean_object* v_leanOpts_3911_, lean_object* v_a_3912_, lean_object* v_b_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_fst_3918_; lean_object* v_snd_3919_; uint8_t v___x_3923_; 
v___x_3923_ = lean_nat_dec_lt(v_a_3912_, v_upperBound_3908_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_dec(v_a_3912_);
lean_dec_ref(v_leanOpts_3911_);
v___x_3924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3924_, 0, v_b_3913_);
lean_ctor_set(v___x_3924_, 1, v___y_3914_);
v___x_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
else
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3926_ = lean_array_fget_borrowed(v_fst_3909_, v_a_3912_);
lean_inc(v___x_3926_);
v___x_3927_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_3926_, v___y_3914_, v___y_3915_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3981_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3930_ = v___x_3927_;
v_isShared_3931_ = v_isSharedCheck_3981_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3981_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v_snd_3932_; lean_object* v___x_3933_; lean_object* v_opts_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v_snd_3932_ = lean_ctor_get(v_a_3928_, 1);
lean_inc(v_snd_3932_);
lean_dec(v_a_3928_);
v___x_3933_ = lean_array_fget_borrowed(v___x_3910_, v_a_3912_);
v_opts_3934_ = lean_ctor_get(v___x_3933_, 4);
v___x_3935_ = lean_unsigned_to_nat(0u);
v___x_3936_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3911_);
lean_inc(v_opts_3934_);
lean_inc(v___x_3926_);
v___x_3937_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_3913_, v___x_3926_, v_opts_3934_, v_leanOpts_3911_, v___x_3923_, v___x_3936_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v_a_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; 
lean_del_object(v___x_3930_);
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
v_a_3939_ = lean_ctor_get(v___x_3937_, 1);
lean_inc(v_a_3939_);
lean_dec_ref_known(v___x_3937_, 2);
v___x_3940_ = lean_array_get_size(v_a_3939_);
v___x_3941_ = lean_nat_dec_lt(v___x_3935_, v___x_3940_);
if (v___x_3941_ == 0)
{
lean_dec(v_a_3939_);
v_fst_3918_ = v_a_3938_;
v_snd_3919_ = v_snd_3932_;
goto v___jp_3917_;
}
else
{
lean_object* v___x_3942_; size_t v___x_3943_; size_t v___x_3944_; lean_object* v___x_3945_; 
v___x_3942_ = lean_box(0);
v___x_3943_ = ((size_t)0ULL);
v___x_3944_ = lean_usize_of_nat(v___x_3940_);
v___x_3945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3939_, v___x_3943_, v___x_3944_, v___x_3942_, v___y_3915_);
lean_dec(v_a_3939_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_dec_ref_known(v___x_3945_, 1);
v_fst_3918_ = v_a_3938_;
v_snd_3919_ = v_snd_3932_;
goto v___jp_3917_;
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec(v_a_3938_);
lean_dec(v_snd_3932_);
lean_dec(v_a_3912_);
lean_dec_ref(v_leanOpts_3911_);
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3945_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3945_);
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
else
{
lean_object* v_a_3954_; lean_object* v___x_3955_; uint8_t v___x_3956_; 
lean_dec(v_snd_3932_);
lean_dec(v_a_3912_);
lean_dec_ref(v_leanOpts_3911_);
v_a_3954_ = lean_ctor_get(v___x_3937_, 1);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3937_, 2);
v___x_3955_ = lean_array_get_size(v_a_3954_);
v___x_3956_ = lean_nat_dec_lt(v___x_3935_, v___x_3955_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; lean_object* v___x_3959_; 
lean_dec(v_a_3954_);
v___x_3957_ = lean_box(0);
if (v_isShared_3931_ == 0)
{
lean_ctor_set_tag(v___x_3930_, 1);
lean_ctor_set(v___x_3930_, 0, v___x_3957_);
v___x_3959_ = v___x_3930_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3957_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
else
{
lean_object* v___x_3961_; size_t v___x_3962_; size_t v___x_3963_; lean_object* v___x_3964_; 
lean_del_object(v___x_3930_);
v___x_3961_ = lean_box(0);
v___x_3962_ = ((size_t)0ULL);
v___x_3963_ = lean_usize_of_nat(v___x_3955_);
v___x_3964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3954_, v___x_3962_, v___x_3963_, v___x_3961_, v___y_3915_);
lean_dec(v_a_3954_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3971_ == 0)
{
lean_object* v_unused_3972_; 
v_unused_3972_ = lean_ctor_get(v___x_3964_, 0);
lean_dec(v_unused_3972_);
v___x_3966_ = v___x_3964_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_dec(v___x_3964_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
lean_ctor_set_tag(v___x_3966_, 1);
lean_ctor_set(v___x_3966_, 0, v___x_3961_);
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3961_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
v_a_3973_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3964_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3964_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v_b_3913_);
lean_dec(v_a_3912_);
lean_dec_ref(v_leanOpts_3911_);
v_a_3982_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3927_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3927_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
v___jp_3917_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = lean_unsigned_to_nat(1u);
v___x_3921_ = lean_nat_add(v_a_3912_, v___x_3920_);
lean_dec(v_a_3912_);
v_a_3912_ = v___x_3921_;
v_b_3913_ = v_fst_3918_;
v___y_3914_ = v_snd_3919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object* v_upperBound_3990_, lean_object* v_fst_3991_, lean_object* v___x_3992_, lean_object* v_leanOpts_3993_, lean_object* v_a_3994_, lean_object* v_b_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_3990_, v_fst_3991_, v___x_3992_, v_leanOpts_3993_, v_a_3994_, v_b_3995_, v___y_3996_, v___y_3997_);
lean_dec_ref(v___y_3997_);
lean_dec_ref(v___x_3992_);
lean_dec_ref(v_fst_3991_);
lean_dec(v_upperBound_3990_);
return v_res_3999_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(lean_object* v___x_4000_, lean_object* v_x_4001_){
_start:
{
lean_object* v_baseName_4002_; lean_object* v_name_4003_; uint8_t v___x_4004_; 
v_baseName_4002_ = lean_ctor_get(v_x_4001_, 1);
v_name_4003_ = lean_ctor_get(v___x_4000_, 0);
v___x_4004_ = lean_name_eq(v_baseName_4002_, v_name_4003_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___x_4005_, lean_object* v_x_4006_){
_start:
{
uint8_t v_res_4007_; lean_object* v_r_4008_; 
v_res_4007_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(v___x_4005_, v_x_4006_);
lean_dec_ref(v_x_4006_);
lean_dec_ref(v___x_4005_);
v_r_4008_ = lean_box(v_res_4007_);
return v_r_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object* v_pkg_4009_, lean_object* v_leanOpts_4010_, uint8_t v_reconfigure_4011_, lean_object* v_as_4012_, size_t v_i_4013_, size_t v_stop_4014_, lean_object* v_b_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
uint8_t v___x_4019_; 
v___x_4019_ = lean_usize_dec_eq(v_i_4013_, v_stop_4014_);
if (v___x_4019_ == 0)
{
lean_object* v_ws_4020_; lean_object* v_depIdxs_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4118_; 
v_ws_4020_ = lean_ctor_get(v_b_4015_, 0);
v_depIdxs_4021_ = lean_ctor_get(v_b_4015_, 1);
v_isSharedCheck_4118_ = !lean_is_exclusive(v_b_4015_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4023_ = v_b_4015_;
v_isShared_4024_ = v_isSharedCheck_4118_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_depIdxs_4021_);
lean_inc(v_ws_4020_);
lean_dec(v_b_4015_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4118_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v_packages_4025_; size_t v___x_4026_; size_t v___x_4027_; lean_object* v___x_4028_; lean_object* v___f_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_packages_4025_ = lean_ctor_get(v_ws_4020_, 4);
v___x_4026_ = ((size_t)1ULL);
v___x_4027_ = lean_usize_sub(v_i_4013_, v___x_4026_);
v___x_4028_ = lean_array_uget_borrowed(v_as_4012_, v___x_4027_);
lean_inc(v___x_4028_);
v___f_4029_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4029_, 0, v___x_4028_);
v___x_4030_ = lean_unsigned_to_nat(0u);
v___x_4031_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_4029_, v_packages_4025_, v___x_4030_);
if (lean_obj_tag(v___x_4031_) == 1)
{
lean_object* v_val_4032_; lean_object* v___x_4033_; lean_object* v___x_4035_; 
v_val_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_val_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v___x_4033_ = lean_array_push(v_depIdxs_4021_, v_val_4032_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 1, v___x_4033_);
v___x_4035_ = v___x_4023_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_ws_4020_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v___x_4033_);
v___x_4035_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
v_i_4013_ = v___x_4027_;
v_b_4015_ = v___x_4035_;
goto _start;
}
}
else
{
lean_object* v_baseName_4038_; lean_object* v_name_4039_; lean_object* v_opts_4040_; uint8_t v___x_4041_; 
lean_dec(v___x_4031_);
v_baseName_4038_ = lean_ctor_get(v_pkg_4009_, 1);
v_name_4039_ = lean_ctor_get(v___x_4028_, 0);
v_opts_4040_ = lean_ctor_get(v___x_4028_, 4);
v___x_4041_ = lean_name_eq(v_baseName_4038_, v_name_4039_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; 
lean_inc_ref(v___y_4017_);
lean_inc_ref(v_ws_4020_);
lean_inc(v___x_4028_);
lean_inc_ref(v_pkg_4009_);
v___x_4042_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_4009_, v___x_4028_, v_ws_4020_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4101_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4045_ = v___x_4042_;
v_isShared_4046_ = v_isSharedCheck_4101_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4042_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4101_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v_fst_4047_; lean_object* v_snd_4048_; lean_object* v___x_4049_; lean_object* v_wsIdx_4050_; lean_object* v___x_4051_; 
v_fst_4047_ = lean_ctor_get(v_a_4043_, 0);
lean_inc(v_fst_4047_);
v_snd_4048_ = lean_ctor_get(v_a_4043_, 1);
lean_inc(v_snd_4048_);
lean_dec(v_a_4043_);
v___x_4049_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_4050_ = lean_array_get_size(v_packages_4025_);
lean_inc_ref(v_leanOpts_4010_);
lean_inc(v_opts_4040_);
v___x_4051_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_4020_, v_fst_4047_, v_opts_4040_, v_leanOpts_4010_, v_reconfigure_4011_, v___x_4049_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v_a_4053_; lean_object* v___x_4054_; lean_object* v___x_4056_; 
lean_del_object(v___x_4045_);
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc(v_a_4052_);
v_a_4053_ = lean_ctor_get(v___x_4051_, 1);
lean_inc(v_a_4053_);
lean_dec_ref_known(v___x_4051_, 2);
v___x_4054_ = lean_array_push(v_depIdxs_4021_, v_wsIdx_4050_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 1, v___x_4054_);
lean_ctor_set(v___x_4023_, 0, v_a_4052_);
v___x_4056_ = v___x_4023_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4052_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v___x_4054_);
v___x_4056_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4057_; uint8_t v___x_4058_; 
v___x_4057_ = lean_array_get_size(v_a_4053_);
v___x_4058_ = lean_nat_dec_lt(v___x_4030_, v___x_4057_);
if (v___x_4058_ == 0)
{
lean_dec(v_a_4053_);
v_i_4013_ = v___x_4027_;
v_b_4015_ = v___x_4056_;
v___y_4016_ = v_snd_4048_;
goto _start;
}
else
{
lean_object* v___x_4060_; size_t v___x_4061_; size_t v___x_4062_; lean_object* v___x_4063_; 
v___x_4060_ = lean_box(0);
v___x_4061_ = ((size_t)0ULL);
v___x_4062_ = lean_usize_of_nat(v___x_4057_);
v___x_4063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4053_, v___x_4061_, v___x_4062_, v___x_4060_, v___y_4017_);
lean_dec(v_a_4053_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_dec_ref_known(v___x_4063_, 1);
v_i_4013_ = v___x_4027_;
v_b_4015_ = v___x_4056_;
v___y_4016_ = v_snd_4048_;
goto _start;
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v___x_4056_);
lean_dec(v_snd_4048_);
lean_dec_ref(v_leanOpts_4010_);
lean_dec_ref(v_pkg_4009_);
v_a_4065_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4063_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4063_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4075_; uint8_t v___x_4076_; 
lean_dec(v_snd_4048_);
lean_del_object(v___x_4023_);
lean_dec_ref(v_depIdxs_4021_);
lean_dec_ref(v_leanOpts_4010_);
lean_dec_ref(v_pkg_4009_);
v_a_4074_ = lean_ctor_get(v___x_4051_, 1);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4051_, 2);
v___x_4075_ = lean_array_get_size(v_a_4074_);
v___x_4076_ = lean_nat_dec_lt(v___x_4030_, v___x_4075_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4079_; 
lean_dec(v_a_4074_);
v___x_4077_ = lean_box(0);
if (v_isShared_4046_ == 0)
{
lean_ctor_set_tag(v___x_4045_, 1);
lean_ctor_set(v___x_4045_, 0, v___x_4077_);
v___x_4079_ = v___x_4045_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
else
{
lean_object* v___x_4081_; size_t v___x_4082_; size_t v___x_4083_; lean_object* v___x_4084_; 
lean_del_object(v___x_4045_);
v___x_4081_ = lean_box(0);
v___x_4082_ = ((size_t)0ULL);
v___x_4083_ = lean_usize_of_nat(v___x_4075_);
v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4074_, v___x_4082_, v___x_4083_, v___x_4081_, v___y_4017_);
lean_dec(v_a_4074_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4091_ == 0)
{
lean_object* v_unused_4092_; 
v_unused_4092_ = lean_ctor_get(v___x_4084_, 0);
lean_dec(v_unused_4092_);
v___x_4086_ = v___x_4084_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_dec(v___x_4084_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
lean_ctor_set_tag(v___x_4086_, 1);
lean_ctor_set(v___x_4086_, 0, v___x_4081_);
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4081_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
v_a_4093_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4084_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4084_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4109_; 
lean_del_object(v___x_4023_);
lean_dec_ref(v_depIdxs_4021_);
lean_dec_ref(v_ws_4020_);
lean_dec_ref(v_leanOpts_4010_);
lean_dec_ref(v_pkg_4009_);
v_a_4102_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4104_ = v___x_4042_;
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4042_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4105_ == 0)
{
v___x_4107_ = v___x_4104_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4102_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
else
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
lean_inc(v_baseName_4038_);
lean_del_object(v___x_4023_);
lean_dec_ref(v_depIdxs_4021_);
lean_dec_ref(v_ws_4020_);
lean_dec(v___y_4016_);
lean_dec_ref(v_leanOpts_4010_);
lean_dec_ref(v_pkg_4009_);
v___x_4110_ = l_Lean_Name_toString(v_baseName_4038_, v___x_4019_);
v___x_4111_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_4112_ = lean_string_append(v___x_4110_, v___x_4111_);
v___x_4113_ = 3;
v___x_4114_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4114_, 0, v___x_4112_);
lean_ctor_set_uint8(v___x_4114_, sizeof(void*)*1, v___x_4113_);
lean_inc_ref(v___y_4017_);
v___x_4115_ = lean_apply_2(v___y_4017_, v___x_4114_, lean_box(0));
v___x_4116_ = lean_box(0);
v___x_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
return v___x_4117_;
}
}
}
}
else
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
lean_dec_ref(v_leanOpts_4010_);
lean_dec_ref(v_pkg_4009_);
v___x_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4119_, 0, v_b_4015_);
lean_ctor_set(v___x_4119_, 1, v___y_4016_);
v___x_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
return v___x_4120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___boxed(lean_object* v_pkg_4121_, lean_object* v_leanOpts_4122_, lean_object* v_reconfigure_4123_, lean_object* v_as_4124_, lean_object* v_i_4125_, lean_object* v_stop_4126_, lean_object* v_b_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
uint8_t v_reconfigure_boxed_4131_; size_t v_i_boxed_4132_; size_t v_stop_boxed_4133_; lean_object* v_res_4134_; 
v_reconfigure_boxed_4131_ = lean_unbox(v_reconfigure_4123_);
v_i_boxed_4132_ = lean_unbox_usize(v_i_4125_);
lean_dec(v_i_4125_);
v_stop_boxed_4133_ = lean_unbox_usize(v_stop_4126_);
lean_dec(v_stop_4126_);
v_res_4134_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4121_, v_leanOpts_4122_, v_reconfigure_boxed_4131_, v_as_4124_, v_i_boxed_4132_, v_stop_boxed_4133_, v_b_4127_, v___y_4128_, v___y_4129_);
lean_dec_ref(v___y_4129_);
lean_dec_ref(v_as_4124_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object* v_leanOpts_4135_, uint8_t v_reconfigure_4136_, lean_object* v_ws_4137_, lean_object* v_i_4138_, lean_object* v_next_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_packages_4143_; lean_object* v_pkg_4144_; lean_object* v_ws_4146_; lean_object* v_depIdxs_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v_____x_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v_depConfigs_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v_s_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v_packages_4143_ = lean_ctor_get(v_ws_4137_, 4);
v_pkg_4144_ = lean_array_fget(v_packages_4143_, v_i_4138_);
lean_dec(v_i_4138_);
v_depConfigs_4165_ = lean_ctor_get(v_pkg_4144_, 12);
v___x_4166_ = lean_array_get_size(v_depConfigs_4165_);
v___x_4167_ = lean_mk_empty_array_with_capacity(v___x_4166_);
lean_inc_ref(v___x_4167_);
lean_inc_ref(v_ws_4137_);
v_s_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_4168_, 0, v_ws_4137_);
lean_ctor_set(v_s_4168_, 1, v___x_4167_);
v___x_4169_ = lean_unsigned_to_nat(0u);
v___x_4170_ = lean_nat_dec_le(v___x_4166_, v___x_4166_);
if (v___x_4170_ == 0)
{
uint8_t v___x_4171_; 
v___x_4171_ = lean_nat_dec_lt(v___x_4169_, v___x_4166_);
if (v___x_4171_ == 0)
{
lean_object* v_ws_4172_; lean_object* v_packages_4173_; lean_object* v___x_4174_; uint8_t v___x_4175_; 
lean_dec_ref_known(v_s_4168_, 2);
v_ws_4172_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4137_, v_pkg_4144_, v___x_4167_);
v_packages_4173_ = lean_ctor_get(v_ws_4172_, 4);
lean_inc_ref(v_packages_4173_);
v___x_4174_ = lean_array_get_size(v_packages_4173_);
lean_dec_ref(v_packages_4173_);
v___x_4175_ = lean_nat_dec_lt(v_next_4139_, v___x_4174_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
lean_dec(v_next_4139_);
lean_dec_ref(v_leanOpts_4135_);
v___x_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4176_, 0, v_ws_4172_);
lean_ctor_set(v___x_4176_, 1, v___y_4140_);
v___x_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
return v___x_4177_;
}
else
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_unsigned_to_nat(1u);
v___x_4179_ = lean_nat_add(v_next_4139_, v___x_4178_);
v_ws_4137_ = v_ws_4172_;
v_i_4138_ = v_next_4139_;
v_next_4139_ = v___x_4179_;
goto _start;
}
}
else
{
size_t v___x_4181_; size_t v___x_4182_; lean_object* v___x_4183_; 
lean_dec_ref(v___x_4167_);
lean_dec_ref(v_ws_4137_);
v___x_4181_ = lean_usize_of_nat(v___x_4166_);
v___x_4182_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4135_);
lean_inc(v_pkg_4144_);
v___x_4183_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4144_, v_leanOpts_4135_, v_reconfigure_4136_, v_depConfigs_4165_, v___x_4181_, v___x_4182_, v_s_4168_, v___y_4140_, v___y_4141_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v_fst_4185_; lean_object* v_snd_4186_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v_fst_4185_ = lean_ctor_get(v_a_4184_, 0);
lean_inc(v_fst_4185_);
v_snd_4186_ = lean_ctor_get(v_a_4184_, 1);
lean_inc(v_snd_4186_);
lean_dec(v_a_4184_);
v_____x_4160_ = v_fst_4185_;
v___y_4161_ = v_snd_4186_;
v___y_4162_ = v___y_4141_;
goto v___jp_4159_;
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_dec(v_pkg_4144_);
lean_dec(v_next_4139_);
lean_dec_ref(v_leanOpts_4135_);
v_a_4187_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4183_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4183_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
}
else
{
uint8_t v___x_4195_; 
v___x_4195_ = lean_nat_dec_lt(v___x_4169_, v___x_4166_);
if (v___x_4195_ == 0)
{
lean_dec_ref_known(v_s_4168_, 2);
v_ws_4146_ = v_ws_4137_;
v_depIdxs_4147_ = v___x_4167_;
v___y_4148_ = v___y_4140_;
v___y_4149_ = v___y_4141_;
goto v___jp_4145_;
}
else
{
size_t v___x_4196_; size_t v___x_4197_; lean_object* v___x_4198_; 
lean_dec_ref(v___x_4167_);
lean_dec_ref(v_ws_4137_);
v___x_4196_ = lean_usize_of_nat(v___x_4166_);
v___x_4197_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4135_);
lean_inc(v_pkg_4144_);
v___x_4198_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4144_, v_leanOpts_4135_, v_reconfigure_4136_, v_depConfigs_4165_, v___x_4196_, v___x_4197_, v_s_4168_, v___y_4140_, v___y_4141_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v_fst_4200_; lean_object* v_snd_4201_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4198_, 1);
v_fst_4200_ = lean_ctor_get(v_a_4199_, 0);
lean_inc(v_fst_4200_);
v_snd_4201_ = lean_ctor_get(v_a_4199_, 1);
lean_inc(v_snd_4201_);
lean_dec(v_a_4199_);
v_____x_4160_ = v_fst_4200_;
v___y_4161_ = v_snd_4201_;
v___y_4162_ = v___y_4141_;
goto v___jp_4159_;
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec(v_pkg_4144_);
lean_dec(v_next_4139_);
lean_dec_ref(v_leanOpts_4135_);
v_a_4202_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4198_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4198_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
}
v___jp_4145_:
{
lean_object* v_ws_4150_; lean_object* v_packages_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v_ws_4150_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4146_, v_pkg_4144_, v_depIdxs_4147_);
v_packages_4151_ = lean_ctor_get(v_ws_4150_, 4);
lean_inc_ref(v_packages_4151_);
v___x_4152_ = lean_array_get_size(v_packages_4151_);
lean_dec_ref(v_packages_4151_);
v___x_4153_ = lean_nat_dec_lt(v_next_4139_, v___x_4152_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_dec(v_next_4139_);
lean_dec_ref(v_leanOpts_4135_);
v___x_4154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4154_, 0, v_ws_4150_);
lean_ctor_set(v___x_4154_, 1, v___y_4148_);
v___x_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
return v___x_4155_;
}
else
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = lean_unsigned_to_nat(1u);
v___x_4157_ = lean_nat_add(v_next_4139_, v___x_4156_);
v_ws_4137_ = v_ws_4150_;
v_i_4138_ = v_next_4139_;
v_next_4139_ = v___x_4157_;
v___y_4140_ = v___y_4148_;
v___y_4141_ = v___y_4149_;
goto _start;
}
}
v___jp_4159_:
{
lean_object* v_ws_4163_; lean_object* v_depIdxs_4164_; 
v_ws_4163_ = lean_ctor_get(v_____x_4160_, 0);
lean_inc_ref(v_ws_4163_);
v_depIdxs_4164_ = lean_ctor_get(v_____x_4160_, 1);
lean_inc_ref(v_depIdxs_4164_);
lean_dec_ref(v_____x_4160_);
v_ws_4146_ = v_ws_4163_;
v_depIdxs_4147_ = v_depIdxs_4164_;
v___y_4148_ = v___y_4161_;
v___y_4149_ = v___y_4162_;
goto v___jp_4145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object* v_leanOpts_4210_, lean_object* v_reconfigure_4211_, lean_object* v_ws_4212_, lean_object* v_i_4213_, lean_object* v_next_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
uint8_t v_reconfigure_boxed_4218_; lean_object* v_res_4219_; 
v_reconfigure_boxed_4218_ = lean_unbox(v_reconfigure_4211_);
v_res_4219_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4210_, v_reconfigure_boxed_4218_, v_ws_4212_, v_i_4213_, v_next_4214_, v___y_4215_, v___y_4216_);
lean_dec_ref(v___y_4216_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4222_, lean_object* v_toUpdate_4223_, lean_object* v_leanOpts_4224_, uint8_t v_updateToolchain_4225_, lean_object* v_a_4226_){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = lean_box(1);
v___x_4229_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4226_, v_ws_4222_, v_toUpdate_4223_, v___x_4228_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v_snd_4231_; uint8_t v___x_4232_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_a_4230_);
lean_dec_ref_known(v___x_4229_, 1);
v_snd_4231_ = lean_ctor_get(v_a_4230_, 1);
lean_inc(v_snd_4231_);
lean_dec(v_a_4230_);
v___x_4232_ = 1;
if (v_updateToolchain_4225_ == 0)
{
lean_object* v_packages_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v_wsIdx_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v_packages_4233_ = lean_ctor_get(v_ws_4222_, 4);
v___x_4234_ = lean_unsigned_to_nat(0u);
v___x_4235_ = lean_array_fget_borrowed(v_packages_4233_, v___x_4234_);
v_wsIdx_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_wsIdx_4236_);
v___x_4237_ = lean_array_get_size(v_packages_4233_);
v___x_4238_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4224_, v___x_4232_, v_ws_4222_, v_wsIdx_4236_, v___x_4237_, v_snd_4231_, v_a_4226_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4256_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4241_ = v___x_4238_;
v_isShared_4242_ = v_isSharedCheck_4256_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4238_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4256_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v_fst_4243_; lean_object* v_snd_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4255_; 
v_fst_4243_ = lean_ctor_get(v_a_4239_, 0);
v_snd_4244_ = lean_ctor_get(v_a_4239_, 1);
v_isSharedCheck_4255_ = !lean_is_exclusive(v_a_4239_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4246_ = v_a_4239_;
v_isShared_4247_ = v_isSharedCheck_4255_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_snd_4244_);
lean_inc(v_fst_4243_);
lean_dec(v_a_4239_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4255_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4248_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4243_);
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4248_);
v___x_4250_ = v___x_4246_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4248_);
lean_ctor_set(v_reuseFailAlloc_4254_, 1, v_snd_4244_);
v___x_4250_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v___x_4252_; 
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 0, v___x_4250_);
v___x_4252_ = v___x_4241_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4250_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
}
else
{
return v___x_4238_;
}
}
else
{
lean_object* v_packages_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v_depConfigs_4260_; lean_object* v___x_4261_; lean_object* v___f_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v_packages_4257_ = lean_ctor_get(v_ws_4222_, 4);
v___x_4258_ = lean_unsigned_to_nat(0u);
v___x_4259_ = lean_array_fget_borrowed(v_packages_4257_, v___x_4258_);
v_depConfigs_4260_ = lean_ctor_get(v___x_4259_, 12);
v___x_4261_ = lean_box(v_updateToolchain_4225_);
lean_inc_ref(v_ws_4222_);
lean_inc(v___x_4259_);
v___f_4262_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4262_, 0, v___x_4259_);
lean_closure_set(v___f_4262_, 1, v___x_4261_);
lean_closure_set(v___f_4262_, 2, v_ws_4222_);
v___x_4263_ = lean_array_get_size(v_depConfigs_4260_);
lean_inc_ref(v_depConfigs_4260_);
v___x_4264_ = l_Array_reverse___redArg(v_depConfigs_4260_);
v___x_4265_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4266_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4263_, v___f_4262_, v___x_4264_, v___x_4258_, v___x_4265_, v_snd_4231_, v_a_4226_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v_fst_4268_; lean_object* v_snd_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4341_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v___x_4266_, 1);
v_fst_4268_ = lean_ctor_get(v_a_4267_, 0);
v_snd_4269_ = lean_ctor_get(v_a_4267_, 1);
v_isSharedCheck_4341_ = !lean_is_exclusive(v_a_4267_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4271_ = v_a_4267_;
v_isShared_4272_ = v_isSharedCheck_4341_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_snd_4269_);
lean_inc(v_fst_4268_);
lean_dec(v_a_4267_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4341_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4273_; 
lean_inc_ref(v_ws_4222_);
v___x_4273_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4226_, v_ws_4222_, v_fst_4268_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
lean_dec_ref_known(v___x_4273_, 1);
v___x_4274_ = lean_array_get_size(v_packages_4257_);
lean_inc_ref(v_leanOpts_4224_);
v___x_4275_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4263_, v_fst_4268_, v___x_4264_, v_leanOpts_4224_, v___x_4258_, v_ws_4222_, v_snd_4269_, v_a_4226_);
lean_dec_ref(v___x_4264_);
lean_dec(v_fst_4268_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4324_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4324_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4324_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v_fst_4280_; lean_object* v_snd_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4323_; 
v_fst_4280_ = lean_ctor_get(v_a_4276_, 0);
v_snd_4281_ = lean_ctor_get(v_a_4276_, 1);
v_isSharedCheck_4323_ = !lean_is_exclusive(v_a_4276_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4283_ = v_a_4276_;
v_isShared_4284_ = v_isSharedCheck_4323_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_snd_4281_);
lean_inc(v_fst_4280_);
lean_dec(v_a_4276_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4323_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v_packages_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4290_; 
v_packages_4285_ = lean_ctor_get(v_fst_4280_, 4);
v___x_4286_ = lean_array_get_size(v_packages_4285_);
v___x_4287_ = lean_array_fget(v_packages_4285_, v___x_4258_);
v___x_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4274_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 1, v___x_4286_);
lean_ctor_set(v___x_4271_, 0, v___x_4288_);
v___x_4290_ = v___x_4271_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4288_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v___x_4286_);
v___x_4290_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; 
v___x_4291_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4290_, v___x_4265_);
v___x_4292_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4280_, v___x_4287_, v___x_4291_);
v___x_4293_ = lean_nat_dec_eq(v___x_4274_, v___x_4286_);
if (v___x_4293_ == 0)
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
lean_del_object(v___x_4283_);
lean_del_object(v___x_4278_);
v___x_4294_ = lean_unsigned_to_nat(1u);
v___x_4295_ = lean_nat_add(v___x_4274_, v___x_4294_);
v___x_4296_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4224_, v___x_4232_, v___x_4292_, v___x_4274_, v___x_4295_, v_snd_4281_, v_a_4226_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4314_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4314_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4314_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v_fst_4301_; lean_object* v_snd_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4313_; 
v_fst_4301_ = lean_ctor_get(v_a_4297_, 0);
v_snd_4302_ = lean_ctor_get(v_a_4297_, 1);
v_isSharedCheck_4313_ = !lean_is_exclusive(v_a_4297_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4304_ = v_a_4297_;
v_isShared_4305_ = v_isSharedCheck_4313_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_snd_4302_);
lean_inc(v_fst_4301_);
lean_dec(v_a_4297_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4313_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4306_; lean_object* v___x_4308_; 
v___x_4306_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4301_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4306_);
v___x_4308_ = v___x_4304_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4306_);
lean_ctor_set(v_reuseFailAlloc_4312_, 1, v_snd_4302_);
v___x_4308_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
lean_object* v___x_4310_; 
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v___x_4308_);
v___x_4310_ = v___x_4299_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
}
else
{
return v___x_4296_;
}
}
else
{
lean_object* v___x_4315_; lean_object* v___x_4317_; 
lean_dec_ref(v_leanOpts_4224_);
v___x_4315_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4292_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4315_);
v___x_4317_ = v___x_4283_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4315_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v_snd_4281_);
v___x_4317_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
lean_object* v___x_4319_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v___x_4317_);
v___x_4319_ = v___x_4278_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_del_object(v___x_4271_);
lean_dec_ref(v_leanOpts_4224_);
v_a_4325_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4275_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4275_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_del_object(v___x_4271_);
lean_dec(v_snd_4269_);
lean_dec(v_fst_4268_);
lean_dec_ref(v___x_4264_);
lean_dec_ref(v_leanOpts_4224_);
lean_dec_ref(v_ws_4222_);
v_a_4333_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4273_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4273_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
lean_dec_ref(v___x_4264_);
lean_dec_ref(v_leanOpts_4224_);
lean_dec_ref(v_ws_4222_);
v_a_4342_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4266_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4266_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
lean_dec_ref(v_leanOpts_4224_);
lean_dec_ref(v_ws_4222_);
v_a_4350_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4229_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4229_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4358_, lean_object* v_toUpdate_4359_, lean_object* v_leanOpts_4360_, lean_object* v_updateToolchain_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_){
_start:
{
uint8_t v_updateToolchain_boxed_4364_; lean_object* v_res_4365_; 
v_updateToolchain_boxed_4364_ = lean_unbox(v_updateToolchain_4361_);
v_res_4365_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4358_, v_toUpdate_4359_, v_leanOpts_4360_, v_updateToolchain_boxed_4364_, v_a_4362_);
lean_dec_ref(v_a_4362_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_leanOpts_4366_, uint8_t v_reconfigure_4367_, lean_object* v_ws_4368_, lean_object* v_i_4369_, lean_object* v_i__lt_4370_, lean_object* v_next_4371_, lean_object* v_lt__next_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v___x_4376_; 
v___x_4376_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4366_, v_reconfigure_4367_, v_ws_4368_, v_i_4369_, v_next_4371_, v___y_4373_, v___y_4374_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_leanOpts_4377_, lean_object* v_reconfigure_4378_, lean_object* v_ws_4379_, lean_object* v_i_4380_, lean_object* v_i__lt_4381_, lean_object* v_next_4382_, lean_object* v_lt__next_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
uint8_t v_reconfigure_boxed_4387_; lean_object* v_res_4388_; 
v_reconfigure_boxed_4387_ = lean_unbox(v_reconfigure_4378_);
v_res_4388_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4377_, v_reconfigure_boxed_4387_, v_ws_4379_, v_i_4380_, v_i__lt_4381_, v_next_4382_, v_lt__next_4383_, v___y_4384_, v___y_4385_);
lean_dec_ref(v___y_4385_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_00_u03b1_4389_, lean_object* v_00_u03b2_4390_, lean_object* v_n_4391_, lean_object* v_f_4392_, lean_object* v_xs_4393_, lean_object* v_k_4394_, lean_object* v_h_4395_, lean_object* v_acc_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4391_, v_f_4392_, v_xs_4393_, v_k_4394_, v_acc_4396_, v___y_4397_, v___y_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_00_u03b1_4401_, lean_object* v_00_u03b2_4402_, lean_object* v_n_4403_, lean_object* v_f_4404_, lean_object* v_xs_4405_, lean_object* v_k_4406_, lean_object* v_h_4407_, lean_object* v_acc_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_00_u03b1_4401_, v_00_u03b2_4402_, v_n_4403_, v_f_4404_, v_xs_4405_, v_k_4406_, v_h_4407_, v_acc_4408_, v___y_4409_, v___y_4410_);
lean_dec_ref(v___y_4410_);
lean_dec_ref(v_xs_4405_);
lean_dec(v_n_4403_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_inst_4413_, lean_object* v_R_4414_, lean_object* v_a_4415_, lean_object* v_b_4416_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_a_4415_, v_b_4416_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_upperBound_4418_, lean_object* v_fst_4419_, lean_object* v___x_4420_, lean_object* v_leanOpts_4421_, lean_object* v_inst_4422_, lean_object* v_R_4423_, lean_object* v_a_4424_, lean_object* v_b_4425_, lean_object* v_c_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v___x_4430_; 
v___x_4430_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4418_, v_fst_4419_, v___x_4420_, v_leanOpts_4421_, v_a_4424_, v_b_4425_, v___y_4427_, v___y_4428_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_upperBound_4431_, lean_object* v_fst_4432_, lean_object* v___x_4433_, lean_object* v_leanOpts_4434_, lean_object* v_inst_4435_, lean_object* v_R_4436_, lean_object* v_a_4437_, lean_object* v_b_4438_, lean_object* v_c_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4431_, v_fst_4432_, v___x_4433_, v_leanOpts_4434_, v_inst_4435_, v_R_4436_, v_a_4437_, v_b_4438_, v_c_4439_, v___y_4440_, v___y_4441_);
lean_dec_ref(v___y_4441_);
lean_dec_ref(v___x_4433_);
lean_dec_ref(v_fst_4432_);
lean_dec(v_upperBound_4431_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_start_4444_, lean_object* v_pkg_4445_, lean_object* v_leanOpts_4446_, uint8_t v_reconfigure_4447_, lean_object* v_as_4448_, size_t v_i_4449_, size_t v_stop_4450_, lean_object* v_b_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v___x_4455_; 
v___x_4455_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4445_, v_leanOpts_4446_, v_reconfigure_4447_, v_as_4448_, v_i_4449_, v_stop_4450_, v_b_4451_, v___y_4452_, v___y_4453_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_start_4456_, lean_object* v_pkg_4457_, lean_object* v_leanOpts_4458_, lean_object* v_reconfigure_4459_, lean_object* v_as_4460_, lean_object* v_i_4461_, lean_object* v_stop_4462_, lean_object* v_b_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
uint8_t v_reconfigure_boxed_4467_; size_t v_i_boxed_4468_; size_t v_stop_boxed_4469_; lean_object* v_res_4470_; 
v_reconfigure_boxed_4467_ = lean_unbox(v_reconfigure_4459_);
v_i_boxed_4468_ = lean_unbox_usize(v_i_4461_);
lean_dec(v_i_4461_);
v_stop_boxed_4469_ = lean_unbox_usize(v_stop_4462_);
lean_dec(v_stop_4462_);
v_res_4470_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_start_4456_, v_pkg_4457_, v_leanOpts_4458_, v_reconfigure_boxed_4467_, v_as_4460_, v_i_boxed_4468_, v_stop_boxed_4469_, v_b_4463_, v___y_4464_, v___y_4465_);
lean_dec_ref(v___y_4465_);
lean_dec_ref(v_as_4460_);
lean_dec(v_start_4456_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_4471_, lean_object* v_msg_4472_){
_start:
{
lean_object* v___x_4473_; 
v___x_4473_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v_msg_4472_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object* v_00_u03b2_4474_, lean_object* v_k_4475_, lean_object* v_v_4476_, lean_object* v_t_4477_){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_4475_, v_v_4476_, v_t_4477_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object* v_init_4479_, lean_object* v_t_4480_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_4479_, v_t_4480_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4482_, lean_object* v_as_4483_, size_t v_i_4484_, size_t v_stop_4485_, lean_object* v_b_4486_){
_start:
{
lean_object* v___y_4488_; uint8_t v___x_4492_; 
v___x_4492_ = lean_usize_dec_eq(v_i_4484_, v_stop_4485_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; lean_object* v_baseName_4494_; lean_object* v_relConfigFile_4495_; lean_object* v_relManifestFile_4496_; lean_object* v___x_4497_; 
v___x_4493_ = lean_array_uget_borrowed(v_as_4483_, v_i_4484_);
v_baseName_4494_ = lean_ctor_get(v___x_4493_, 1);
v_relConfigFile_4495_ = lean_ctor_get(v___x_4493_, 8);
v_relManifestFile_4496_ = lean_ctor_get(v___x_4493_, 9);
v___x_4497_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4482_, v_baseName_4494_);
if (lean_obj_tag(v___x_4497_) == 0)
{
v___y_4488_ = v_b_4486_;
goto v___jp_4487_;
}
else
{
lean_object* v_val_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4519_; 
v_val_4498_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4500_ = v___x_4497_;
v_isShared_4501_ = v_isSharedCheck_4519_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_val_4498_);
lean_dec(v___x_4497_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4519_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v_name_4502_; lean_object* v_scope_4503_; uint8_t v_inherited_4504_; lean_object* v_src_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4516_; 
v_name_4502_ = lean_ctor_get(v_val_4498_, 0);
v_scope_4503_ = lean_ctor_get(v_val_4498_, 1);
v_inherited_4504_ = lean_ctor_get_uint8(v_val_4498_, sizeof(void*)*5);
v_src_4505_ = lean_ctor_get(v_val_4498_, 4);
v_isSharedCheck_4516_ = !lean_is_exclusive(v_val_4498_);
if (v_isSharedCheck_4516_ == 0)
{
lean_object* v_unused_4517_; lean_object* v_unused_4518_; 
v_unused_4517_ = lean_ctor_get(v_val_4498_, 3);
lean_dec(v_unused_4517_);
v_unused_4518_ = lean_ctor_get(v_val_4498_, 2);
lean_dec(v_unused_4518_);
v___x_4507_ = v_val_4498_;
v_isShared_4508_ = v_isSharedCheck_4516_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_src_4505_);
lean_inc(v_scope_4503_);
lean_inc(v_name_4502_);
lean_dec(v_val_4498_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4516_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
lean_inc_ref(v_relManifestFile_4496_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 0, v_relManifestFile_4496_);
v___x_4510_ = v___x_4500_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_relManifestFile_4496_);
v___x_4510_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4512_; 
lean_inc_ref(v_relConfigFile_4495_);
if (v_isShared_4508_ == 0)
{
lean_ctor_set(v___x_4507_, 3, v___x_4510_);
lean_ctor_set(v___x_4507_, 2, v_relConfigFile_4495_);
v___x_4512_ = v___x_4507_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_name_4502_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_scope_4503_);
lean_ctor_set(v_reuseFailAlloc_4514_, 2, v_relConfigFile_4495_);
lean_ctor_set(v_reuseFailAlloc_4514_, 3, v___x_4510_);
lean_ctor_set(v_reuseFailAlloc_4514_, 4, v_src_4505_);
lean_ctor_set_uint8(v_reuseFailAlloc_4514_, sizeof(void*)*5, v_inherited_4504_);
v___x_4512_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
lean_object* v___x_4513_; 
v___x_4513_ = lean_array_push(v_b_4486_, v___x_4512_);
v___y_4488_ = v___x_4513_;
goto v___jp_4487_;
}
}
}
}
}
}
else
{
return v_b_4486_;
}
v___jp_4487_:
{
size_t v___x_4489_; size_t v___x_4490_; 
v___x_4489_ = ((size_t)1ULL);
v___x_4490_ = lean_usize_add(v_i_4484_, v___x_4489_);
v_i_4484_ = v___x_4490_;
v_b_4486_ = v___y_4488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4520_, lean_object* v_as_4521_, lean_object* v_i_4522_, lean_object* v_stop_4523_, lean_object* v_b_4524_){
_start:
{
size_t v_i_boxed_4525_; size_t v_stop_boxed_4526_; lean_object* v_res_4527_; 
v_i_boxed_4525_ = lean_unbox_usize(v_i_4522_);
lean_dec(v_i_4522_);
v_stop_boxed_4526_ = lean_unbox_usize(v_stop_4523_);
lean_dec(v_stop_4523_);
v_res_4527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4520_, v_as_4521_, v_i_boxed_4525_, v_stop_boxed_4526_, v_b_4524_);
lean_dec_ref(v_as_4521_);
lean_dec(v_entries_4520_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4528_, lean_object* v_entries_4529_){
_start:
{
lean_object* v_packages_4531_; lean_object* v___y_4533_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; uint8_t v___x_4551_; 
v_packages_4531_ = lean_ctor_get(v_ws_4528_, 4);
v___x_4548_ = lean_unsigned_to_nat(0u);
v___x_4549_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4550_ = lean_array_get_size(v_packages_4531_);
v___x_4551_ = lean_nat_dec_lt(v___x_4548_, v___x_4550_);
if (v___x_4551_ == 0)
{
v___y_4533_ = v___x_4549_;
goto v___jp_4532_;
}
else
{
uint8_t v___x_4552_; 
v___x_4552_ = lean_nat_dec_le(v___x_4550_, v___x_4550_);
if (v___x_4552_ == 0)
{
if (v___x_4551_ == 0)
{
v___y_4533_ = v___x_4549_;
goto v___jp_4532_;
}
else
{
size_t v___x_4553_; size_t v___x_4554_; lean_object* v___x_4555_; 
v___x_4553_ = ((size_t)0ULL);
v___x_4554_ = lean_usize_of_nat(v___x_4550_);
v___x_4555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4529_, v_packages_4531_, v___x_4553_, v___x_4554_, v___x_4549_);
v___y_4533_ = v___x_4555_;
goto v___jp_4532_;
}
}
else
{
size_t v___x_4556_; size_t v___x_4557_; lean_object* v___x_4558_; 
v___x_4556_ = ((size_t)0ULL);
v___x_4557_ = lean_usize_of_nat(v___x_4550_);
v___x_4558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4529_, v_packages_4531_, v___x_4556_, v___x_4557_, v___x_4549_);
v___y_4533_ = v___x_4558_;
goto v___jp_4532_;
}
}
v___jp_4532_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v_config_4536_; lean_object* v_baseName_4537_; lean_object* v_dir_4538_; lean_object* v_relManifestFile_4539_; lean_object* v_toWorkspaceConfig_4540_; uint8_t v_fixedToolchain_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v_manifest_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4534_ = lean_unsigned_to_nat(0u);
v___x_4535_ = lean_array_fget_borrowed(v_packages_4531_, v___x_4534_);
v_config_4536_ = lean_ctor_get(v___x_4535_, 6);
v_baseName_4537_ = lean_ctor_get(v___x_4535_, 1);
v_dir_4538_ = lean_ctor_get(v___x_4535_, 4);
v_relManifestFile_4539_ = lean_ctor_get(v___x_4535_, 9);
v_toWorkspaceConfig_4540_ = lean_ctor_get(v_config_4536_, 0);
v_fixedToolchain_4541_ = lean_ctor_get_uint8(v_config_4536_, sizeof(void*)*28 + 6);
v___x_4542_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4540_);
v___x_4543_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4540_);
v___x_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
lean_inc(v_baseName_4537_);
v_manifest_4545_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4545_, 0, v_baseName_4537_);
lean_ctor_set(v_manifest_4545_, 1, v___x_4542_);
lean_ctor_set(v_manifest_4545_, 2, v___x_4544_);
lean_ctor_set(v_manifest_4545_, 3, v___y_4533_);
lean_ctor_set_uint8(v_manifest_4545_, sizeof(void*)*4, v_fixedToolchain_4541_);
lean_inc_ref(v_relManifestFile_4539_);
lean_inc_ref(v_dir_4538_);
v___x_4546_ = l_Lake_joinRelative(v_dir_4538_, v_relManifestFile_4539_);
v___x_4547_ = l_Lake_Manifest_save(v_manifest_4545_, v___x_4546_);
lean_dec_ref(v___x_4546_);
return v___x_4547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4559_, lean_object* v_entries_4560_, lean_object* v_a_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4559_, v_entries_4560_);
lean_dec(v_entries_4560_);
lean_dec_ref(v_ws_4559_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4563_, lean_object* v_as_4564_, size_t v_i_4565_, size_t v_stop_4566_, lean_object* v_b_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_a_4572_; lean_object* v___y_4577_; uint8_t v___x_4579_; 
v___x_4579_ = lean_usize_dec_eq(v_i_4565_, v_stop_4566_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_6568__overap_4582_; lean_object* v___x_4583_; 
v___x_4580_ = lean_unsigned_to_nat(0u);
v___x_4581_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_6568__overap_4582_ = lean_array_uget_borrowed(v_as_4564_, v_i_4565_);
lean_inc(v___x_6568__overap_4582_);
lean_inc(v___y_4568_);
lean_inc_ref(v_pkg_4563_);
v___x_4583_ = lean_apply_4(v___x_6568__overap_4582_, v_pkg_4563_, v___y_4568_, v___x_4581_, lean_box(0));
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v_a_4585_; lean_object* v___x_4586_; uint8_t v___x_4587_; 
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
lean_inc(v_a_4584_);
v_a_4585_ = lean_ctor_get(v___x_4583_, 1);
lean_inc(v_a_4585_);
lean_dec_ref_known(v___x_4583_, 2);
v___x_4586_ = lean_array_get_size(v_a_4585_);
v___x_4587_ = lean_nat_dec_lt(v___x_4580_, v___x_4586_);
if (v___x_4587_ == 0)
{
lean_dec(v_a_4585_);
v_a_4572_ = v_a_4584_;
goto v___jp_4571_;
}
else
{
lean_object* v___x_4588_; size_t v___x_4589_; size_t v___x_4590_; lean_object* v___x_4591_; 
v___x_4588_ = lean_box(0);
v___x_4589_ = ((size_t)0ULL);
v___x_4590_ = lean_usize_of_nat(v___x_4586_);
v___x_4591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4585_, v___x_4589_, v___x_4590_, v___x_4588_, v___y_4569_);
lean_dec(v_a_4585_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_dec_ref_known(v___x_4591_, 1);
v_a_4572_ = v_a_4584_;
goto v___jp_4571_;
}
else
{
lean_dec(v_a_4584_);
v___y_4577_ = v___x_4591_;
goto v___jp_4576_;
}
}
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4593_; uint8_t v___x_4594_; 
v_a_4592_ = lean_ctor_get(v___x_4583_, 1);
lean_inc(v_a_4592_);
lean_dec_ref_known(v___x_4583_, 2);
v___x_4593_ = lean_array_get_size(v_a_4592_);
v___x_4594_ = lean_nat_dec_lt(v___x_4580_, v___x_4593_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
lean_dec(v_a_4592_);
lean_dec_ref(v_pkg_4563_);
v___x_4595_ = lean_box(0);
v___x_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
else
{
lean_object* v___x_4597_; size_t v___x_4598_; size_t v___x_4599_; lean_object* v___x_4600_; 
v___x_4597_ = lean_box(0);
v___x_4598_ = ((size_t)0ULL);
v___x_4599_ = lean_usize_of_nat(v___x_4593_);
v___x_4600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4592_, v___x_4598_, v___x_4599_, v___x_4597_, v___y_4569_);
lean_dec(v_a_4592_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
lean_dec_ref(v_pkg_4563_);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4600_);
if (v_isSharedCheck_4607_ == 0)
{
lean_object* v_unused_4608_; 
v_unused_4608_ = lean_ctor_get(v___x_4600_, 0);
lean_dec(v_unused_4608_);
v___x_4602_ = v___x_4600_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_dec(v___x_4600_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
lean_ctor_set_tag(v___x_4602_, 1);
lean_ctor_set(v___x_4602_, 0, v___x_4597_);
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4597_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
else
{
v___y_4577_ = v___x_4600_;
goto v___jp_4576_;
}
}
}
}
else
{
lean_object* v___x_4609_; 
lean_dec_ref(v_pkg_4563_);
v___x_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4609_, 0, v_b_4567_);
return v___x_4609_;
}
v___jp_4571_:
{
size_t v___x_4573_; size_t v___x_4574_; 
v___x_4573_ = ((size_t)1ULL);
v___x_4574_ = lean_usize_add(v_i_4565_, v___x_4573_);
v_i_4565_ = v___x_4574_;
v_b_4567_ = v_a_4572_;
goto _start;
}
v___jp_4576_:
{
if (lean_obj_tag(v___y_4577_) == 0)
{
lean_object* v_a_4578_; 
v_a_4578_ = lean_ctor_get(v___y_4577_, 0);
lean_inc(v_a_4578_);
lean_dec_ref_known(v___y_4577_, 1);
v_a_4572_ = v_a_4578_;
goto v___jp_4571_;
}
else
{
lean_dec_ref(v_pkg_4563_);
return v___y_4577_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4610_, lean_object* v_as_4611_, lean_object* v_i_4612_, lean_object* v_stop_4613_, lean_object* v_b_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
size_t v_i_boxed_4618_; size_t v_stop_boxed_4619_; lean_object* v_res_4620_; 
v_i_boxed_4618_ = lean_unbox_usize(v_i_4612_);
lean_dec(v_i_4612_);
v_stop_boxed_4619_ = lean_unbox_usize(v_stop_4613_);
lean_dec(v_stop_4613_);
v_res_4620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4610_, v_as_4611_, v_i_boxed_4618_, v_stop_boxed_4619_, v_b_4614_, v___y_4615_, v___y_4616_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v_as_4611_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v_baseName_4626_; lean_object* v_postUpdateHooks_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; uint8_t v___x_4630_; 
v_baseName_4626_ = lean_ctor_get(v_pkg_4622_, 1);
v_postUpdateHooks_4627_ = lean_ctor_get(v_pkg_4622_, 20);
lean_inc_ref(v_postUpdateHooks_4627_);
v___x_4628_ = lean_array_get_size(v_postUpdateHooks_4627_);
v___x_4629_ = lean_unsigned_to_nat(0u);
v___x_4630_ = lean_nat_dec_eq(v___x_4628_, v___x_4629_);
if (v___x_4630_ == 0)
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; uint8_t v___x_4638_; 
lean_inc(v_baseName_4626_);
v___x_4631_ = l_Lean_Name_toString(v_baseName_4626_, v___x_4630_);
v___x_4632_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4633_ = lean_string_append(v___x_4631_, v___x_4632_);
v___x_4634_ = 1;
v___x_4635_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4635_, 0, v___x_4633_);
lean_ctor_set_uint8(v___x_4635_, sizeof(void*)*1, v___x_4634_);
lean_inc_ref(v_a_4624_);
v___x_4636_ = lean_apply_2(v_a_4624_, v___x_4635_, lean_box(0));
v___x_4637_ = lean_box(0);
v___x_4638_ = lean_nat_dec_lt(v___x_4629_, v___x_4628_);
if (v___x_4638_ == 0)
{
lean_object* v___x_4639_; 
lean_dec_ref(v_postUpdateHooks_4627_);
lean_dec_ref(v_pkg_4622_);
v___x_4639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4637_);
return v___x_4639_;
}
else
{
uint8_t v___x_4640_; 
v___x_4640_ = lean_nat_dec_le(v___x_4628_, v___x_4628_);
if (v___x_4640_ == 0)
{
if (v___x_4638_ == 0)
{
lean_object* v___x_4641_; 
lean_dec_ref(v_postUpdateHooks_4627_);
lean_dec_ref(v_pkg_4622_);
v___x_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4641_, 0, v___x_4637_);
return v___x_4641_;
}
else
{
size_t v___x_4642_; size_t v___x_4643_; lean_object* v___x_4644_; 
v___x_4642_ = ((size_t)0ULL);
v___x_4643_ = lean_usize_of_nat(v___x_4628_);
v___x_4644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4622_, v_postUpdateHooks_4627_, v___x_4642_, v___x_4643_, v___x_4637_, v_a_4623_, v_a_4624_);
lean_dec_ref(v_postUpdateHooks_4627_);
return v___x_4644_;
}
}
else
{
size_t v___x_4645_; size_t v___x_4646_; lean_object* v___x_4647_; 
v___x_4645_ = ((size_t)0ULL);
v___x_4646_ = lean_usize_of_nat(v___x_4628_);
v___x_4647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4622_, v_postUpdateHooks_4627_, v___x_4645_, v___x_4646_, v___x_4637_, v_a_4623_, v_a_4624_);
lean_dec_ref(v_postUpdateHooks_4627_);
return v___x_4647_;
}
}
}
else
{
lean_object* v___x_4648_; lean_object* v___x_4649_; 
lean_dec_ref(v_postUpdateHooks_4627_);
lean_dec_ref(v_pkg_4622_);
v___x_4648_ = lean_box(0);
v___x_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
return v___x_4649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4650_, v_a_4651_, v_a_4652_);
lean_dec_ref(v_a_4652_);
lean_dec(v_a_4651_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4655_, lean_object* v_ws_4656_, lean_object* v_toUpdate_4657_, lean_object* v_leanOpts_4658_, uint8_t v_updateToolchain_4659_){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = lean_box(1);
v___x_4662_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4655_, v_ws_4656_, v_toUpdate_4657_, v___x_4661_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v_snd_4664_; uint8_t v___x_4665_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref_known(v___x_4662_, 1);
v_snd_4664_ = lean_ctor_get(v_a_4663_, 1);
lean_inc(v_snd_4664_);
lean_dec(v_a_4663_);
v___x_4665_ = 1;
if (v_updateToolchain_4659_ == 0)
{
lean_object* v_packages_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v_wsIdx_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v_packages_4666_ = lean_ctor_get(v_ws_4656_, 4);
v___x_4667_ = lean_unsigned_to_nat(0u);
v___x_4668_ = lean_array_fget_borrowed(v_packages_4666_, v___x_4667_);
v_wsIdx_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_wsIdx_4669_);
v___x_4670_ = lean_array_get_size(v_packages_4666_);
v___x_4671_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4658_, v___x_4665_, v_ws_4656_, v_wsIdx_4669_, v___x_4670_, v_snd_4664_, v_a_4655_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4689_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4674_ = v___x_4671_;
v_isShared_4675_ = v_isSharedCheck_4689_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4671_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4689_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v_fst_4676_; lean_object* v_snd_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4688_; 
v_fst_4676_ = lean_ctor_get(v_a_4672_, 0);
v_snd_4677_ = lean_ctor_get(v_a_4672_, 1);
v_isSharedCheck_4688_ = !lean_is_exclusive(v_a_4672_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4679_ = v_a_4672_;
v_isShared_4680_ = v_isSharedCheck_4688_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_snd_4677_);
lean_inc(v_fst_4676_);
lean_dec(v_a_4672_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4688_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4681_; lean_object* v___x_4683_; 
v___x_4681_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4676_);
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 0, v___x_4681_);
v___x_4683_ = v___x_4679_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4681_);
lean_ctor_set(v_reuseFailAlloc_4687_, 1, v_snd_4677_);
v___x_4683_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
lean_object* v___x_4685_; 
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v___x_4683_);
v___x_4685_ = v___x_4674_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4683_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
}
}
else
{
return v___x_4671_;
}
}
else
{
lean_object* v_packages_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v_depConfigs_4693_; lean_object* v___x_4694_; lean_object* v___f_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v_packages_4690_ = lean_ctor_get(v_ws_4656_, 4);
v___x_4691_ = lean_unsigned_to_nat(0u);
v___x_4692_ = lean_array_fget_borrowed(v_packages_4690_, v___x_4691_);
v_depConfigs_4693_ = lean_ctor_get(v___x_4692_, 12);
v___x_4694_ = lean_box(v_updateToolchain_4659_);
lean_inc_ref(v_ws_4656_);
lean_inc(v___x_4692_);
v___f_4695_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4695_, 0, v___x_4692_);
lean_closure_set(v___f_4695_, 1, v___x_4694_);
lean_closure_set(v___f_4695_, 2, v_ws_4656_);
v___x_4696_ = lean_array_get_size(v_depConfigs_4693_);
lean_inc_ref(v_depConfigs_4693_);
v___x_4697_ = l_Array_reverse___redArg(v_depConfigs_4693_);
v___x_4698_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4699_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4696_, v___f_4695_, v___x_4697_, v___x_4691_, v___x_4698_, v_snd_4664_, v_a_4655_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v_a_4700_; lean_object* v_fst_4701_; lean_object* v_snd_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4774_; 
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
lean_inc(v_a_4700_);
lean_dec_ref_known(v___x_4699_, 1);
v_fst_4701_ = lean_ctor_get(v_a_4700_, 0);
v_snd_4702_ = lean_ctor_get(v_a_4700_, 1);
v_isSharedCheck_4774_ = !lean_is_exclusive(v_a_4700_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4704_ = v_a_4700_;
v_isShared_4705_ = v_isSharedCheck_4774_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_snd_4702_);
lean_inc(v_fst_4701_);
lean_dec(v_a_4700_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4774_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; 
lean_inc_ref(v_ws_4656_);
v___x_4706_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4655_, v_ws_4656_, v_fst_4701_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
lean_dec_ref_known(v___x_4706_, 1);
v___x_4707_ = lean_array_get_size(v_packages_4690_);
lean_inc_ref(v_leanOpts_4658_);
v___x_4708_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4696_, v_fst_4701_, v___x_4697_, v_leanOpts_4658_, v___x_4691_, v_ws_4656_, v_snd_4702_, v_a_4655_);
lean_dec_ref(v___x_4697_);
lean_dec(v_fst_4701_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4757_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4711_ = v___x_4708_;
v_isShared_4712_ = v_isSharedCheck_4757_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4708_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4757_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v_fst_4713_; lean_object* v_snd_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4756_; 
v_fst_4713_ = lean_ctor_get(v_a_4709_, 0);
v_snd_4714_ = lean_ctor_get(v_a_4709_, 1);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_a_4709_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4716_ = v_a_4709_;
v_isShared_4717_ = v_isSharedCheck_4756_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_snd_4714_);
lean_inc(v_fst_4713_);
lean_dec(v_a_4709_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4756_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v_packages_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4723_; 
v_packages_4718_ = lean_ctor_get(v_fst_4713_, 4);
v___x_4719_ = lean_array_get_size(v_packages_4718_);
v___x_4720_ = lean_array_fget(v_packages_4718_, v___x_4691_);
v___x_4721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4707_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 1, v___x_4719_);
lean_ctor_set(v___x_4704_, 0, v___x_4721_);
v___x_4723_ = v___x_4704_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4721_);
lean_ctor_set(v_reuseFailAlloc_4755_, 1, v___x_4719_);
v___x_4723_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; uint8_t v___x_4726_; 
v___x_4724_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4723_, v___x_4698_);
v___x_4725_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4713_, v___x_4720_, v___x_4724_);
v___x_4726_ = lean_nat_dec_eq(v___x_4707_, v___x_4719_);
if (v___x_4726_ == 0)
{
lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
lean_del_object(v___x_4716_);
lean_del_object(v___x_4711_);
v___x_4727_ = lean_unsigned_to_nat(1u);
v___x_4728_ = lean_nat_add(v___x_4707_, v___x_4727_);
v___x_4729_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4658_, v___x_4665_, v___x_4725_, v___x_4707_, v___x_4728_, v_snd_4714_, v_a_4655_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4747_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4732_ = v___x_4729_;
v_isShared_4733_ = v_isSharedCheck_4747_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4729_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4747_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v_fst_4734_; lean_object* v_snd_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4746_; 
v_fst_4734_ = lean_ctor_get(v_a_4730_, 0);
v_snd_4735_ = lean_ctor_get(v_a_4730_, 1);
v_isSharedCheck_4746_ = !lean_is_exclusive(v_a_4730_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4737_ = v_a_4730_;
v_isShared_4738_ = v_isSharedCheck_4746_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_snd_4735_);
lean_inc(v_fst_4734_);
lean_dec(v_a_4730_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4746_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4739_; lean_object* v___x_4741_; 
v___x_4739_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4734_);
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 0, v___x_4739_);
v___x_4741_ = v___x_4737_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4739_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v_snd_4735_);
v___x_4741_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
lean_object* v___x_4743_; 
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 0, v___x_4741_);
v___x_4743_ = v___x_4732_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4741_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
else
{
return v___x_4729_;
}
}
else
{
lean_object* v___x_4748_; lean_object* v___x_4750_; 
lean_dec_ref(v_leanOpts_4658_);
v___x_4748_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4725_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4748_);
v___x_4750_ = v___x_4716_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4748_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_snd_4714_);
v___x_4750_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
lean_object* v___x_4752_; 
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 0, v___x_4750_);
v___x_4752_ = v___x_4711_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4750_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
lean_del_object(v___x_4704_);
lean_dec_ref(v_leanOpts_4658_);
v_a_4758_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4708_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4708_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
lean_del_object(v___x_4704_);
lean_dec(v_snd_4702_);
lean_dec(v_fst_4701_);
lean_dec_ref(v___x_4697_);
lean_dec_ref(v_leanOpts_4658_);
lean_dec_ref(v_ws_4656_);
v_a_4766_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4706_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4706_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
}
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4782_; 
lean_dec_ref(v___x_4697_);
lean_dec_ref(v_leanOpts_4658_);
lean_dec_ref(v_ws_4656_);
v_a_4775_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4777_ = v___x_4699_;
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v___x_4699_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4780_; 
if (v_isShared_4778_ == 0)
{
v___x_4780_ = v___x_4777_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4775_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
lean_dec_ref(v_leanOpts_4658_);
lean_dec_ref(v_ws_4656_);
v_a_4783_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4662_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4662_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4791_, lean_object* v_ws_4792_, lean_object* v_toUpdate_4793_, lean_object* v_leanOpts_4794_, lean_object* v_updateToolchain_4795_, lean_object* v_a_4796_){
_start:
{
uint8_t v_updateToolchain_boxed_4797_; lean_object* v_res_4798_; 
v_updateToolchain_boxed_4797_ = lean_unbox(v_updateToolchain_4795_);
v_res_4798_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4791_, v_ws_4792_, v_toUpdate_4793_, v_leanOpts_4794_, v_updateToolchain_boxed_4797_);
lean_dec_ref(v_a_4791_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4799_, size_t v_i_4800_, size_t v_stop_4801_, lean_object* v_b_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
uint8_t v___x_4806_; 
v___x_4806_ = lean_usize_dec_eq(v_i_4800_, v_stop_4801_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4807_ = lean_array_uget_borrowed(v_as_4799_, v_i_4800_);
lean_inc(v___x_4807_);
v___x_4808_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4807_, v___y_4803_, v___y_4804_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v_a_4809_; size_t v___x_4810_; size_t v___x_4811_; 
v_a_4809_ = lean_ctor_get(v___x_4808_, 0);
lean_inc(v_a_4809_);
lean_dec_ref_known(v___x_4808_, 1);
v___x_4810_ = ((size_t)1ULL);
v___x_4811_ = lean_usize_add(v_i_4800_, v___x_4810_);
v_i_4800_ = v___x_4811_;
v_b_4802_ = v_a_4809_;
goto _start;
}
else
{
return v___x_4808_;
}
}
else
{
lean_object* v___x_4813_; 
v___x_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4813_, 0, v_b_4802_);
return v___x_4813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4814_, lean_object* v_i_4815_, lean_object* v_stop_4816_, lean_object* v_b_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_){
_start:
{
size_t v_i_boxed_4821_; size_t v_stop_boxed_4822_; lean_object* v_res_4823_; 
v_i_boxed_4821_ = lean_unbox_usize(v_i_4815_);
lean_dec(v_i_4815_);
v_stop_boxed_4822_ = lean_unbox_usize(v_stop_4816_);
lean_dec(v_stop_4816_);
v_res_4823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4814_, v_i_boxed_4821_, v_stop_boxed_4822_, v_b_4817_, v___y_4818_, v___y_4819_);
lean_dec_ref(v___y_4819_);
lean_dec(v___y_4818_);
lean_dec_ref(v_as_4814_);
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4824_, lean_object* v_toUpdate_4825_, lean_object* v_leanOpts_4826_, uint8_t v_updateToolchain_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v___x_4830_; 
v___x_4830_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4828_, v_ws_4824_, v_toUpdate_4825_, v_leanOpts_4826_, v_updateToolchain_4827_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v_fst_4832_; lean_object* v_snd_4833_; lean_object* v___y_4835_; lean_object* v___x_4852_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4831_);
lean_dec_ref_known(v___x_4830_, 1);
v_fst_4832_ = lean_ctor_get(v_a_4831_, 0);
lean_inc(v_fst_4832_);
v_snd_4833_ = lean_ctor_get(v_a_4831_, 1);
lean_inc(v_snd_4833_);
lean_dec(v_a_4831_);
v___x_4852_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4832_, v_snd_4833_);
lean_dec(v_snd_4833_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4874_; 
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4874_ == 0)
{
lean_object* v_unused_4875_; 
v_unused_4875_ = lean_ctor_get(v___x_4852_, 0);
lean_dec(v_unused_4875_);
v___x_4854_ = v___x_4852_;
v_isShared_4855_ = v_isSharedCheck_4874_;
goto v_resetjp_4853_;
}
else
{
lean_dec(v___x_4852_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4874_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v_packages_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; uint8_t v___x_4859_; 
v_packages_4856_ = lean_ctor_get(v_fst_4832_, 4);
v___x_4857_ = lean_unsigned_to_nat(0u);
v___x_4858_ = lean_array_get_size(v_packages_4856_);
v___x_4859_ = lean_nat_dec_lt(v___x_4857_, v___x_4858_);
if (v___x_4859_ == 0)
{
lean_object* v___x_4861_; 
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v_fst_4832_);
v___x_4861_ = v___x_4854_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_fst_4832_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
else
{
lean_object* v___x_4863_; uint8_t v___x_4864_; 
v___x_4863_ = lean_box(0);
v___x_4864_ = lean_nat_dec_le(v___x_4858_, v___x_4858_);
if (v___x_4864_ == 0)
{
if (v___x_4859_ == 0)
{
lean_object* v___x_4866_; 
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v_fst_4832_);
v___x_4866_ = v___x_4854_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_fst_4832_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
else
{
size_t v___x_4868_; size_t v___x_4869_; lean_object* v___x_4870_; 
lean_del_object(v___x_4854_);
v___x_4868_ = ((size_t)0ULL);
v___x_4869_ = lean_usize_of_nat(v___x_4858_);
v___x_4870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4856_, v___x_4868_, v___x_4869_, v___x_4863_, v_fst_4832_, v_a_4828_);
v___y_4835_ = v___x_4870_;
goto v___jp_4834_;
}
}
else
{
size_t v___x_4871_; size_t v___x_4872_; lean_object* v___x_4873_; 
lean_del_object(v___x_4854_);
v___x_4871_ = ((size_t)0ULL);
v___x_4872_ = lean_usize_of_nat(v___x_4858_);
v___x_4873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4856_, v___x_4871_, v___x_4872_, v___x_4863_, v_fst_4832_, v_a_4828_);
v___y_4835_ = v___x_4873_;
goto v___jp_4834_;
}
}
}
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4888_; 
lean_dec(v_fst_4832_);
v_a_4876_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4878_ = v___x_4852_;
v_isShared_4879_ = v_isSharedCheck_4888_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4852_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4888_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4880_; uint8_t v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4886_; 
v___x_4880_ = lean_io_error_to_string(v_a_4876_);
v___x_4881_ = 3;
v___x_4882_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4882_, 0, v___x_4880_);
lean_ctor_set_uint8(v___x_4882_, sizeof(void*)*1, v___x_4881_);
lean_inc_ref(v_a_4828_);
v___x_4883_ = lean_apply_2(v_a_4828_, v___x_4882_, lean_box(0));
v___x_4884_ = lean_box(0);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v___x_4884_);
v___x_4886_ = v___x_4878_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
v___jp_4834_:
{
if (lean_obj_tag(v___y_4835_) == 0)
{
lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
v_isSharedCheck_4842_ = !lean_is_exclusive(v___y_4835_);
if (v_isSharedCheck_4842_ == 0)
{
lean_object* v_unused_4843_; 
v_unused_4843_ = lean_ctor_get(v___y_4835_, 0);
lean_dec(v_unused_4843_);
v___x_4837_ = v___y_4835_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_dec(v___y_4835_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
lean_ctor_set(v___x_4837_, 0, v_fst_4832_);
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_fst_4832_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
else
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4851_; 
lean_dec(v_fst_4832_);
v_a_4844_ = lean_ctor_get(v___y_4835_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___y_4835_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4846_ = v___y_4835_;
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___y_4835_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4849_; 
if (v_isShared_4847_ == 0)
{
v___x_4849_ = v___x_4846_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4844_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
v_a_4889_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4830_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4830_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4897_, lean_object* v_toUpdate_4898_, lean_object* v_leanOpts_4899_, lean_object* v_updateToolchain_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_){
_start:
{
uint8_t v_updateToolchain_boxed_4903_; lean_object* v_res_4904_; 
v_updateToolchain_boxed_4903_ = lean_unbox(v_updateToolchain_4900_);
v_res_4904_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4897_, v_toUpdate_4898_, v_leanOpts_4899_, v_updateToolchain_boxed_4903_, v_a_4901_);
lean_dec_ref(v_a_4901_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_4909_, lean_object* v_what_4910_, lean_object* v___y_4911_){
_start:
{
lean_object* v_name_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; uint8_t v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; uint8_t v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v_name_4913_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_name_4913_);
lean_dec_ref(v___x_4909_);
v___x_4914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_4915_ = lean_string_append(v___x_4914_, v_what_4910_);
v___x_4916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_4917_ = lean_string_append(v___x_4915_, v___x_4916_);
v___x_4918_ = 1;
v___x_4919_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4913_, v___x_4918_);
v___x_4920_ = lean_string_append(v___x_4917_, v___x_4919_);
v___x_4921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_4922_ = lean_string_append(v___x_4920_, v___x_4921_);
v___x_4923_ = lean_string_append(v___x_4922_, v___x_4919_);
lean_dec_ref(v___x_4919_);
v___x_4924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_4925_ = lean_string_append(v___x_4923_, v___x_4924_);
v___x_4926_ = 2;
v___x_4927_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4927_, 0, v___x_4925_);
lean_ctor_set_uint8(v___x_4927_, sizeof(void*)*1, v___x_4926_);
lean_inc_ref(v___y_4911_);
v___x_4928_ = lean_apply_2(v___y_4911_, v___x_4927_, lean_box(0));
v___x_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_4930_, lean_object* v_what_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4930_, v_what_4931_, v___y_4932_);
lean_dec_ref(v___y_4932_);
lean_dec_ref(v_what_4931_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_4938_, lean_object* v_as_4939_, size_t v_i_4940_, size_t v_stop_4941_, lean_object* v_b_4942_, lean_object* v___y_4943_){
_start:
{
lean_object* v_a_4946_; lean_object* v___y_4951_; uint8_t v___x_4953_; 
v___x_4953_ = lean_usize_dec_eq(v_i_4940_, v_stop_4941_);
if (v___x_4953_ == 0)
{
lean_object* v___x_4954_; lean_object* v_src_x3f_4955_; 
v___x_4954_ = lean_array_uget_borrowed(v_as_4939_, v_i_4940_);
v_src_x3f_4955_ = lean_ctor_get(v___x_4954_, 3);
if (lean_obj_tag(v_src_x3f_4955_) == 1)
{
lean_object* v_name_4956_; lean_object* v_val_4957_; lean_object* v___x_4958_; 
v_name_4956_ = lean_ctor_get(v___x_4954_, 0);
v_val_4957_ = lean_ctor_get(v_src_x3f_4955_, 0);
v___x_4958_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_4938_, v_name_4956_);
if (lean_obj_tag(v___x_4958_) == 1)
{
lean_object* v_val_4959_; lean_object* v___y_4961_; lean_object* v___y_4965_; 
v_val_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_val_4959_);
lean_dec_ref_known(v___x_4958_, 1);
if (lean_obj_tag(v_val_4957_) == 0)
{
lean_object* v_src_4968_; 
v_src_4968_ = lean_ctor_get(v_val_4959_, 4);
lean_inc_ref(v_src_4968_);
lean_dec(v_val_4959_);
if (lean_obj_tag(v_src_4968_) == 0)
{
lean_object* v___x_4969_; 
lean_dec_ref_known(v_src_4968_, 1);
v___x_4969_ = lean_box(0);
v_a_4946_ = v___x_4969_;
goto v___jp_4945_;
}
else
{
lean_dec_ref(v_src_4968_);
v___y_4965_ = v___y_4943_;
goto v___jp_4964_;
}
}
else
{
lean_object* v_src_4970_; 
v_src_4970_ = lean_ctor_get(v_val_4959_, 4);
lean_inc_ref(v_src_4970_);
lean_dec(v_val_4959_);
if (lean_obj_tag(v_src_4970_) == 1)
{
lean_object* v_url_4971_; lean_object* v_rev_4972_; lean_object* v_url_4973_; lean_object* v_inputRev_x3f_4974_; lean_object* v___y_4976_; uint8_t v___x_4983_; 
v_url_4971_ = lean_ctor_get(v_val_4957_, 0);
v_rev_4972_ = lean_ctor_get(v_val_4957_, 1);
v_url_4973_ = lean_ctor_get(v_src_4970_, 0);
lean_inc_ref(v_url_4973_);
v_inputRev_x3f_4974_ = lean_ctor_get(v_src_4970_, 2);
lean_inc(v_inputRev_x3f_4974_);
lean_dec_ref_known(v_src_4970_, 4);
v___x_4983_ = lean_string_dec_eq(v_url_4971_, v_url_4973_);
lean_dec_ref(v_url_4973_);
if (v___x_4983_ == 0)
{
goto v___jp_4980_;
}
else
{
if (v___x_4953_ == 0)
{
v___y_4976_ = v___y_4943_;
goto v___jp_4975_;
}
else
{
goto v___jp_4980_;
}
}
v___jp_4975_:
{
lean_object* v___x_4977_; uint8_t v___x_4978_; 
v___x_4977_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_4972_);
v___x_4978_ = l_Option_instDecidableEq___redArg(v___x_4977_, v_rev_4972_, v_inputRev_x3f_4974_);
if (v___x_4978_ == 0)
{
v___y_4961_ = v___y_4976_;
goto v___jp_4960_;
}
else
{
if (v___x_4953_ == 0)
{
lean_object* v___x_4979_; 
v___x_4979_ = lean_box(0);
v_a_4946_ = v___x_4979_;
goto v___jp_4945_;
}
else
{
v___y_4961_ = v___y_4976_;
goto v___jp_4960_;
}
}
}
v___jp_4980_:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_4954_);
v___x_4982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4954_, v___x_4981_, v___y_4943_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_dec_ref_known(v___x_4982_, 1);
v___y_4976_ = v___y_4943_;
goto v___jp_4975_;
}
else
{
lean_dec(v_inputRev_x3f_4974_);
return v___x_4982_;
}
}
}
else
{
lean_dec_ref(v_src_4970_);
v___y_4965_ = v___y_4943_;
goto v___jp_4964_;
}
}
v___jp_4960_:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_4954_);
v___x_4963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4954_, v___x_4962_, v___y_4961_);
v___y_4951_ = v___x_4963_;
goto v___jp_4950_;
}
v___jp_4964_:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_4954_);
v___x_4967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4954_, v___x_4966_, v___y_4965_);
v___y_4951_ = v___x_4967_;
goto v___jp_4950_;
}
}
else
{
lean_object* v___x_4984_; 
lean_dec(v___x_4958_);
v___x_4984_ = lean_box(0);
v_a_4946_ = v___x_4984_;
goto v___jp_4945_;
}
}
else
{
lean_object* v___x_4985_; 
v___x_4985_ = lean_box(0);
v_a_4946_ = v___x_4985_;
goto v___jp_4945_;
}
}
else
{
lean_object* v___x_4986_; 
v___x_4986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4986_, 0, v_b_4942_);
return v___x_4986_;
}
v___jp_4945_:
{
size_t v___x_4947_; size_t v___x_4948_; 
v___x_4947_ = ((size_t)1ULL);
v___x_4948_ = lean_usize_add(v_i_4940_, v___x_4947_);
v_i_4940_ = v___x_4948_;
v_b_4942_ = v_a_4946_;
goto _start;
}
v___jp_4950_:
{
if (lean_obj_tag(v___y_4951_) == 0)
{
lean_object* v_a_4952_; 
v_a_4952_ = lean_ctor_get(v___y_4951_, 0);
lean_inc(v_a_4952_);
lean_dec_ref_known(v___y_4951_, 1);
v_a_4946_ = v_a_4952_;
goto v___jp_4945_;
}
else
{
return v___y_4951_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_4987_, lean_object* v_as_4988_, lean_object* v_i_4989_, lean_object* v_stop_4990_, lean_object* v_b_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_){
_start:
{
size_t v_i_boxed_4994_; size_t v_stop_boxed_4995_; lean_object* v_res_4996_; 
v_i_boxed_4994_ = lean_unbox_usize(v_i_4989_);
lean_dec(v_i_4989_);
v_stop_boxed_4995_ = lean_unbox_usize(v_stop_4990_);
lean_dec(v_stop_4990_);
v_res_4996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4987_, v_as_4988_, v_i_boxed_4994_, v_stop_boxed_4995_, v_b_4991_, v___y_4992_);
lean_dec_ref(v___y_4992_);
lean_dec_ref(v_as_4988_);
lean_dec(v_pkgEntries_4987_);
return v_res_4996_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_4997_, lean_object* v_deps_4998_, lean_object* v_a_4999_){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; uint8_t v___x_5004_; 
v___x_5001_ = lean_unsigned_to_nat(0u);
v___x_5002_ = lean_array_get_size(v_deps_4998_);
v___x_5003_ = lean_box(0);
v___x_5004_ = lean_nat_dec_lt(v___x_5001_, v___x_5002_);
if (v___x_5004_ == 0)
{
lean_object* v___x_5005_; 
v___x_5005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5003_);
return v___x_5005_;
}
else
{
uint8_t v___x_5006_; 
v___x_5006_ = lean_nat_dec_le(v___x_5002_, v___x_5002_);
if (v___x_5006_ == 0)
{
if (v___x_5004_ == 0)
{
lean_object* v___x_5007_; 
v___x_5007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5007_, 0, v___x_5003_);
return v___x_5007_;
}
else
{
size_t v___x_5008_; size_t v___x_5009_; lean_object* v___x_5010_; 
v___x_5008_ = ((size_t)0ULL);
v___x_5009_ = lean_usize_of_nat(v___x_5002_);
v___x_5010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4997_, v_deps_4998_, v___x_5008_, v___x_5009_, v___x_5003_, v_a_4999_);
return v___x_5010_;
}
}
else
{
size_t v___x_5011_; size_t v___x_5012_; lean_object* v___x_5013_; 
v___x_5011_ = ((size_t)0ULL);
v___x_5012_ = lean_usize_of_nat(v___x_5002_);
v___x_5013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4997_, v_deps_4998_, v___x_5011_, v___x_5012_, v___x_5003_, v_a_4999_);
return v___x_5013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_5014_, lean_object* v_deps_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_5014_, v_deps_5015_, v_a_5016_);
lean_dec_ref(v_a_5016_);
lean_dec_ref(v_deps_5015_);
lean_dec(v_pkgEntries_5014_);
return v_res_5018_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_5019_, lean_object* v_x_5020_){
_start:
{
if (lean_obj_tag(v_x_5019_) == 0)
{
if (lean_obj_tag(v_x_5020_) == 0)
{
uint8_t v___x_5021_; 
v___x_5021_ = 1;
return v___x_5021_;
}
else
{
uint8_t v___x_5022_; 
v___x_5022_ = 0;
return v___x_5022_;
}
}
else
{
if (lean_obj_tag(v_x_5020_) == 0)
{
uint8_t v___x_5023_; 
v___x_5023_ = 0;
return v___x_5023_;
}
else
{
lean_object* v_val_5024_; lean_object* v_val_5025_; uint8_t v___x_5026_; 
v_val_5024_ = lean_ctor_get(v_x_5019_, 0);
v_val_5025_ = lean_ctor_get(v_x_5020_, 0);
v___x_5026_ = lean_string_dec_eq(v_val_5024_, v_val_5025_);
return v___x_5026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_5027_, lean_object* v_x_5028_){
_start:
{
uint8_t v_res_5029_; lean_object* v_r_5030_; 
v_res_5029_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_5027_, v_x_5028_);
lean_dec(v_x_5028_);
lean_dec(v_x_5027_);
v_r_5030_ = lean_box(v_res_5029_);
return v_r_5030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_pkg_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v_leanOpts_5039_, uint8_t v_reconfigure_5040_, lean_object* v_as_5041_, size_t v_i_5042_, size_t v_stop_5043_, lean_object* v_b_5044_, lean_object* v___y_5045_){
_start:
{
uint8_t v___x_5047_; 
v___x_5047_ = lean_usize_dec_eq(v_i_5042_, v_stop_5043_);
if (v___x_5047_ == 0)
{
lean_object* v_ws_5048_; lean_object* v_depIdxs_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5179_; 
v_ws_5048_ = lean_ctor_get(v_b_5044_, 0);
v_depIdxs_5049_ = lean_ctor_get(v_b_5044_, 1);
v_isSharedCheck_5179_ = !lean_is_exclusive(v_b_5044_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5051_ = v_b_5044_;
v_isShared_5052_ = v_isSharedCheck_5179_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_depIdxs_5049_);
lean_inc(v_ws_5048_);
lean_dec(v_b_5044_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5179_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v_lakeEnv_5053_; lean_object* v_packages_5054_; size_t v___x_5055_; size_t v___x_5056_; lean_object* v___x_5057_; lean_object* v___f_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v_lakeEnv_5053_ = lean_ctor_get(v_ws_5048_, 0);
v_packages_5054_ = lean_ctor_get(v_ws_5048_, 4);
v___x_5055_ = ((size_t)1ULL);
v___x_5056_ = lean_usize_sub(v_i_5042_, v___x_5055_);
v___x_5057_ = lean_array_uget_borrowed(v_as_5041_, v___x_5056_);
lean_inc(v___x_5057_);
v___f_5058_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5058_, 0, v___x_5057_);
v___x_5059_ = lean_unsigned_to_nat(0u);
v___x_5060_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5058_, v_packages_5054_, v___x_5059_);
if (lean_obj_tag(v___x_5060_) == 1)
{
lean_object* v_val_5061_; lean_object* v___x_5062_; lean_object* v___x_5064_; 
v_val_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_val_5061_);
lean_dec_ref_known(v___x_5060_, 1);
v___x_5062_ = lean_array_push(v_depIdxs_5049_, v_val_5061_);
if (v_isShared_5052_ == 0)
{
lean_ctor_set(v___x_5051_, 1, v___x_5062_);
v___x_5064_ = v___x_5051_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_ws_5048_);
lean_ctor_set(v_reuseFailAlloc_5066_, 1, v___x_5062_);
v___x_5064_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
v_i_5042_ = v___x_5056_;
v_b_5044_ = v___x_5064_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_5067_; lean_object* v_baseName_5068_; lean_object* v_name_5069_; lean_object* v_opts_5070_; uint8_t v___x_5071_; 
lean_dec(v___x_5060_);
v_wsIdx_5067_ = lean_ctor_get(v_pkg_5036_, 0);
v_baseName_5068_ = lean_ctor_get(v_pkg_5036_, 1);
v_name_5069_ = lean_ctor_get(v___x_5057_, 0);
v_opts_5070_ = lean_ctor_get(v___x_5057_, 4);
v___x_5071_ = lean_name_eq(v_baseName_5068_, v_name_5069_);
if (v___x_5071_ == 0)
{
lean_object* v___x_5072_; 
v___x_5072_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5037_, v_name_5069_);
if (lean_obj_tag(v___x_5072_) == 1)
{
lean_object* v_val_5073_; lean_object* v___x_5074_; lean_object* v_dir_5075_; lean_object* v___x_5076_; 
v_val_5073_ = lean_ctor_get(v___x_5072_, 0);
lean_inc(v_val_5073_);
lean_dec_ref_known(v___x_5072_, 1);
v___x_5074_ = lean_array_fget_borrowed(v_packages_5054_, v___x_5059_);
v_dir_5075_ = lean_ctor_get(v___x_5074_, 4);
lean_inc_ref(v___y_5038_);
lean_inc_ref(v_dir_5075_);
v___x_5076_ = l_Lake_PackageEntry_materialize(v_val_5073_, v_lakeEnv_5053_, v_dir_5075_, v___y_5038_, v___y_5045_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5133_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5079_ = v___x_5076_;
v_isShared_5080_ = v_isSharedCheck_5133_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5076_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5133_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5081_; lean_object* v_wsIdx_5082_; lean_object* v___x_5083_; 
v___x_5081_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_5082_ = lean_array_get_size(v_packages_5054_);
lean_inc_ref(v_leanOpts_5039_);
lean_inc(v_opts_5070_);
v___x_5083_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5048_, v_a_5077_, v_opts_5070_, v_leanOpts_5039_, v_reconfigure_5040_, v___x_5081_);
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_object* v_a_5084_; lean_object* v_a_5085_; lean_object* v___x_5086_; lean_object* v___x_5088_; 
lean_del_object(v___x_5079_);
v_a_5084_ = lean_ctor_get(v___x_5083_, 0);
lean_inc(v_a_5084_);
v_a_5085_ = lean_ctor_get(v___x_5083_, 1);
lean_inc(v_a_5085_);
lean_dec_ref_known(v___x_5083_, 2);
v___x_5086_ = lean_array_push(v_depIdxs_5049_, v_wsIdx_5082_);
if (v_isShared_5052_ == 0)
{
lean_ctor_set(v___x_5051_, 1, v___x_5086_);
lean_ctor_set(v___x_5051_, 0, v_a_5084_);
v___x_5088_ = v___x_5051_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5084_);
lean_ctor_set(v_reuseFailAlloc_5105_, 1, v___x_5086_);
v___x_5088_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
lean_object* v___x_5089_; uint8_t v___x_5090_; 
v___x_5089_ = lean_array_get_size(v_a_5085_);
v___x_5090_ = lean_nat_dec_lt(v___x_5059_, v___x_5089_);
if (v___x_5090_ == 0)
{
lean_dec(v_a_5085_);
v_i_5042_ = v___x_5056_;
v_b_5044_ = v___x_5088_;
goto _start;
}
else
{
lean_object* v___x_5092_; size_t v___x_5093_; size_t v___x_5094_; lean_object* v___x_5095_; 
v___x_5092_ = lean_box(0);
v___x_5093_ = ((size_t)0ULL);
v___x_5094_ = lean_usize_of_nat(v___x_5089_);
v___x_5095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5085_, v___x_5093_, v___x_5094_, v___x_5092_, v___y_5045_);
lean_dec(v_a_5085_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_dec_ref_known(v___x_5095_, 1);
v_i_5042_ = v___x_5056_;
v_b_5044_ = v___x_5088_;
goto _start;
}
else
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5104_; 
lean_dec_ref(v___x_5088_);
lean_dec_ref(v_leanOpts_5039_);
lean_dec_ref(v___y_5038_);
lean_dec_ref(v_pkg_5036_);
v_a_5097_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5099_ = v___x_5095_;
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5095_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5100_ == 0)
{
v___x_5102_ = v___x_5099_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5097_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
}
}
}
else
{
lean_object* v_a_5106_; lean_object* v___x_5107_; uint8_t v___x_5108_; 
lean_del_object(v___x_5051_);
lean_dec_ref(v_depIdxs_5049_);
lean_dec_ref(v_leanOpts_5039_);
lean_dec_ref(v___y_5038_);
lean_dec_ref(v_pkg_5036_);
v_a_5106_ = lean_ctor_get(v___x_5083_, 1);
lean_inc(v_a_5106_);
lean_dec_ref_known(v___x_5083_, 2);
v___x_5107_ = lean_array_get_size(v_a_5106_);
v___x_5108_ = lean_nat_dec_lt(v___x_5059_, v___x_5107_);
if (v___x_5108_ == 0)
{
lean_object* v___x_5109_; lean_object* v___x_5111_; 
lean_dec(v_a_5106_);
v___x_5109_ = lean_box(0);
if (v_isShared_5080_ == 0)
{
lean_ctor_set_tag(v___x_5079_, 1);
lean_ctor_set(v___x_5079_, 0, v___x_5109_);
v___x_5111_ = v___x_5079_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5109_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
return v___x_5111_;
}
}
else
{
lean_object* v___x_5113_; size_t v___x_5114_; size_t v___x_5115_; lean_object* v___x_5116_; 
lean_del_object(v___x_5079_);
v___x_5113_ = lean_box(0);
v___x_5114_ = ((size_t)0ULL);
v___x_5115_ = lean_usize_of_nat(v___x_5107_);
v___x_5116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5106_, v___x_5114_, v___x_5115_, v___x_5113_, v___y_5045_);
lean_dec(v_a_5106_);
if (lean_obj_tag(v___x_5116_) == 0)
{
lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5123_ == 0)
{
lean_object* v_unused_5124_; 
v_unused_5124_ = lean_ctor_get(v___x_5116_, 0);
lean_dec(v_unused_5124_);
v___x_5118_ = v___x_5116_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_dec(v___x_5116_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
lean_ctor_set_tag(v___x_5118_, 1);
lean_ctor_set(v___x_5118_, 0, v___x_5113_);
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5113_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
v_a_5125_ = lean_ctor_get(v___x_5116_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5116_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5116_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5141_; 
lean_del_object(v___x_5051_);
lean_dec_ref(v_depIdxs_5049_);
lean_dec_ref(v_ws_5048_);
lean_dec_ref(v_leanOpts_5039_);
lean_dec_ref(v___y_5038_);
lean_dec_ref(v_pkg_5036_);
v_a_5134_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5141_ == 0)
{
v___x_5136_ = v___x_5076_;
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_a_5134_);
lean_dec(v___x_5076_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5139_; 
if (v_isShared_5137_ == 0)
{
v___x_5139_ = v___x_5136_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v_a_5134_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
}
else
{
uint8_t v___x_5142_; 
lean_inc(v_baseName_5068_);
lean_inc(v_wsIdx_5067_);
lean_dec(v___x_5072_);
lean_del_object(v___x_5051_);
lean_dec_ref(v_depIdxs_5049_);
lean_dec_ref(v_ws_5048_);
lean_dec_ref(v_leanOpts_5039_);
lean_dec_ref(v___y_5038_);
lean_dec_ref(v_pkg_5036_);
v___x_5142_ = lean_nat_dec_eq(v_wsIdx_5067_, v___x_5059_);
lean_dec(v_wsIdx_5067_);
if (v___x_5142_ == 0)
{
lean_object* v___x_5143_; uint8_t v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; uint8_t v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; 
v___x_5143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5144_ = 1;
lean_inc(v_name_5069_);
v___x_5145_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5069_, v___x_5144_);
v___x_5146_ = lean_string_append(v___x_5143_, v___x_5145_);
lean_dec_ref(v___x_5145_);
v___x_5147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5148_ = lean_string_append(v___x_5146_, v___x_5147_);
v___x_5149_ = l_Lean_Name_toString(v_baseName_5068_, v___x_5142_);
v___x_5150_ = lean_string_append(v___x_5148_, v___x_5149_);
lean_dec_ref(v___x_5149_);
v___x_5151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5152_ = lean_string_append(v___x_5150_, v___x_5151_);
v___x_5153_ = 3;
v___x_5154_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5154_, 0, v___x_5152_);
lean_ctor_set_uint8(v___x_5154_, sizeof(void*)*1, v___x_5153_);
lean_inc_ref(v___y_5045_);
v___x_5155_ = lean_apply_2(v___y_5045_, v___x_5154_, lean_box(0));
v___x_5156_ = lean_box(0);
v___x_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5157_, 0, v___x_5156_);
return v___x_5157_;
}
else
{
lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; uint8_t v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
lean_dec(v_baseName_5068_);
v___x_5158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5069_);
v___x_5159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5069_, v___x_5142_);
v___x_5160_ = lean_string_append(v___x_5158_, v___x_5159_);
v___x_5161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5162_ = lean_string_append(v___x_5160_, v___x_5161_);
v___x_5163_ = lean_string_append(v___x_5162_, v___x_5159_);
lean_dec_ref(v___x_5159_);
v___x_5164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5165_ = lean_string_append(v___x_5163_, v___x_5164_);
v___x_5166_ = 3;
v___x_5167_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5167_, 0, v___x_5165_);
lean_ctor_set_uint8(v___x_5167_, sizeof(void*)*1, v___x_5166_);
lean_inc_ref(v___y_5045_);
v___x_5168_ = lean_apply_2(v___y_5045_, v___x_5167_, lean_box(0));
v___x_5169_ = lean_box(0);
v___x_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5170_, 0, v___x_5169_);
return v___x_5170_;
}
}
}
else
{
lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; uint8_t v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; 
lean_inc(v_baseName_5068_);
lean_del_object(v___x_5051_);
lean_dec_ref(v_depIdxs_5049_);
lean_dec_ref(v_ws_5048_);
lean_dec_ref(v_leanOpts_5039_);
lean_dec_ref(v___y_5038_);
lean_dec_ref(v_pkg_5036_);
v___x_5171_ = l_Lean_Name_toString(v_baseName_5068_, v___x_5047_);
v___x_5172_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5173_ = lean_string_append(v___x_5171_, v___x_5172_);
v___x_5174_ = 3;
v___x_5175_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5175_, 0, v___x_5173_);
lean_ctor_set_uint8(v___x_5175_, sizeof(void*)*1, v___x_5174_);
lean_inc_ref(v___y_5045_);
v___x_5176_ = lean_apply_2(v___y_5045_, v___x_5175_, lean_box(0));
v___x_5177_ = lean_box(0);
v___x_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5178_, 0, v___x_5177_);
return v___x_5178_;
}
}
}
}
else
{
lean_object* v___x_5180_; 
lean_dec_ref(v_leanOpts_5039_);
lean_dec_ref(v___y_5038_);
lean_dec_ref(v_pkg_5036_);
v___x_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5180_, 0, v_b_5044_);
return v___x_5180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_pkg_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v_leanOpts_5184_, lean_object* v_reconfigure_5185_, lean_object* v_as_5186_, lean_object* v_i_5187_, lean_object* v_stop_5188_, lean_object* v_b_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
uint8_t v_reconfigure_boxed_5192_; size_t v_i_boxed_5193_; size_t v_stop_boxed_5194_; lean_object* v_res_5195_; 
v_reconfigure_boxed_5192_ = lean_unbox(v_reconfigure_5185_);
v_i_boxed_5193_ = lean_unbox_usize(v_i_5187_);
lean_dec(v_i_5187_);
v_stop_boxed_5194_ = lean_unbox_usize(v_stop_5188_);
lean_dec(v_stop_5188_);
v_res_5195_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5181_, v___y_5182_, v___y_5183_, v_leanOpts_5184_, v_reconfigure_boxed_5192_, v_as_5186_, v_i_boxed_5193_, v_stop_boxed_5194_, v_b_5189_, v___y_5190_);
lean_dec_ref(v___y_5190_);
lean_dec_ref(v_as_5186_);
lean_dec(v___y_5182_);
return v_res_5195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_start_5196_, lean_object* v_pkg_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v_leanOpts_5200_, uint8_t v_reconfigure_5201_, lean_object* v_as_5202_, size_t v_i_5203_, size_t v_stop_5204_, lean_object* v_b_5205_, lean_object* v___y_5206_){
_start:
{
uint8_t v___x_5208_; 
v___x_5208_ = lean_usize_dec_eq(v_i_5203_, v_stop_5204_);
if (v___x_5208_ == 0)
{
lean_object* v_ws_5209_; lean_object* v_depIdxs_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5340_; 
v_ws_5209_ = lean_ctor_get(v_b_5205_, 0);
v_depIdxs_5210_ = lean_ctor_get(v_b_5205_, 1);
v_isSharedCheck_5340_ = !lean_is_exclusive(v_b_5205_);
if (v_isSharedCheck_5340_ == 0)
{
v___x_5212_ = v_b_5205_;
v_isShared_5213_ = v_isSharedCheck_5340_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_depIdxs_5210_);
lean_inc(v_ws_5209_);
lean_dec(v_b_5205_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5340_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v_lakeEnv_5214_; lean_object* v_packages_5215_; size_t v___x_5216_; size_t v___x_5217_; lean_object* v___x_5218_; lean_object* v___f_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; 
v_lakeEnv_5214_ = lean_ctor_get(v_ws_5209_, 0);
v_packages_5215_ = lean_ctor_get(v_ws_5209_, 4);
v___x_5216_ = ((size_t)1ULL);
v___x_5217_ = lean_usize_sub(v_i_5203_, v___x_5216_);
v___x_5218_ = lean_array_uget_borrowed(v_as_5202_, v___x_5217_);
lean_inc(v___x_5218_);
v___f_5219_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5219_, 0, v___x_5218_);
v___x_5220_ = lean_unsigned_to_nat(0u);
v___x_5221_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5219_, v_packages_5215_, v___x_5220_);
if (lean_obj_tag(v___x_5221_) == 1)
{
lean_object* v_val_5222_; lean_object* v___x_5223_; lean_object* v___x_5225_; 
v_val_5222_ = lean_ctor_get(v___x_5221_, 0);
lean_inc(v_val_5222_);
lean_dec_ref_known(v___x_5221_, 1);
v___x_5223_ = lean_array_push(v_depIdxs_5210_, v_val_5222_);
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 1, v___x_5223_);
v___x_5225_ = v___x_5212_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_ws_5209_);
lean_ctor_set(v_reuseFailAlloc_5227_, 1, v___x_5223_);
v___x_5225_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
lean_object* v___x_5226_; 
v___x_5226_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5197_, v___y_5198_, v___y_5199_, v_leanOpts_5200_, v_reconfigure_5201_, v_as_5202_, v___x_5217_, v_stop_5204_, v___x_5225_, v___y_5206_);
return v___x_5226_;
}
}
else
{
lean_object* v_wsIdx_5228_; lean_object* v_baseName_5229_; lean_object* v_name_5230_; lean_object* v_opts_5231_; uint8_t v___x_5232_; 
lean_dec(v___x_5221_);
v_wsIdx_5228_ = lean_ctor_get(v_pkg_5197_, 0);
v_baseName_5229_ = lean_ctor_get(v_pkg_5197_, 1);
v_name_5230_ = lean_ctor_get(v___x_5218_, 0);
v_opts_5231_ = lean_ctor_get(v___x_5218_, 4);
v___x_5232_ = lean_name_eq(v_baseName_5229_, v_name_5230_);
if (v___x_5232_ == 0)
{
lean_object* v___x_5233_; 
v___x_5233_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5198_, v_name_5230_);
if (lean_obj_tag(v___x_5233_) == 1)
{
lean_object* v_val_5234_; lean_object* v___x_5235_; lean_object* v_dir_5236_; lean_object* v___x_5237_; 
v_val_5234_ = lean_ctor_get(v___x_5233_, 0);
lean_inc(v_val_5234_);
lean_dec_ref_known(v___x_5233_, 1);
v___x_5235_ = lean_array_fget_borrowed(v_packages_5215_, v___x_5220_);
v_dir_5236_ = lean_ctor_get(v___x_5235_, 4);
lean_inc_ref(v___y_5199_);
lean_inc_ref(v_dir_5236_);
v___x_5237_ = l_Lake_PackageEntry_materialize(v_val_5234_, v_lakeEnv_5214_, v_dir_5236_, v___y_5199_, v___y_5206_);
if (lean_obj_tag(v___x_5237_) == 0)
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5294_; 
v_a_5238_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5240_ = v___x_5237_;
v_isShared_5241_ = v_isSharedCheck_5294_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5237_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5294_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5242_; lean_object* v_wsIdx_5243_; lean_object* v___x_5244_; 
v___x_5242_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_5243_ = lean_array_get_size(v_packages_5215_);
lean_inc_ref(v_leanOpts_5200_);
lean_inc(v_opts_5231_);
v___x_5244_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5209_, v_a_5238_, v_opts_5231_, v_leanOpts_5200_, v_reconfigure_5201_, v___x_5242_);
if (lean_obj_tag(v___x_5244_) == 0)
{
lean_object* v_a_5245_; lean_object* v_a_5246_; lean_object* v___x_5247_; lean_object* v___x_5249_; 
lean_del_object(v___x_5240_);
v_a_5245_ = lean_ctor_get(v___x_5244_, 0);
lean_inc(v_a_5245_);
v_a_5246_ = lean_ctor_get(v___x_5244_, 1);
lean_inc(v_a_5246_);
lean_dec_ref_known(v___x_5244_, 2);
v___x_5247_ = lean_array_push(v_depIdxs_5210_, v_wsIdx_5243_);
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 1, v___x_5247_);
lean_ctor_set(v___x_5212_, 0, v_a_5245_);
v___x_5249_ = v___x_5212_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5245_);
lean_ctor_set(v_reuseFailAlloc_5266_, 1, v___x_5247_);
v___x_5249_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
lean_object* v___x_5250_; uint8_t v___x_5251_; 
v___x_5250_ = lean_array_get_size(v_a_5246_);
v___x_5251_ = lean_nat_dec_lt(v___x_5220_, v___x_5250_);
if (v___x_5251_ == 0)
{
lean_object* v___x_5252_; 
lean_dec(v_a_5246_);
v___x_5252_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5197_, v___y_5198_, v___y_5199_, v_leanOpts_5200_, v_reconfigure_5201_, v_as_5202_, v___x_5217_, v_stop_5204_, v___x_5249_, v___y_5206_);
return v___x_5252_;
}
else
{
lean_object* v___x_5253_; size_t v___x_5254_; size_t v___x_5255_; lean_object* v___x_5256_; 
v___x_5253_ = lean_box(0);
v___x_5254_ = ((size_t)0ULL);
v___x_5255_ = lean_usize_of_nat(v___x_5250_);
v___x_5256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5246_, v___x_5254_, v___x_5255_, v___x_5253_, v___y_5206_);
lean_dec(v_a_5246_);
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v___x_5257_; 
lean_dec_ref_known(v___x_5256_, 1);
v___x_5257_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5197_, v___y_5198_, v___y_5199_, v_leanOpts_5200_, v_reconfigure_5201_, v_as_5202_, v___x_5217_, v_stop_5204_, v___x_5249_, v___y_5206_);
return v___x_5257_;
}
else
{
lean_object* v_a_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5265_; 
lean_dec_ref(v___x_5249_);
lean_dec_ref(v_leanOpts_5200_);
lean_dec_ref(v___y_5199_);
lean_dec_ref(v_pkg_5197_);
v_a_5258_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5260_ = v___x_5256_;
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_a_5258_);
lean_dec(v___x_5256_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v___x_5263_; 
if (v_isShared_5261_ == 0)
{
v___x_5263_ = v___x_5260_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_a_5258_);
v___x_5263_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
return v___x_5263_;
}
}
}
}
}
}
else
{
lean_object* v_a_5267_; lean_object* v___x_5268_; uint8_t v___x_5269_; 
lean_del_object(v___x_5212_);
lean_dec_ref(v_depIdxs_5210_);
lean_dec_ref(v_leanOpts_5200_);
lean_dec_ref(v___y_5199_);
lean_dec_ref(v_pkg_5197_);
v_a_5267_ = lean_ctor_get(v___x_5244_, 1);
lean_inc(v_a_5267_);
lean_dec_ref_known(v___x_5244_, 2);
v___x_5268_ = lean_array_get_size(v_a_5267_);
v___x_5269_ = lean_nat_dec_lt(v___x_5220_, v___x_5268_);
if (v___x_5269_ == 0)
{
lean_object* v___x_5270_; lean_object* v___x_5272_; 
lean_dec(v_a_5267_);
v___x_5270_ = lean_box(0);
if (v_isShared_5241_ == 0)
{
lean_ctor_set_tag(v___x_5240_, 1);
lean_ctor_set(v___x_5240_, 0, v___x_5270_);
v___x_5272_ = v___x_5240_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5270_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
else
{
lean_object* v___x_5274_; size_t v___x_5275_; size_t v___x_5276_; lean_object* v___x_5277_; 
lean_del_object(v___x_5240_);
v___x_5274_ = lean_box(0);
v___x_5275_ = ((size_t)0ULL);
v___x_5276_ = lean_usize_of_nat(v___x_5268_);
v___x_5277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5267_, v___x_5275_, v___x_5276_, v___x_5274_, v___y_5206_);
lean_dec(v_a_5267_);
if (lean_obj_tag(v___x_5277_) == 0)
{
lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5284_; 
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5284_ == 0)
{
lean_object* v_unused_5285_; 
v_unused_5285_ = lean_ctor_get(v___x_5277_, 0);
lean_dec(v_unused_5285_);
v___x_5279_ = v___x_5277_;
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
else
{
lean_dec(v___x_5277_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5282_; 
if (v_isShared_5280_ == 0)
{
lean_ctor_set_tag(v___x_5279_, 1);
lean_ctor_set(v___x_5279_, 0, v___x_5274_);
v___x_5282_ = v___x_5279_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5274_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
else
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5293_; 
v_a_5286_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5288_ = v___x_5277_;
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___x_5277_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5291_; 
if (v_isShared_5289_ == 0)
{
v___x_5291_ = v___x_5288_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5302_; 
lean_del_object(v___x_5212_);
lean_dec_ref(v_depIdxs_5210_);
lean_dec_ref(v_ws_5209_);
lean_dec_ref(v_leanOpts_5200_);
lean_dec_ref(v___y_5199_);
lean_dec_ref(v_pkg_5197_);
v_a_5295_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5297_ = v___x_5237_;
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_dec(v___x_5237_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5300_; 
if (v_isShared_5298_ == 0)
{
v___x_5300_ = v___x_5297_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_a_5295_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
}
else
{
uint8_t v___x_5303_; 
lean_inc(v_baseName_5229_);
lean_inc(v_wsIdx_5228_);
lean_dec(v___x_5233_);
lean_del_object(v___x_5212_);
lean_dec_ref(v_depIdxs_5210_);
lean_dec_ref(v_ws_5209_);
lean_dec_ref(v_leanOpts_5200_);
lean_dec_ref(v___y_5199_);
lean_dec_ref(v_pkg_5197_);
v___x_5303_ = lean_nat_dec_eq(v_wsIdx_5228_, v___x_5220_);
lean_dec(v_wsIdx_5228_);
if (v___x_5303_ == 0)
{
lean_object* v___x_5304_; uint8_t v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; uint8_t v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5305_ = 1;
lean_inc(v_name_5230_);
v___x_5306_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5230_, v___x_5305_);
v___x_5307_ = lean_string_append(v___x_5304_, v___x_5306_);
lean_dec_ref(v___x_5306_);
v___x_5308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5309_ = lean_string_append(v___x_5307_, v___x_5308_);
v___x_5310_ = l_Lean_Name_toString(v_baseName_5229_, v___x_5303_);
v___x_5311_ = lean_string_append(v___x_5309_, v___x_5310_);
lean_dec_ref(v___x_5310_);
v___x_5312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5313_ = lean_string_append(v___x_5311_, v___x_5312_);
v___x_5314_ = 3;
v___x_5315_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5315_, 0, v___x_5313_);
lean_ctor_set_uint8(v___x_5315_, sizeof(void*)*1, v___x_5314_);
lean_inc_ref(v___y_5206_);
v___x_5316_ = lean_apply_2(v___y_5206_, v___x_5315_, lean_box(0));
v___x_5317_ = lean_box(0);
v___x_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5317_);
return v___x_5318_;
}
else
{
lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; uint8_t v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; 
lean_dec(v_baseName_5229_);
v___x_5319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5230_);
v___x_5320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5230_, v___x_5303_);
v___x_5321_ = lean_string_append(v___x_5319_, v___x_5320_);
v___x_5322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5323_ = lean_string_append(v___x_5321_, v___x_5322_);
v___x_5324_ = lean_string_append(v___x_5323_, v___x_5320_);
lean_dec_ref(v___x_5320_);
v___x_5325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5326_ = lean_string_append(v___x_5324_, v___x_5325_);
v___x_5327_ = 3;
v___x_5328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5328_, 0, v___x_5326_);
lean_ctor_set_uint8(v___x_5328_, sizeof(void*)*1, v___x_5327_);
lean_inc_ref(v___y_5206_);
v___x_5329_ = lean_apply_2(v___y_5206_, v___x_5328_, lean_box(0));
v___x_5330_ = lean_box(0);
v___x_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5330_);
return v___x_5331_;
}
}
}
else
{
lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; uint8_t v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; 
lean_inc(v_baseName_5229_);
lean_del_object(v___x_5212_);
lean_dec_ref(v_depIdxs_5210_);
lean_dec_ref(v_ws_5209_);
lean_dec_ref(v_leanOpts_5200_);
lean_dec_ref(v___y_5199_);
lean_dec_ref(v_pkg_5197_);
v___x_5332_ = l_Lean_Name_toString(v_baseName_5229_, v___x_5208_);
v___x_5333_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5334_ = lean_string_append(v___x_5332_, v___x_5333_);
v___x_5335_ = 3;
v___x_5336_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5336_, 0, v___x_5334_);
lean_ctor_set_uint8(v___x_5336_, sizeof(void*)*1, v___x_5335_);
lean_inc_ref(v___y_5206_);
v___x_5337_ = lean_apply_2(v___y_5206_, v___x_5336_, lean_box(0));
v___x_5338_ = lean_box(0);
v___x_5339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5339_, 0, v___x_5338_);
return v___x_5339_;
}
}
}
}
else
{
lean_object* v___x_5341_; 
lean_dec_ref(v_leanOpts_5200_);
lean_dec_ref(v___y_5199_);
lean_dec_ref(v_pkg_5197_);
v___x_5341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5341_, 0, v_b_5205_);
return v___x_5341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_start_5342_, lean_object* v_pkg_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v_leanOpts_5346_, lean_object* v_reconfigure_5347_, lean_object* v_as_5348_, lean_object* v_i_5349_, lean_object* v_stop_5350_, lean_object* v_b_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_){
_start:
{
uint8_t v_reconfigure_boxed_5354_; size_t v_i_boxed_5355_; size_t v_stop_boxed_5356_; lean_object* v_res_5357_; 
v_reconfigure_boxed_5354_ = lean_unbox(v_reconfigure_5347_);
v_i_boxed_5355_ = lean_unbox_usize(v_i_5349_);
lean_dec(v_i_5349_);
v_stop_boxed_5356_ = lean_unbox_usize(v_stop_5350_);
lean_dec(v_stop_5350_);
v_res_5357_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5342_, v_pkg_5343_, v___y_5344_, v___y_5345_, v_leanOpts_5346_, v_reconfigure_boxed_5354_, v_as_5348_, v_i_boxed_5355_, v_stop_boxed_5356_, v_b_5351_, v___y_5352_);
lean_dec_ref(v___y_5352_);
lean_dec_ref(v_as_5348_);
lean_dec(v___y_5344_);
lean_dec(v_start_5342_);
return v_res_5357_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v_leanOpts_5360_, uint8_t v_reconfigure_5361_, lean_object* v_ws_5362_, lean_object* v_i_5363_, lean_object* v_next_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v_packages_5367_; lean_object* v_pkg_5368_; lean_object* v_ws_5370_; lean_object* v_depIdxs_5371_; lean_object* v___y_5372_; lean_object* v_____x_5382_; lean_object* v___y_5383_; lean_object* v_depConfigs_5386_; lean_object* v_start_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v_s_5390_; lean_object* v___x_5391_; uint8_t v___x_5392_; 
v_packages_5367_ = lean_ctor_get(v_ws_5362_, 4);
v_pkg_5368_ = lean_array_fget(v_packages_5367_, v_i_5363_);
lean_dec(v_i_5363_);
v_depConfigs_5386_ = lean_ctor_get(v_pkg_5368_, 12);
v_start_5387_ = lean_array_get_size(v_packages_5367_);
v___x_5388_ = lean_array_get_size(v_depConfigs_5386_);
v___x_5389_ = lean_mk_empty_array_with_capacity(v___x_5388_);
lean_inc_ref(v___x_5389_);
lean_inc_ref(v_ws_5362_);
v_s_5390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5390_, 0, v_ws_5362_);
lean_ctor_set(v_s_5390_, 1, v___x_5389_);
v___x_5391_ = lean_unsigned_to_nat(0u);
v___x_5392_ = lean_nat_dec_le(v___x_5388_, v___x_5388_);
if (v___x_5392_ == 0)
{
uint8_t v___x_5393_; 
v___x_5393_ = lean_nat_dec_lt(v___x_5391_, v___x_5388_);
if (v___x_5393_ == 0)
{
lean_object* v_ws_5394_; lean_object* v_packages_5395_; lean_object* v___x_5396_; uint8_t v___x_5397_; 
lean_dec_ref_known(v_s_5390_, 2);
v_ws_5394_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5362_, v_pkg_5368_, v___x_5389_);
v_packages_5395_ = lean_ctor_get(v_ws_5394_, 4);
lean_inc_ref(v_packages_5395_);
v___x_5396_ = lean_array_get_size(v_packages_5395_);
lean_dec_ref(v_packages_5395_);
v___x_5397_ = lean_nat_dec_lt(v_next_5364_, v___x_5396_);
if (v___x_5397_ == 0)
{
lean_object* v___x_5398_; 
lean_dec(v_next_5364_);
lean_dec_ref(v_leanOpts_5360_);
lean_dec_ref(v___y_5359_);
v___x_5398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5398_, 0, v_ws_5394_);
return v___x_5398_;
}
else
{
lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5399_ = lean_unsigned_to_nat(1u);
v___x_5400_ = lean_nat_add(v_next_5364_, v___x_5399_);
v_ws_5362_ = v_ws_5394_;
v_i_5363_ = v_next_5364_;
v_next_5364_ = v___x_5400_;
goto _start;
}
}
else
{
size_t v___x_5402_; size_t v___x_5403_; lean_object* v___x_5404_; 
lean_dec_ref(v___x_5389_);
lean_dec_ref(v_ws_5362_);
v___x_5402_ = lean_usize_of_nat(v___x_5388_);
v___x_5403_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5360_);
lean_inc_ref(v___y_5359_);
lean_inc(v_pkg_5368_);
v___x_5404_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5387_, v_pkg_5368_, v___y_5358_, v___y_5359_, v_leanOpts_5360_, v_reconfigure_5361_, v_depConfigs_5386_, v___x_5402_, v___x_5403_, v_s_5390_, v___y_5365_);
if (lean_obj_tag(v___x_5404_) == 0)
{
lean_object* v_a_5405_; 
v_a_5405_ = lean_ctor_get(v___x_5404_, 0);
lean_inc(v_a_5405_);
lean_dec_ref_known(v___x_5404_, 1);
v_____x_5382_ = v_a_5405_;
v___y_5383_ = v___y_5365_;
goto v___jp_5381_;
}
else
{
lean_object* v_a_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5413_; 
lean_dec(v_pkg_5368_);
lean_dec(v_next_5364_);
lean_dec_ref(v_leanOpts_5360_);
lean_dec_ref(v___y_5359_);
v_a_5406_ = lean_ctor_get(v___x_5404_, 0);
v_isSharedCheck_5413_ = !lean_is_exclusive(v___x_5404_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5408_ = v___x_5404_;
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_a_5406_);
lean_dec(v___x_5404_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v___x_5411_; 
if (v_isShared_5409_ == 0)
{
v___x_5411_ = v___x_5408_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_a_5406_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
return v___x_5411_;
}
}
}
}
}
else
{
uint8_t v___x_5414_; 
v___x_5414_ = lean_nat_dec_lt(v___x_5391_, v___x_5388_);
if (v___x_5414_ == 0)
{
lean_dec_ref_known(v_s_5390_, 2);
v_ws_5370_ = v_ws_5362_;
v_depIdxs_5371_ = v___x_5389_;
v___y_5372_ = v___y_5365_;
goto v___jp_5369_;
}
else
{
size_t v___x_5415_; size_t v___x_5416_; lean_object* v___x_5417_; 
lean_dec_ref(v___x_5389_);
lean_dec_ref(v_ws_5362_);
v___x_5415_ = lean_usize_of_nat(v___x_5388_);
v___x_5416_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5360_);
lean_inc_ref(v___y_5359_);
lean_inc(v_pkg_5368_);
v___x_5417_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5387_, v_pkg_5368_, v___y_5358_, v___y_5359_, v_leanOpts_5360_, v_reconfigure_5361_, v_depConfigs_5386_, v___x_5415_, v___x_5416_, v_s_5390_, v___y_5365_);
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_object* v_a_5418_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
lean_inc(v_a_5418_);
lean_dec_ref_known(v___x_5417_, 1);
v_____x_5382_ = v_a_5418_;
v___y_5383_ = v___y_5365_;
goto v___jp_5381_;
}
else
{
lean_object* v_a_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5426_; 
lean_dec(v_pkg_5368_);
lean_dec(v_next_5364_);
lean_dec_ref(v_leanOpts_5360_);
lean_dec_ref(v___y_5359_);
v_a_5419_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5426_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5421_ = v___x_5417_;
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_a_5419_);
lean_dec(v___x_5417_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5424_; 
if (v_isShared_5422_ == 0)
{
v___x_5424_ = v___x_5421_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_a_5419_);
v___x_5424_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
return v___x_5424_;
}
}
}
}
}
v___jp_5369_:
{
lean_object* v_ws_5373_; lean_object* v_packages_5374_; lean_object* v___x_5375_; uint8_t v___x_5376_; 
v_ws_5373_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5370_, v_pkg_5368_, v_depIdxs_5371_);
v_packages_5374_ = lean_ctor_get(v_ws_5373_, 4);
lean_inc_ref(v_packages_5374_);
v___x_5375_ = lean_array_get_size(v_packages_5374_);
lean_dec_ref(v_packages_5374_);
v___x_5376_ = lean_nat_dec_lt(v_next_5364_, v___x_5375_);
if (v___x_5376_ == 0)
{
lean_object* v___x_5377_; 
lean_dec(v_next_5364_);
lean_dec_ref(v_leanOpts_5360_);
lean_dec_ref(v___y_5359_);
v___x_5377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5377_, 0, v_ws_5373_);
return v___x_5377_;
}
else
{
lean_object* v___x_5378_; lean_object* v___x_5379_; 
v___x_5378_ = lean_unsigned_to_nat(1u);
v___x_5379_ = lean_nat_add(v_next_5364_, v___x_5378_);
v_ws_5362_ = v_ws_5373_;
v_i_5363_ = v_next_5364_;
v_next_5364_ = v___x_5379_;
v___y_5365_ = v___y_5372_;
goto _start;
}
}
v___jp_5381_:
{
lean_object* v_ws_5384_; lean_object* v_depIdxs_5385_; 
v_ws_5384_ = lean_ctor_get(v_____x_5382_, 0);
lean_inc_ref(v_ws_5384_);
v_depIdxs_5385_ = lean_ctor_get(v_____x_5382_, 1);
lean_inc_ref(v_depIdxs_5385_);
lean_dec_ref(v_____x_5382_);
v_ws_5370_ = v_ws_5384_;
v_depIdxs_5371_ = v_depIdxs_5385_;
v___y_5372_ = v___y_5383_;
goto v___jp_5369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v_leanOpts_5429_, lean_object* v_reconfigure_5430_, lean_object* v_ws_5431_, lean_object* v_i_5432_, lean_object* v_next_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
uint8_t v_reconfigure_boxed_5436_; lean_object* v_res_5437_; 
v_reconfigure_boxed_5436_ = lean_unbox(v_reconfigure_5430_);
v_res_5437_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5427_, v___y_5428_, v_leanOpts_5429_, v_reconfigure_boxed_5436_, v_ws_5431_, v_i_5432_, v_next_5433_, v___y_5434_);
lean_dec_ref(v___y_5434_);
lean_dec(v___y_5427_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(lean_object* v_as_5438_, size_t v_i_5439_, size_t v_stop_5440_, lean_object* v_b_5441_){
_start:
{
uint8_t v___x_5442_; 
v___x_5442_ = lean_usize_dec_eq(v_i_5439_, v_stop_5440_);
if (v___x_5442_ == 0)
{
lean_object* v___x_5443_; lean_object* v_name_5444_; lean_object* v___x_5445_; size_t v___x_5446_; size_t v___x_5447_; 
v___x_5443_ = lean_array_uget_borrowed(v_as_5438_, v_i_5439_);
v_name_5444_ = lean_ctor_get(v___x_5443_, 0);
lean_inc(v___x_5443_);
lean_inc(v_name_5444_);
v___x_5445_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5444_, v___x_5443_, v_b_5441_);
v___x_5446_ = ((size_t)1ULL);
v___x_5447_ = lean_usize_add(v_i_5439_, v___x_5446_);
v_i_5439_ = v___x_5447_;
v_b_5441_ = v___x_5445_;
goto _start;
}
else
{
return v_b_5441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2___boxed(lean_object* v_as_5449_, lean_object* v_i_5450_, lean_object* v_stop_5451_, lean_object* v_b_5452_){
_start:
{
size_t v_i_boxed_5453_; size_t v_stop_boxed_5454_; lean_object* v_res_5455_; 
v_i_boxed_5453_ = lean_unbox_usize(v_i_5450_);
lean_dec(v_i_5450_);
v_stop_boxed_5454_ = lean_unbox_usize(v_stop_5451_);
lean_dec(v_stop_5451_);
v_res_5455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5449_, v_i_boxed_5453_, v_stop_boxed_5454_, v_b_5452_);
lean_dec_ref(v_as_5449_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5456_, size_t v_i_5457_, size_t v_stop_5458_, lean_object* v_b_5459_){
_start:
{
uint8_t v___x_5460_; 
v___x_5460_ = lean_usize_dec_eq(v_i_5457_, v_stop_5458_);
if (v___x_5460_ == 0)
{
lean_object* v___x_5461_; lean_object* v_name_5462_; lean_object* v___x_5463_; size_t v___x_5464_; size_t v___x_5465_; lean_object* v___x_5466_; 
v___x_5461_ = lean_array_uget_borrowed(v_as_5456_, v_i_5457_);
v_name_5462_ = lean_ctor_get(v___x_5461_, 0);
lean_inc(v___x_5461_);
lean_inc(v_name_5462_);
v___x_5463_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5462_, v___x_5461_, v_b_5459_);
v___x_5464_ = ((size_t)1ULL);
v___x_5465_ = lean_usize_add(v_i_5457_, v___x_5464_);
v___x_5466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5456_, v___x_5465_, v_stop_5458_, v___x_5463_);
return v___x_5466_;
}
else
{
return v_b_5459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5467_, lean_object* v_i_5468_, lean_object* v_stop_5469_, lean_object* v_b_5470_){
_start:
{
size_t v_i_boxed_5471_; size_t v_stop_boxed_5472_; lean_object* v_res_5473_; 
v_i_boxed_5471_ = lean_unbox_usize(v_i_5468_);
lean_dec(v_i_5468_);
v_stop_boxed_5472_ = lean_unbox_usize(v_stop_5469_);
lean_dec(v_stop_5469_);
v_res_5473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5467_, v_i_boxed_5471_, v_stop_boxed_5472_, v_b_5470_);
lean_dec_ref(v_as_5467_);
return v_res_5473_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5483_, lean_object* v_manifest_5484_, lean_object* v_leanOpts_5485_, uint8_t v_reconfigure_5486_, lean_object* v_overrides_5487_, lean_object* v_a_5488_){
_start:
{
lean_object* v___y_5491_; lean_object* v___y_5492_; lean_object* v___y_5493_; lean_object* v___y_5494_; lean_object* v___y_5495_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v___y_5510_; lean_object* v___y_5511_; lean_object* v___y_5512_; lean_object* v___y_5513_; lean_object* v___y_5514_; lean_object* v___y_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; lean_object* v___y_5528_; lean_object* v___y_5539_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v_packagesDir_x3f_5585_; lean_object* v_packages_5586_; lean_object* v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5602_; lean_object* v___x_5610_; lean_object* v___x_5611_; uint8_t v___x_5612_; 
v_packagesDir_x3f_5585_ = lean_ctor_get(v_manifest_5484_, 2);
lean_inc(v_packagesDir_x3f_5585_);
v_packages_5586_ = lean_ctor_get(v_manifest_5484_, 3);
lean_inc_ref(v_packages_5586_);
lean_dec_ref(v_manifest_5484_);
v___x_5610_ = lean_array_get_size(v_packages_5586_);
v___x_5611_ = lean_unsigned_to_nat(0u);
v___x_5612_ = lean_nat_dec_eq(v___x_5610_, v___x_5611_);
if (v___x_5612_ == 0)
{
lean_object* v_packages_5613_; lean_object* v___x_5614_; lean_object* v_config_5615_; lean_object* v_toWorkspaceConfig_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; uint8_t v___x_5620_; 
v_packages_5613_ = lean_ctor_get(v_ws_5483_, 4);
v___x_5614_ = lean_array_fget_borrowed(v_packages_5613_, v___x_5611_);
v_config_5615_ = lean_ctor_get(v___x_5614_, 6);
v_toWorkspaceConfig_5616_ = lean_ctor_get(v_config_5615_, 0);
lean_inc_ref(v_toWorkspaceConfig_5616_);
v___x_5617_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5616_);
v___x_5618_ = l_Lake_mkRelPathString(v___x_5617_);
v___x_5619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5618_);
v___x_5620_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5585_, v___x_5619_);
lean_dec_ref_known(v___x_5619_, 1);
if (v___x_5620_ == 0)
{
lean_object* v___x_5621_; lean_object* v___x_5622_; 
v___x_5621_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5488_);
v___x_5622_ = lean_apply_2(v_a_5488_, v___x_5621_, lean_box(0));
v___y_5602_ = v_a_5488_;
goto v___jp_5601_;
}
else
{
v___y_5602_ = v_a_5488_;
goto v___jp_5601_;
}
}
else
{
v___y_5602_ = v_a_5488_;
goto v___jp_5601_;
}
v___jp_5490_:
{
lean_object* v___x_5496_; lean_object* v___x_5497_; 
v___x_5496_ = lean_array_get_size(v___y_5491_);
lean_dec_ref(v___y_5491_);
v___x_5497_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5494_, v___y_5495_, v_leanOpts_5485_, v_reconfigure_5486_, v_ws_5483_, v___y_5493_, v___x_5496_, v___y_5492_);
lean_dec(v___y_5494_);
if (lean_obj_tag(v___x_5497_) == 0)
{
lean_object* v_a_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5506_; 
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5497_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5500_ = v___x_5497_;
v_isShared_5501_ = v_isSharedCheck_5506_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5497_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5506_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5502_; lean_object* v___x_5504_; 
v___x_5502_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_a_5498_);
if (v_isShared_5501_ == 0)
{
lean_ctor_set(v___x_5500_, 0, v___x_5502_);
v___x_5504_ = v___x_5500_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5502_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
else
{
return v___x_5497_;
}
}
v___jp_5507_:
{
if (lean_obj_tag(v___y_5514_) == 0)
{
lean_dec_ref(v___y_5508_);
v___y_5491_ = v___y_5509_;
v___y_5492_ = v___y_5511_;
v___y_5493_ = v___y_5512_;
v___y_5494_ = v___y_5514_;
v___y_5495_ = v___y_5513_;
goto v___jp_5490_;
}
else
{
lean_object* v___x_5515_; uint8_t v___x_5516_; 
v___x_5515_ = lean_array_get_size(v___y_5508_);
lean_dec_ref(v___y_5508_);
v___x_5516_ = lean_nat_dec_eq(v___x_5515_, v___y_5510_);
if (v___x_5516_ == 0)
{
lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; 
lean_dec_ref(v___y_5513_);
lean_dec(v___y_5512_);
lean_dec_ref(v___y_5509_);
lean_dec_ref(v_leanOpts_5485_);
lean_dec_ref(v_ws_5483_);
v___x_5517_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5511_);
v___x_5518_ = lean_apply_2(v___y_5511_, v___x_5517_, lean_box(0));
v___x_5519_ = lean_box(0);
v___x_5520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5520_, 0, v___x_5519_);
return v___x_5520_;
}
else
{
v___y_5491_ = v___y_5509_;
v___y_5492_ = v___y_5511_;
v___y_5493_ = v___y_5512_;
v___y_5494_ = v___y_5514_;
v___y_5495_ = v___y_5513_;
goto v___jp_5490_;
}
}
}
v___jp_5521_:
{
lean_object* v___x_5529_; uint8_t v___x_5530_; 
v___x_5529_ = lean_array_get_size(v_overrides_5487_);
v___x_5530_ = lean_nat_dec_lt(v___y_5524_, v___x_5529_);
if (v___x_5530_ == 0)
{
v___y_5508_ = v___y_5522_;
v___y_5509_ = v___y_5523_;
v___y_5510_ = v___y_5524_;
v___y_5511_ = v___y_5525_;
v___y_5512_ = v___y_5526_;
v___y_5513_ = v___y_5527_;
v___y_5514_ = v___y_5528_;
goto v___jp_5507_;
}
else
{
uint8_t v___x_5531_; 
v___x_5531_ = lean_nat_dec_le(v___x_5529_, v___x_5529_);
if (v___x_5531_ == 0)
{
if (v___x_5530_ == 0)
{
v___y_5508_ = v___y_5522_;
v___y_5509_ = v___y_5523_;
v___y_5510_ = v___y_5524_;
v___y_5511_ = v___y_5525_;
v___y_5512_ = v___y_5526_;
v___y_5513_ = v___y_5527_;
v___y_5514_ = v___y_5528_;
goto v___jp_5507_;
}
else
{
size_t v___x_5532_; size_t v___x_5533_; lean_object* v___x_5534_; 
v___x_5532_ = ((size_t)0ULL);
v___x_5533_ = lean_usize_of_nat(v___x_5529_);
v___x_5534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5487_, v___x_5532_, v___x_5533_, v___y_5528_);
v___y_5508_ = v___y_5522_;
v___y_5509_ = v___y_5523_;
v___y_5510_ = v___y_5524_;
v___y_5511_ = v___y_5525_;
v___y_5512_ = v___y_5526_;
v___y_5513_ = v___y_5527_;
v___y_5514_ = v___x_5534_;
goto v___jp_5507_;
}
}
else
{
size_t v___x_5535_; size_t v___x_5536_; lean_object* v___x_5537_; 
v___x_5535_ = ((size_t)0ULL);
v___x_5536_ = lean_usize_of_nat(v___x_5529_);
v___x_5537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5487_, v___x_5535_, v___x_5536_, v___y_5528_);
v___y_5508_ = v___y_5522_;
v___y_5509_ = v___y_5523_;
v___y_5510_ = v___y_5524_;
v___y_5511_ = v___y_5525_;
v___y_5512_ = v___y_5526_;
v___y_5513_ = v___y_5527_;
v___y_5514_ = v___x_5537_;
goto v___jp_5507_;
}
}
}
v___jp_5538_:
{
lean_object* v_packages_5543_; lean_object* v___x_5544_; lean_object* v_wsIdx_5545_; lean_object* v_dir_5546_; lean_object* v_depConfigs_5547_; lean_object* v___x_5548_; 
v_packages_5543_ = lean_ctor_get(v_ws_5483_, 4);
v___x_5544_ = lean_array_fget_borrowed(v_packages_5543_, v___y_5539_);
v_wsIdx_5545_ = lean_ctor_get(v___x_5544_, 0);
v_dir_5546_ = lean_ctor_get(v___x_5544_, 4);
v_depConfigs_5547_ = lean_ctor_get(v___x_5544_, 12);
v___x_5548_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5542_, v_depConfigs_5547_, v___y_5540_);
if (lean_obj_tag(v___x_5548_) == 0)
{
lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; 
lean_dec_ref_known(v___x_5548_, 1);
v___x_5549_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5546_);
v___x_5550_ = l_Lake_joinRelative(v_dir_5546_, v___x_5549_);
v___x_5551_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5552_ = l_Lake_joinRelative(v___x_5550_, v___x_5551_);
v___x_5553_ = l_Lake_Manifest_tryLoadEntries(v___x_5552_);
if (lean_obj_tag(v___x_5553_) == 0)
{
lean_object* v_a_5554_; lean_object* v___x_5555_; uint8_t v___x_5556_; 
v_a_5554_ = lean_ctor_get(v___x_5553_, 0);
lean_inc(v_a_5554_);
lean_dec_ref_known(v___x_5553_, 1);
v___x_5555_ = lean_array_get_size(v_a_5554_);
v___x_5556_ = lean_nat_dec_lt(v___y_5539_, v___x_5555_);
if (v___x_5556_ == 0)
{
lean_dec(v_a_5554_);
lean_inc(v_wsIdx_5545_);
lean_inc_ref(v_packages_5543_);
lean_inc_ref(v_depConfigs_5547_);
v___y_5522_ = v_depConfigs_5547_;
v___y_5523_ = v_packages_5543_;
v___y_5524_ = v___y_5539_;
v___y_5525_ = v___y_5540_;
v___y_5526_ = v_wsIdx_5545_;
v___y_5527_ = v___y_5541_;
v___y_5528_ = v___y_5542_;
goto v___jp_5521_;
}
else
{
uint8_t v___x_5557_; 
v___x_5557_ = lean_nat_dec_le(v___x_5555_, v___x_5555_);
if (v___x_5557_ == 0)
{
if (v___x_5556_ == 0)
{
lean_dec(v_a_5554_);
lean_inc(v_wsIdx_5545_);
lean_inc_ref(v_packages_5543_);
lean_inc_ref(v_depConfigs_5547_);
v___y_5522_ = v_depConfigs_5547_;
v___y_5523_ = v_packages_5543_;
v___y_5524_ = v___y_5539_;
v___y_5525_ = v___y_5540_;
v___y_5526_ = v_wsIdx_5545_;
v___y_5527_ = v___y_5541_;
v___y_5528_ = v___y_5542_;
goto v___jp_5521_;
}
else
{
size_t v___x_5558_; size_t v___x_5559_; lean_object* v___x_5560_; 
v___x_5558_ = ((size_t)0ULL);
v___x_5559_ = lean_usize_of_nat(v___x_5555_);
v___x_5560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5554_, v___x_5558_, v___x_5559_, v___y_5542_);
lean_dec(v_a_5554_);
lean_inc(v_wsIdx_5545_);
lean_inc_ref(v_packages_5543_);
lean_inc_ref(v_depConfigs_5547_);
v___y_5522_ = v_depConfigs_5547_;
v___y_5523_ = v_packages_5543_;
v___y_5524_ = v___y_5539_;
v___y_5525_ = v___y_5540_;
v___y_5526_ = v_wsIdx_5545_;
v___y_5527_ = v___y_5541_;
v___y_5528_ = v___x_5560_;
goto v___jp_5521_;
}
}
else
{
size_t v___x_5561_; size_t v___x_5562_; lean_object* v___x_5563_; 
v___x_5561_ = ((size_t)0ULL);
v___x_5562_ = lean_usize_of_nat(v___x_5555_);
v___x_5563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5554_, v___x_5561_, v___x_5562_, v___y_5542_);
lean_dec(v_a_5554_);
lean_inc(v_wsIdx_5545_);
lean_inc_ref(v_packages_5543_);
lean_inc_ref(v_depConfigs_5547_);
v___y_5522_ = v_depConfigs_5547_;
v___y_5523_ = v_packages_5543_;
v___y_5524_ = v___y_5539_;
v___y_5525_ = v___y_5540_;
v___y_5526_ = v_wsIdx_5545_;
v___y_5527_ = v___y_5541_;
v___y_5528_ = v___x_5563_;
goto v___jp_5521_;
}
}
}
else
{
lean_object* v_a_5564_; lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5576_; 
lean_dec(v___y_5542_);
lean_dec_ref(v___y_5541_);
lean_dec_ref(v_leanOpts_5485_);
lean_dec_ref(v_ws_5483_);
v_a_5564_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5576_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5576_ == 0)
{
v___x_5566_ = v___x_5553_;
v_isShared_5567_ = v_isSharedCheck_5576_;
goto v_resetjp_5565_;
}
else
{
lean_inc(v_a_5564_);
lean_dec(v___x_5553_);
v___x_5566_ = lean_box(0);
v_isShared_5567_ = v_isSharedCheck_5576_;
goto v_resetjp_5565_;
}
v_resetjp_5565_:
{
lean_object* v___x_5568_; uint8_t v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5574_; 
v___x_5568_ = lean_io_error_to_string(v_a_5564_);
v___x_5569_ = 3;
v___x_5570_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5570_, 0, v___x_5568_);
lean_ctor_set_uint8(v___x_5570_, sizeof(void*)*1, v___x_5569_);
lean_inc_ref(v___y_5540_);
v___x_5571_ = lean_apply_2(v___y_5540_, v___x_5570_, lean_box(0));
v___x_5572_ = lean_box(0);
if (v_isShared_5567_ == 0)
{
lean_ctor_set(v___x_5566_, 0, v___x_5572_);
v___x_5574_ = v___x_5566_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v___x_5572_);
v___x_5574_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
return v___x_5574_;
}
}
}
}
else
{
lean_object* v_a_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5584_; 
lean_dec(v___y_5542_);
lean_dec_ref(v___y_5541_);
lean_dec_ref(v_leanOpts_5485_);
lean_dec_ref(v_ws_5483_);
v_a_5577_ = lean_ctor_get(v___x_5548_, 0);
v_isSharedCheck_5584_ = !lean_is_exclusive(v___x_5548_);
if (v_isSharedCheck_5584_ == 0)
{
v___x_5579_ = v___x_5548_;
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_a_5577_);
lean_dec(v___x_5548_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5582_; 
if (v_isShared_5580_ == 0)
{
v___x_5582_ = v___x_5579_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_a_5577_);
v___x_5582_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
return v___x_5582_;
}
}
}
}
v___jp_5587_:
{
lean_object* v_pkgEntries_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; uint8_t v___x_5593_; 
v_pkgEntries_5590_ = lean_box(1);
v___x_5591_ = lean_unsigned_to_nat(0u);
v___x_5592_ = lean_array_get_size(v_packages_5586_);
v___x_5593_ = lean_nat_dec_lt(v___x_5591_, v___x_5592_);
if (v___x_5593_ == 0)
{
lean_dec_ref(v_packages_5586_);
v___y_5539_ = v___x_5591_;
v___y_5540_ = v___y_5588_;
v___y_5541_ = v___y_5589_;
v___y_5542_ = v_pkgEntries_5590_;
goto v___jp_5538_;
}
else
{
uint8_t v___x_5594_; 
v___x_5594_ = lean_nat_dec_le(v___x_5592_, v___x_5592_);
if (v___x_5594_ == 0)
{
if (v___x_5593_ == 0)
{
lean_dec_ref(v_packages_5586_);
v___y_5539_ = v___x_5591_;
v___y_5540_ = v___y_5588_;
v___y_5541_ = v___y_5589_;
v___y_5542_ = v_pkgEntries_5590_;
goto v___jp_5538_;
}
else
{
size_t v___x_5595_; size_t v___x_5596_; lean_object* v___x_5597_; 
v___x_5595_ = ((size_t)0ULL);
v___x_5596_ = lean_usize_of_nat(v___x_5592_);
v___x_5597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5586_, v___x_5595_, v___x_5596_, v_pkgEntries_5590_);
lean_dec_ref(v_packages_5586_);
v___y_5539_ = v___x_5591_;
v___y_5540_ = v___y_5588_;
v___y_5541_ = v___y_5589_;
v___y_5542_ = v___x_5597_;
goto v___jp_5538_;
}
}
else
{
size_t v___x_5598_; size_t v___x_5599_; lean_object* v___x_5600_; 
v___x_5598_ = ((size_t)0ULL);
v___x_5599_ = lean_usize_of_nat(v___x_5592_);
v___x_5600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5586_, v___x_5598_, v___x_5599_, v_pkgEntries_5590_);
lean_dec_ref(v_packages_5586_);
v___y_5539_ = v___x_5591_;
v___y_5540_ = v___y_5588_;
v___y_5541_ = v___y_5589_;
v___y_5542_ = v___x_5600_;
goto v___jp_5538_;
}
}
}
v___jp_5601_:
{
if (lean_obj_tag(v_packagesDir_x3f_5585_) == 0)
{
lean_object* v_packages_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v_config_5606_; lean_object* v_toWorkspaceConfig_5607_; lean_object* v___x_5608_; 
v_packages_5603_ = lean_ctor_get(v_ws_5483_, 4);
v___x_5604_ = lean_unsigned_to_nat(0u);
v___x_5605_ = lean_array_fget_borrowed(v_packages_5603_, v___x_5604_);
v_config_5606_ = lean_ctor_get(v___x_5605_, 6);
v_toWorkspaceConfig_5607_ = lean_ctor_get(v_config_5606_, 0);
lean_inc_ref(v_toWorkspaceConfig_5607_);
v___x_5608_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5607_);
v___y_5588_ = v___y_5602_;
v___y_5589_ = v___x_5608_;
goto v___jp_5587_;
}
else
{
lean_object* v_val_5609_; 
v_val_5609_ = lean_ctor_get(v_packagesDir_x3f_5585_, 0);
lean_inc(v_val_5609_);
lean_dec_ref_known(v_packagesDir_x3f_5585_, 1);
v___y_5588_ = v___y_5602_;
v___y_5589_ = v_val_5609_;
goto v___jp_5587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5623_, lean_object* v_manifest_5624_, lean_object* v_leanOpts_5625_, lean_object* v_reconfigure_5626_, lean_object* v_overrides_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_){
_start:
{
uint8_t v_reconfigure_boxed_5630_; lean_object* v_res_5631_; 
v_reconfigure_boxed_5630_ = lean_unbox(v_reconfigure_5626_);
v_res_5631_ = l_Lake_Workspace_materializeDeps(v_ws_5623_, v_manifest_5624_, v_leanOpts_5625_, v_reconfigure_boxed_5630_, v_overrides_5627_, v_a_5628_);
lean_dec_ref(v_a_5628_);
lean_dec_ref(v_overrides_5627_);
return v_res_5631_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v_leanOpts_5634_, uint8_t v_reconfigure_5635_, lean_object* v_ws_5636_, lean_object* v_i_5637_, lean_object* v_i__lt_5638_, lean_object* v_next_5639_, lean_object* v_lt__next_5640_, lean_object* v___y_5641_){
_start:
{
lean_object* v___x_5643_; 
v___x_5643_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5632_, v___y_5633_, v_leanOpts_5634_, v_reconfigure_5635_, v_ws_5636_, v_i_5637_, v_next_5639_, v___y_5641_);
return v___x_5643_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v_leanOpts_5646_, lean_object* v_reconfigure_5647_, lean_object* v_ws_5648_, lean_object* v_i_5649_, lean_object* v_i__lt_5650_, lean_object* v_next_5651_, lean_object* v_lt__next_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_){
_start:
{
uint8_t v_reconfigure_boxed_5655_; lean_object* v_res_5656_; 
v_reconfigure_boxed_5655_ = lean_unbox(v_reconfigure_5647_);
v_res_5656_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5644_, v___y_5645_, v_leanOpts_5646_, v_reconfigure_boxed_5655_, v_ws_5648_, v_i_5649_, v_i__lt_5650_, v_next_5651_, v_lt__next_5652_, v___y_5653_);
lean_dec_ref(v___y_5653_);
lean_dec(v___y_5644_);
return v_res_5656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(lean_object* v_start_5657_, lean_object* v_pkg_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v_leanOpts_5661_, uint8_t v_reconfigure_5662_, lean_object* v_as_5663_, size_t v_i_5664_, size_t v_stop_5665_, lean_object* v_b_5666_, lean_object* v___y_5667_){
_start:
{
lean_object* v___x_5669_; 
v___x_5669_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5658_, v___y_5659_, v___y_5660_, v_leanOpts_5661_, v_reconfigure_5662_, v_as_5663_, v_i_5664_, v_stop_5665_, v_b_5666_, v___y_5667_);
return v___x_5669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_start_5670_, lean_object* v_pkg_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v_leanOpts_5674_, lean_object* v_reconfigure_5675_, lean_object* v_as_5676_, lean_object* v_i_5677_, lean_object* v_stop_5678_, lean_object* v_b_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_){
_start:
{
uint8_t v_reconfigure_boxed_5682_; size_t v_i_boxed_5683_; size_t v_stop_boxed_5684_; lean_object* v_res_5685_; 
v_reconfigure_boxed_5682_ = lean_unbox(v_reconfigure_5675_);
v_i_boxed_5683_ = lean_unbox_usize(v_i_5677_);
lean_dec(v_i_5677_);
v_stop_boxed_5684_ = lean_unbox_usize(v_stop_5678_);
lean_dec(v_stop_5678_);
v_res_5685_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(v_start_5670_, v_pkg_5671_, v___y_5672_, v___y_5673_, v_leanOpts_5674_, v_reconfigure_boxed_5682_, v_as_5676_, v_i_boxed_5683_, v_stop_boxed_5684_, v_b_5679_, v___y_5680_);
lean_dec_ref(v___y_5680_);
lean_dec_ref(v_as_5676_);
lean_dec(v___y_5672_);
lean_dec(v_start_5670_);
return v_res_5685_;
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

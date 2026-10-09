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
lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(lean_object* v_ws_3_, lean_object* v_dep_4_, lean_object* v_lakeOpts_5_, lean_object* v_leanOpts_6_, uint8_t v_reconfigure_7_){
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
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_3_ = stack[0].m_obj;
lean_object* v_dep_4_ = stack[1].m_obj;
lean_object* v_lakeOpts_5_ = stack[2].m_obj;
lean_object* v_leanOpts_6_ = stack[3].m_obj;
uint8_t v_reconfigure_7_ = stack[4].m_num;
lean_object* v_res_32_;
v_res_32_ = l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(v_ws_3_, v_dep_4_, v_lakeOpts_5_, v_leanOpts_6_, v_reconfigure_7_);
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___boxed(lean_object* v_ws_33_, lean_object* v_dep_34_, lean_object* v_lakeOpts_35_, lean_object* v_leanOpts_36_, lean_object* v_reconfigure_37_){
_start:
{
uint8_t v_reconfigure_boxed_38_; lean_object* v_res_39_; 
v_reconfigure_boxed_38_ = lean_unbox(v_reconfigure_37_);
v_res_39_ = l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(v_ws_33_, v_dep_34_, v_lakeOpts_35_, v_leanOpts_36_, v_reconfigure_boxed_38_);
lean_dec_ref(v_ws_33_);
return v_res_39_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(lean_object* v_as_40_, size_t v_i_41_, size_t v_stop_42_, lean_object* v_b_43_){
_start:
{
uint8_t v___x_44_; 
v___x_44_ = lean_usize_dec_eq(v_i_41_, v_stop_42_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v_name_46_; lean_object* v_config_47_; lean_object* v_lakeEnv_48_; lean_object* v_lakeConfig_49_; lean_object* v_lakeCache_50_; lean_object* v_lakeArgs_x3f_51_; lean_object* v_packages_52_; lean_object* v_packageMap_53_; lean_object* v_facetConfigs_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_65_; 
v___x_45_ = lean_array_uget_borrowed(v_as_40_, v_i_41_);
v_name_46_ = lean_ctor_get(v___x_45_, 0);
v_config_47_ = lean_ctor_get(v___x_45_, 1);
v_lakeEnv_48_ = lean_ctor_get(v_b_43_, 0);
v_lakeConfig_49_ = lean_ctor_get(v_b_43_, 1);
v_lakeCache_50_ = lean_ctor_get(v_b_43_, 2);
v_lakeArgs_x3f_51_ = lean_ctor_get(v_b_43_, 3);
v_packages_52_ = lean_ctor_get(v_b_43_, 4);
v_packageMap_53_ = lean_ctor_get(v_b_43_, 5);
v_facetConfigs_54_ = lean_ctor_get(v_b_43_, 6);
v_isSharedCheck_65_ = !lean_is_exclusive(v_b_43_);
if (v_isSharedCheck_65_ == 0)
{
v___x_56_ = v_b_43_;
v_isShared_57_ = v_isSharedCheck_65_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_facetConfigs_54_);
lean_inc(v_packageMap_53_);
lean_inc(v_packages_52_);
lean_inc(v_lakeArgs_x3f_51_);
lean_inc(v_lakeCache_50_);
lean_inc(v_lakeConfig_49_);
lean_inc(v_lakeEnv_48_);
lean_dec(v_b_43_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_65_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
lean_inc(v_config_47_);
lean_inc(v_name_46_);
v___x_58_ = l_Lake_FacetConfigMap_insert(v_name_46_, v_config_47_, v_facetConfigs_54_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 6, v___x_58_);
v___x_60_ = v___x_56_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_lakeEnv_48_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_lakeConfig_49_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_lakeCache_50_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v_lakeArgs_x3f_51_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v_packages_52_);
lean_ctor_set(v_reuseFailAlloc_64_, 5, v_packageMap_53_);
lean_ctor_set(v_reuseFailAlloc_64_, 6, v___x_58_);
v___x_60_ = v_reuseFailAlloc_64_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
size_t v___x_61_; size_t v___x_62_; 
v___x_61_ = ((size_t)1ULL);
v___x_62_ = lean_usize_add(v_i_41_, v___x_61_);
v_i_41_ = v___x_62_;
v_b_43_ = v___x_60_;
goto _start;
}
}
}
else
{
return v_b_43_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_40_ = stack[0].m_obj;
size_t v_i_41_ = stack[1].m_num;
size_t v_stop_42_ = stack[2].m_num;
lean_object* v_b_43_ = stack[3].m_obj;
lean_object* v_res_66_;
v_res_66_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_as_40_, v_i_41_, v_stop_42_, v_b_43_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0___boxed(lean_object* v_as_67_, lean_object* v_i_68_, lean_object* v_stop_69_, lean_object* v_b_70_){
_start:
{
size_t v_i_boxed_71_; size_t v_stop_boxed_72_; lean_object* v_res_73_; 
v_i_boxed_71_ = lean_unbox_usize(v_i_68_);
lean_dec(v_i_68_);
v_stop_boxed_72_ = lean_unbox_usize(v_stop_69_);
lean_dec(v_stop_69_);
v_res_73_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_as_67_, v_i_boxed_71_, v_stop_boxed_72_, v_b_70_);
lean_dec_ref(v_as_67_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(lean_object* v_decls_74_, lean_object* v_self_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_array_get_size(v_decls_74_);
v___x_78_ = lean_nat_dec_lt(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
return v_self_75_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = lean_nat_dec_le(v___x_77_, v___x_77_);
if (v___x_79_ == 0)
{
if (v___x_78_ == 0)
{
return v_self_75_;
}
else
{
size_t v___x_80_; size_t v___x_81_; lean_object* v___x_82_; 
v___x_80_ = ((size_t)0ULL);
v___x_81_ = lean_usize_of_nat(v___x_77_);
v___x_82_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_decls_74_, v___x_80_, v___x_81_, v_self_75_);
return v___x_82_;
}
}
else
{
size_t v___x_83_; size_t v___x_84_; lean_object* v___x_85_; 
v___x_83_ = ((size_t)0ULL);
v___x_84_ = lean_usize_of_nat(v___x_77_);
v___x_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(v_decls_74_, v___x_83_, v___x_84_, v_self_75_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls___boxed(lean_object* v_decls_86_, lean_object* v_self_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(v_decls_86_, v_self_87_);
lean_dec_ref(v_decls_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(lean_object* v_k_89_, lean_object* v_v_90_, lean_object* v_t_91_){
_start:
{
if (lean_obj_tag(v_t_91_) == 0)
{
lean_object* v_size_92_; lean_object* v_k_93_; lean_object* v_v_94_; lean_object* v_l_95_; lean_object* v_r_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_376_; 
v_size_92_ = lean_ctor_get(v_t_91_, 0);
v_k_93_ = lean_ctor_get(v_t_91_, 1);
v_v_94_ = lean_ctor_get(v_t_91_, 2);
v_l_95_ = lean_ctor_get(v_t_91_, 3);
v_r_96_ = lean_ctor_get(v_t_91_, 4);
v_isSharedCheck_376_ = !lean_is_exclusive(v_t_91_);
if (v_isSharedCheck_376_ == 0)
{
v___x_98_ = v_t_91_;
v_isShared_99_ = v_isSharedCheck_376_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_r_96_);
lean_inc(v_l_95_);
lean_inc(v_v_94_);
lean_inc(v_k_93_);
lean_inc(v_size_92_);
lean_dec(v_t_91_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_376_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
uint8_t v___x_100_; 
v___x_100_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_89_, v_k_93_);
switch(v___x_100_)
{
case 0:
{
lean_object* v_impl_101_; lean_object* v___x_102_; 
lean_dec(v_size_92_);
v_impl_101_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_89_, v_v_90_, v_l_95_);
v___x_102_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_96_) == 0)
{
lean_object* v_size_103_; lean_object* v_size_104_; lean_object* v_k_105_; lean_object* v_v_106_; lean_object* v_l_107_; lean_object* v_r_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_size_103_ = lean_ctor_get(v_r_96_, 0);
v_size_104_ = lean_ctor_get(v_impl_101_, 0);
v_k_105_ = lean_ctor_get(v_impl_101_, 1);
v_v_106_ = lean_ctor_get(v_impl_101_, 2);
v_l_107_ = lean_ctor_get(v_impl_101_, 3);
v_r_108_ = lean_ctor_get(v_impl_101_, 4);
lean_inc(v_r_108_);
v___x_109_ = lean_unsigned_to_nat(3u);
v___x_110_ = lean_nat_mul(v___x_109_, v_size_103_);
v___x_111_ = lean_nat_dec_lt(v___x_110_, v_size_104_);
lean_dec(v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
lean_dec(v_r_108_);
v___x_112_ = lean_nat_add(v___x_102_, v_size_104_);
v___x_113_ = lean_nat_add(v___x_112_, v_size_103_);
lean_dec(v___x_112_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 3, v_impl_101_);
lean_ctor_set(v___x_98_, 0, v___x_113_);
v___x_115_ = v___x_98_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_impl_101_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v_r_96_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
else
{
lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_182_; 
lean_inc(v_l_107_);
lean_inc(v_v_106_);
lean_inc(v_k_105_);
lean_inc(v_size_104_);
v_isSharedCheck_182_ = !lean_is_exclusive(v_impl_101_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; lean_object* v_unused_184_; lean_object* v_unused_185_; lean_object* v_unused_186_; lean_object* v_unused_187_; 
v_unused_183_ = lean_ctor_get(v_impl_101_, 4);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_impl_101_, 3);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_impl_101_, 2);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_impl_101_, 1);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_impl_101_, 0);
lean_dec(v_unused_187_);
v___x_118_ = v_impl_101_;
v_isShared_119_ = v_isSharedCheck_182_;
goto v_resetjp_117_;
}
else
{
lean_dec(v_impl_101_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_182_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_size_120_; lean_object* v_size_121_; lean_object* v_k_122_; lean_object* v_v_123_; lean_object* v_l_124_; lean_object* v_r_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_size_120_ = lean_ctor_get(v_l_107_, 0);
v_size_121_ = lean_ctor_get(v_r_108_, 0);
v_k_122_ = lean_ctor_get(v_r_108_, 1);
v_v_123_ = lean_ctor_get(v_r_108_, 2);
v_l_124_ = lean_ctor_get(v_r_108_, 3);
v_r_125_ = lean_ctor_get(v_r_108_, 4);
v___x_126_ = lean_unsigned_to_nat(2u);
v___x_127_ = lean_nat_mul(v___x_126_, v_size_120_);
v___x_128_ = lean_nat_dec_lt(v_size_121_, v___x_127_);
lean_dec(v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_157_; 
lean_inc(v_r_125_);
lean_inc(v_l_124_);
lean_inc(v_v_123_);
lean_inc(v_k_122_);
v_isSharedCheck_157_ = !lean_is_exclusive(v_r_108_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; lean_object* v_unused_159_; lean_object* v_unused_160_; lean_object* v_unused_161_; lean_object* v_unused_162_; 
v_unused_158_ = lean_ctor_get(v_r_108_, 4);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_r_108_, 3);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_r_108_, 2);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_r_108_, 1);
lean_dec(v_unused_161_);
v_unused_162_ = lean_ctor_get(v_r_108_, 0);
lean_dec(v_unused_162_);
v___x_130_ = v_r_108_;
v_isShared_131_ = v_isSharedCheck_157_;
goto v_resetjp_129_;
}
else
{
lean_dec(v_r_108_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_157_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; lean_object* v___x_145_; lean_object* v___y_147_; 
v___x_132_ = lean_nat_add(v___x_102_, v_size_104_);
lean_dec(v_size_104_);
v___x_133_ = lean_nat_add(v___x_132_, v_size_103_);
lean_dec(v___x_132_);
v___x_145_ = lean_nat_add(v___x_102_, v_size_120_);
if (lean_obj_tag(v_l_124_) == 0)
{
lean_object* v_size_155_; 
v_size_155_ = lean_ctor_get(v_l_124_, 0);
lean_inc(v_size_155_);
v___y_147_ = v_size_155_;
goto v___jp_146_;
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___y_147_ = v___x_156_;
goto v___jp_146_;
}
v___jp_134_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_nat_add(v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec(v___y_136_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 4, v_r_96_);
lean_ctor_set(v___x_130_, 3, v_r_125_);
lean_ctor_set(v___x_130_, 2, v_v_94_);
lean_ctor_set(v___x_130_, 1, v_k_93_);
lean_ctor_set(v___x_130_, 0, v___x_138_);
v___x_140_ = v___x_130_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v_r_125_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v_r_96_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 4, v___x_140_);
lean_ctor_set(v___x_118_, 3, v___y_135_);
lean_ctor_set(v___x_118_, 2, v_v_123_);
lean_ctor_set(v___x_118_, 1, v_k_122_);
lean_ctor_set(v___x_118_, 0, v___x_133_);
v___x_142_ = v___x_118_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v___y_135_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_nat_add(v___x_145_, v___y_147_);
lean_dec(v___y_147_);
lean_dec(v___x_145_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v_l_124_);
lean_ctor_set(v___x_98_, 3, v_l_107_);
lean_ctor_set(v___x_98_, 2, v_v_106_);
lean_ctor_set(v___x_98_, 1, v_k_105_);
lean_ctor_set(v___x_98_, 0, v___x_148_);
v___x_150_ = v___x_98_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_k_105_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_v_106_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_l_107_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v_l_124_);
v___x_150_ = v_reuseFailAlloc_154_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = lean_nat_add(v___x_102_, v_size_103_);
if (lean_obj_tag(v_r_125_) == 0)
{
lean_object* v_size_152_; 
v_size_152_ = lean_ctor_get(v_r_125_, 0);
lean_inc(v_size_152_);
v___y_135_ = v___x_150_;
v___y_136_ = v___x_151_;
v___y_137_ = v_size_152_;
goto v___jp_134_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___y_135_ = v___x_150_;
v___y_136_ = v___x_151_;
v___y_137_ = v___x_153_;
goto v___jp_134_;
}
}
}
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
lean_del_object(v___x_98_);
v___x_163_ = lean_nat_add(v___x_102_, v_size_104_);
lean_dec(v_size_104_);
v___x_164_ = lean_nat_add(v___x_163_, v_size_103_);
lean_dec(v___x_163_);
v___x_165_ = lean_nat_add(v___x_102_, v_size_103_);
v___x_166_ = lean_nat_add(v___x_165_, v_size_121_);
lean_dec(v___x_165_);
lean_inc_ref(v_r_96_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 4, v_r_96_);
lean_ctor_set(v___x_118_, 3, v_r_108_);
lean_ctor_set(v___x_118_, 2, v_v_94_);
lean_ctor_set(v___x_118_, 1, v_k_93_);
lean_ctor_set(v___x_118_, 0, v___x_166_);
v___x_168_ = v___x_118_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v_r_108_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v_r_96_);
v___x_168_ = v_reuseFailAlloc_181_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
v_isSharedCheck_175_ = !lean_is_exclusive(v_r_96_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; lean_object* v_unused_177_; lean_object* v_unused_178_; lean_object* v_unused_179_; lean_object* v_unused_180_; 
v_unused_176_ = lean_ctor_get(v_r_96_, 4);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_r_96_, 3);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_r_96_, 2);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_r_96_, 1);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_r_96_, 0);
lean_dec(v_unused_180_);
v___x_170_ = v_r_96_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_dec(v_r_96_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v___x_168_);
lean_ctor_set(v___x_170_, 3, v_l_107_);
lean_ctor_set(v___x_170_, 2, v_v_106_);
lean_ctor_set(v___x_170_, 1, v_k_105_);
lean_ctor_set(v___x_170_, 0, v___x_164_);
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_k_105_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_v_106_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v_l_107_);
lean_ctor_set(v_reuseFailAlloc_174_, 4, v___x_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_188_; 
v_l_188_ = lean_ctor_get(v_impl_101_, 3);
if (lean_obj_tag(v_l_188_) == 0)
{
lean_object* v_r_189_; lean_object* v_k_190_; lean_object* v_v_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_202_; 
lean_inc_ref(v_l_188_);
v_r_189_ = lean_ctor_get(v_impl_101_, 4);
v_k_190_ = lean_ctor_get(v_impl_101_, 1);
v_v_191_ = lean_ctor_get(v_impl_101_, 2);
v_isSharedCheck_202_ = !lean_is_exclusive(v_impl_101_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_203_ = lean_ctor_get(v_impl_101_, 3);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_impl_101_, 0);
lean_dec(v_unused_204_);
v___x_193_ = v_impl_101_;
v_isShared_194_ = v_isSharedCheck_202_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_r_189_);
lean_inc(v_v_191_);
lean_inc(v_k_190_);
lean_dec(v_impl_101_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_202_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_189_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 3, v_r_189_);
lean_ctor_set(v___x_193_, 2, v_v_94_);
lean_ctor_set(v___x_193_, 1, v_k_93_);
lean_ctor_set(v___x_193_, 0, v___x_102_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_r_189_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_r_189_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v___x_197_);
lean_ctor_set(v___x_98_, 3, v_l_188_);
lean_ctor_set(v___x_98_, 2, v_v_191_);
lean_ctor_set(v___x_98_, 1, v_k_190_);
lean_ctor_set(v___x_98_, 0, v___x_195_);
v___x_199_ = v___x_98_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_k_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_v_191_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_r_205_; 
v_r_205_ = lean_ctor_get(v_impl_101_, 4);
lean_inc(v_r_205_);
if (lean_obj_tag(v_r_205_) == 0)
{
lean_object* v_k_206_; lean_object* v_v_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_230_; 
lean_inc(v_l_188_);
v_k_206_ = lean_ctor_get(v_impl_101_, 1);
v_v_207_ = lean_ctor_get(v_impl_101_, 2);
v_isSharedCheck_230_ = !lean_is_exclusive(v_impl_101_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_231_ = lean_ctor_get(v_impl_101_, 4);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_impl_101_, 3);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_impl_101_, 0);
lean_dec(v_unused_233_);
v___x_209_ = v_impl_101_;
v_isShared_210_ = v_isSharedCheck_230_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_v_207_);
lean_inc(v_k_206_);
lean_dec(v_impl_101_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_230_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_k_211_; lean_object* v_v_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_226_; 
v_k_211_ = lean_ctor_get(v_r_205_, 1);
v_v_212_ = lean_ctor_get(v_r_205_, 2);
v_isSharedCheck_226_ = !lean_is_exclusive(v_r_205_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; lean_object* v_unused_228_; lean_object* v_unused_229_; 
v_unused_227_ = lean_ctor_get(v_r_205_, 4);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_r_205_, 3);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_r_205_, 0);
lean_dec(v_unused_229_);
v___x_214_ = v_r_205_;
v_isShared_215_ = v_isSharedCheck_226_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_v_212_);
lean_inc(v_k_211_);
lean_dec(v_r_205_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_226_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_unsigned_to_nat(3u);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 4, v_l_188_);
lean_ctor_set(v___x_214_, 3, v_l_188_);
lean_ctor_set(v___x_214_, 2, v_v_207_);
lean_ctor_set(v___x_214_, 1, v_k_206_);
lean_ctor_set(v___x_214_, 0, v___x_102_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_k_206_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_v_207_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v_l_188_);
v___x_218_ = v_reuseFailAlloc_225_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 4, v_l_188_);
lean_ctor_set(v___x_209_, 2, v_v_94_);
lean_ctor_set(v___x_209_, 1, v_k_93_);
lean_ctor_set(v___x_209_, 0, v___x_102_);
v___x_220_ = v___x_209_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_l_188_);
v___x_220_ = v_reuseFailAlloc_224_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v___x_220_);
lean_ctor_set(v___x_98_, 3, v___x_218_);
lean_ctor_set(v___x_98_, 2, v_v_212_);
lean_ctor_set(v___x_98_, 1, v_k_211_);
lean_ctor_set(v___x_98_, 0, v___x_216_);
v___x_222_ = v___x_98_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_k_211_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_v_212_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_223_, 4, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_unsigned_to_nat(2u);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v_r_205_);
lean_ctor_set(v___x_98_, 3, v_impl_101_);
lean_ctor_set(v___x_98_, 0, v___x_234_);
v___x_236_ = v___x_98_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_impl_101_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_r_205_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
case 1:
{
lean_object* v___x_239_; 
lean_dec(v_v_94_);
lean_dec(v_k_93_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 2, v_v_90_);
lean_ctor_set(v___x_98_, 1, v_k_89_);
v___x_239_ = v___x_98_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_size_92_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_k_89_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_v_90_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_l_95_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_r_96_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
default: 
{
lean_object* v_impl_241_; lean_object* v___x_242_; 
lean_dec(v_size_92_);
v_impl_241_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_89_, v_v_90_, v_r_96_);
v___x_242_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_95_) == 0)
{
lean_object* v_size_243_; lean_object* v_size_244_; lean_object* v_k_245_; lean_object* v_v_246_; lean_object* v_l_247_; lean_object* v_r_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_size_243_ = lean_ctor_get(v_l_95_, 0);
v_size_244_ = lean_ctor_get(v_impl_241_, 0);
v_k_245_ = lean_ctor_get(v_impl_241_, 1);
v_v_246_ = lean_ctor_get(v_impl_241_, 2);
v_l_247_ = lean_ctor_get(v_impl_241_, 3);
lean_inc(v_l_247_);
v_r_248_ = lean_ctor_get(v_impl_241_, 4);
v___x_249_ = lean_unsigned_to_nat(3u);
v___x_250_ = lean_nat_mul(v___x_249_, v_size_243_);
v___x_251_ = lean_nat_dec_lt(v___x_250_, v_size_244_);
lean_dec(v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec(v_l_247_);
v___x_252_ = lean_nat_add(v___x_242_, v_size_243_);
v___x_253_ = lean_nat_add(v___x_252_, v_size_244_);
lean_dec(v___x_252_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v_impl_241_);
lean_ctor_set(v___x_98_, 0, v___x_253_);
v___x_255_ = v___x_98_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_l_95_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_impl_241_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
else
{
lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_320_; 
lean_inc(v_r_248_);
lean_inc(v_v_246_);
lean_inc(v_k_245_);
lean_inc(v_size_244_);
v_isSharedCheck_320_ = !lean_is_exclusive(v_impl_241_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; lean_object* v_unused_324_; lean_object* v_unused_325_; 
v_unused_321_ = lean_ctor_get(v_impl_241_, 4);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_impl_241_, 3);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_impl_241_, 2);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_impl_241_, 1);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_impl_241_, 0);
lean_dec(v_unused_325_);
v___x_258_ = v_impl_241_;
v_isShared_259_ = v_isSharedCheck_320_;
goto v_resetjp_257_;
}
else
{
lean_dec(v_impl_241_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_320_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_size_260_; lean_object* v_k_261_; lean_object* v_v_262_; lean_object* v_l_263_; lean_object* v_r_264_; lean_object* v_size_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_size_260_ = lean_ctor_get(v_l_247_, 0);
v_k_261_ = lean_ctor_get(v_l_247_, 1);
v_v_262_ = lean_ctor_get(v_l_247_, 2);
v_l_263_ = lean_ctor_get(v_l_247_, 3);
v_r_264_ = lean_ctor_get(v_l_247_, 4);
v_size_265_ = lean_ctor_get(v_r_248_, 0);
v___x_266_ = lean_unsigned_to_nat(2u);
v___x_267_ = lean_nat_mul(v___x_266_, v_size_265_);
v___x_268_ = lean_nat_dec_lt(v_size_260_, v___x_267_);
lean_dec(v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_296_; 
lean_inc(v_r_264_);
lean_inc(v_l_263_);
lean_inc(v_v_262_);
lean_inc(v_k_261_);
v_isSharedCheck_296_ = !lean_is_exclusive(v_l_247_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; lean_object* v_unused_300_; lean_object* v_unused_301_; 
v_unused_297_ = lean_ctor_get(v_l_247_, 4);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_l_247_, 3);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_l_247_, 2);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_l_247_, 1);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_l_247_, 0);
lean_dec(v_unused_301_);
v___x_270_ = v_l_247_;
v_isShared_271_ = v_isSharedCheck_296_;
goto v_resetjp_269_;
}
else
{
lean_dec(v_l_247_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_296_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_286_; 
v___x_272_ = lean_nat_add(v___x_242_, v_size_243_);
v___x_273_ = lean_nat_add(v___x_272_, v_size_244_);
lean_dec(v_size_244_);
if (lean_obj_tag(v_l_263_) == 0)
{
lean_object* v_size_294_; 
v_size_294_ = lean_ctor_get(v_l_263_, 0);
lean_inc(v_size_294_);
v___y_286_ = v_size_294_;
goto v___jp_285_;
}
else
{
lean_object* v___x_295_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___y_286_ = v___x_295_;
goto v___jp_285_;
}
v___jp_274_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_nat_add(v___y_275_, v___y_277_);
lean_dec(v___y_277_);
lean_dec(v___y_275_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v_r_248_);
lean_ctor_set(v___x_270_, 3, v_r_264_);
lean_ctor_set(v___x_270_, 2, v_v_246_);
lean_ctor_set(v___x_270_, 1, v_k_245_);
lean_ctor_set(v___x_270_, 0, v___x_278_);
v___x_280_ = v___x_270_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_k_245_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_v_246_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_r_264_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v_r_248_);
v___x_280_ = v_reuseFailAlloc_284_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_282_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 4, v___x_280_);
lean_ctor_set(v___x_258_, 3, v___y_276_);
lean_ctor_set(v___x_258_, 2, v_v_262_);
lean_ctor_set(v___x_258_, 1, v_k_261_);
lean_ctor_set(v___x_258_, 0, v___x_273_);
v___x_282_ = v___x_258_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_k_261_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_v_262_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v___y_276_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = lean_nat_add(v___x_272_, v___y_286_);
lean_dec(v___y_286_);
lean_dec(v___x_272_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v_l_263_);
lean_ctor_set(v___x_98_, 0, v___x_287_);
v___x_289_ = v___x_98_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_l_95_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_l_263_);
v___x_289_ = v_reuseFailAlloc_293_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = lean_nat_add(v___x_242_, v_size_265_);
if (lean_obj_tag(v_r_264_) == 0)
{
lean_object* v_size_291_; 
v_size_291_ = lean_ctor_get(v_r_264_, 0);
lean_inc(v_size_291_);
v___y_275_ = v___x_290_;
v___y_276_ = v___x_289_;
v___y_277_ = v_size_291_;
goto v___jp_274_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___y_275_ = v___x_290_;
v___y_276_ = v___x_289_;
v___y_277_ = v___x_292_;
goto v___jp_274_;
}
}
}
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
lean_del_object(v___x_98_);
v___x_302_ = lean_nat_add(v___x_242_, v_size_243_);
v___x_303_ = lean_nat_add(v___x_302_, v_size_244_);
lean_dec(v_size_244_);
v___x_304_ = lean_nat_add(v___x_302_, v_size_260_);
lean_dec(v___x_302_);
lean_inc_ref(v_l_95_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 4, v_l_247_);
lean_ctor_set(v___x_258_, 3, v_l_95_);
lean_ctor_set(v___x_258_, 2, v_v_94_);
lean_ctor_set(v___x_258_, 1, v_k_93_);
lean_ctor_set(v___x_258_, 0, v___x_304_);
v___x_306_ = v___x_258_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_l_95_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_l_247_);
v___x_306_ = v_reuseFailAlloc_319_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v_isSharedCheck_313_ = !lean_is_exclusive(v_l_95_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; 
v_unused_314_ = lean_ctor_get(v_l_95_, 4);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_l_95_, 3);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_l_95_, 2);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_l_95_, 1);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_l_95_, 0);
lean_dec(v_unused_318_);
v___x_308_ = v_l_95_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_dec(v_l_95_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 4, v_r_248_);
lean_ctor_set(v___x_308_, 3, v___x_306_);
lean_ctor_set(v___x_308_, 2, v_v_246_);
lean_ctor_set(v___x_308_, 1, v_k_245_);
lean_ctor_set(v___x_308_, 0, v___x_303_);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_k_245_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_v_246_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_r_248_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_326_; 
v_l_326_ = lean_ctor_get(v_impl_241_, 3);
lean_inc(v_l_326_);
if (lean_obj_tag(v_l_326_) == 0)
{
lean_object* v_r_327_; lean_object* v_k_328_; lean_object* v_v_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_352_; 
v_r_327_ = lean_ctor_get(v_impl_241_, 4);
v_k_328_ = lean_ctor_get(v_impl_241_, 1);
v_v_329_ = lean_ctor_get(v_impl_241_, 2);
v_isSharedCheck_352_ = !lean_is_exclusive(v_impl_241_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; lean_object* v_unused_354_; 
v_unused_353_ = lean_ctor_get(v_impl_241_, 3);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_impl_241_, 0);
lean_dec(v_unused_354_);
v___x_331_ = v_impl_241_;
v_isShared_332_ = v_isSharedCheck_352_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_r_327_);
lean_inc(v_v_329_);
lean_inc(v_k_328_);
lean_dec(v_impl_241_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_352_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_k_333_; lean_object* v_v_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_348_; 
v_k_333_ = lean_ctor_get(v_l_326_, 1);
v_v_334_ = lean_ctor_get(v_l_326_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v_l_326_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; lean_object* v_unused_350_; lean_object* v_unused_351_; 
v_unused_349_ = lean_ctor_get(v_l_326_, 4);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_l_326_, 3);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_l_326_, 0);
lean_dec(v_unused_351_);
v___x_336_ = v_l_326_;
v_isShared_337_ = v_isSharedCheck_348_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_v_334_);
lean_inc(v_k_333_);
lean_dec(v_l_326_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_348_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_327_, 2);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 4, v_r_327_);
lean_ctor_set(v___x_336_, 3, v_r_327_);
lean_ctor_set(v___x_336_, 2, v_v_94_);
lean_ctor_set(v___x_336_, 1, v_k_93_);
lean_ctor_set(v___x_336_, 0, v___x_242_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_r_327_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_r_327_);
v___x_340_ = v_reuseFailAlloc_347_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
lean_inc(v_r_327_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 3, v_r_327_);
lean_ctor_set(v___x_331_, 0, v___x_242_);
v___x_342_ = v___x_331_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_328_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_329_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_r_327_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_r_327_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v___x_342_);
lean_ctor_set(v___x_98_, 3, v___x_340_);
lean_ctor_set(v___x_98_, 2, v_v_334_);
lean_ctor_set(v___x_98_, 1, v_k_333_);
lean_ctor_set(v___x_98_, 0, v___x_338_);
v___x_344_ = v___x_98_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_k_333_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_v_334_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_345_, 4, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
else
{
lean_object* v_r_355_; 
v_r_355_ = lean_ctor_get(v_impl_241_, 4);
lean_inc(v_r_355_);
if (lean_obj_tag(v_r_355_) == 0)
{
lean_object* v_k_356_; lean_object* v_v_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_368_; 
v_k_356_ = lean_ctor_get(v_impl_241_, 1);
v_v_357_ = lean_ctor_get(v_impl_241_, 2);
v_isSharedCheck_368_ = !lean_is_exclusive(v_impl_241_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; lean_object* v_unused_371_; 
v_unused_369_ = lean_ctor_get(v_impl_241_, 4);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_impl_241_, 3);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_impl_241_, 0);
lean_dec(v_unused_371_);
v___x_359_ = v_impl_241_;
v_isShared_360_ = v_isSharedCheck_368_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_v_357_);
lean_inc(v_k_356_);
lean_dec(v_impl_241_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_368_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = lean_unsigned_to_nat(3u);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 4, v_l_326_);
lean_ctor_set(v___x_359_, 2, v_v_94_);
lean_ctor_set(v___x_359_, 1, v_k_93_);
lean_ctor_set(v___x_359_, 0, v___x_242_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_l_326_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v_l_326_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v_r_355_);
lean_ctor_set(v___x_98_, 3, v___x_363_);
lean_ctor_set(v___x_98_, 2, v_v_357_);
lean_ctor_set(v___x_98_, 1, v_k_356_);
lean_ctor_set(v___x_98_, 0, v___x_361_);
v___x_365_ = v___x_98_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_k_356_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_v_357_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_r_355_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
else
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_unsigned_to_nat(2u);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v_impl_241_);
lean_ctor_set(v___x_98_, 3, v_r_355_);
lean_ctor_set(v___x_98_, 0, v___x_372_);
v___x_374_ = v___x_98_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_k_93_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_v_94_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_r_355_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_impl_241_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
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
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v_k_89_);
lean_ctor_set(v___x_378_, 2, v_v_90_);
lean_ctor_set(v___x_378_, 3, v_t_91_);
lean_ctor_set(v___x_378_, 4, v_t_91_);
return v___x_378_;
}
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(lean_object* v_ws_379_, lean_object* v_dep_380_, lean_object* v_lakeOpts_381_, lean_object* v_leanOpts_382_, uint8_t v_reconfigure_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_lakeEnv_386_; lean_object* v_lakeConfig_387_; lean_object* v_lakeCache_388_; lean_object* v_lakeArgs_x3f_389_; lean_object* v_packages_390_; lean_object* v_packageMap_391_; lean_object* v_facetConfigs_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_459_; 
v_lakeEnv_386_ = lean_ctor_get(v_ws_379_, 0);
v_lakeConfig_387_ = lean_ctor_get(v_ws_379_, 1);
v_lakeCache_388_ = lean_ctor_get(v_ws_379_, 2);
v_lakeArgs_x3f_389_ = lean_ctor_get(v_ws_379_, 3);
v_packages_390_ = lean_ctor_get(v_ws_379_, 4);
v_packageMap_391_ = lean_ctor_get(v_ws_379_, 5);
v_facetConfigs_392_ = lean_ctor_get(v_ws_379_, 6);
v_isSharedCheck_459_ = !lean_is_exclusive(v_ws_379_);
if (v_isSharedCheck_459_ == 0)
{
v___x_394_ = v_ws_379_;
v_isShared_395_ = v_isSharedCheck_459_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_facetConfigs_392_);
lean_inc(v_packageMap_391_);
lean_inc(v_packages_390_);
lean_inc(v_lakeArgs_x3f_389_);
lean_inc(v_lakeCache_388_);
lean_inc(v_lakeConfig_387_);
lean_inc(v_lakeEnv_386_);
lean_dec(v_ws_379_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_459_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_manifestEntry_398_; lean_object* v_dir_399_; lean_object* v_pkgDir_400_; lean_object* v_relPkgDir_401_; lean_object* v_remoteUrl_402_; lean_object* v_name_403_; lean_object* v_scope_404_; lean_object* v_configFile_405_; lean_object* v_manifestFile_x3f_406_; lean_object* v_wsIdx_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___y_411_; 
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_array_fget_borrowed(v_packages_390_, v___x_396_);
v_manifestEntry_398_ = lean_ctor_get(v_dep_380_, 4);
lean_inc_ref(v_manifestEntry_398_);
v_dir_399_ = lean_ctor_get(v___x_397_, 4);
v_pkgDir_400_ = lean_ctor_get(v_dep_380_, 0);
lean_inc_ref_n(v_pkgDir_400_, 2);
v_relPkgDir_401_ = lean_ctor_get(v_dep_380_, 1);
lean_inc_ref(v_relPkgDir_401_);
v_remoteUrl_402_ = lean_ctor_get(v_dep_380_, 2);
lean_inc_ref(v_remoteUrl_402_);
lean_dec_ref(v_dep_380_);
v_name_403_ = lean_ctor_get(v_manifestEntry_398_, 0);
lean_inc(v_name_403_);
v_scope_404_ = lean_ctor_get(v_manifestEntry_398_, 1);
lean_inc_ref(v_scope_404_);
v_configFile_405_ = lean_ctor_get(v_manifestEntry_398_, 2);
lean_inc_ref_n(v_configFile_405_, 2);
v_manifestFile_x3f_406_ = lean_ctor_get(v_manifestEntry_398_, 3);
lean_inc(v_manifestFile_x3f_406_);
lean_dec_ref(v_manifestEntry_398_);
v_wsIdx_407_ = lean_array_get_size(v_packages_390_);
v___x_408_ = lean_box(0);
v___x_409_ = l_Lake_joinRelative(v_pkgDir_400_, v_configFile_405_);
if (lean_obj_tag(v_manifestFile_x3f_406_) == 0)
{
lean_object* v___x_457_; 
v___x_457_ = l_Lake_defaultManifestFile;
v___y_411_ = v___x_457_;
goto v___jp_410_;
}
else
{
lean_object* v_val_458_; 
v_val_458_ = lean_ctor_get(v_manifestFile_x3f_406_, 0);
lean_inc(v_val_458_);
lean_dec_ref_known(v_manifestFile_x3f_406_, 1);
v___y_411_ = v_val_458_;
goto v___jp_410_;
}
v___jp_410_:
{
lean_object* v___x_412_; uint8_t v___x_413_; uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_412_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_413_ = 0;
v___x_414_ = 1;
lean_inc(v_name_403_);
lean_inc_ref(v_dir_399_);
lean_inc_ref(v_lakeEnv_386_);
v___x_415_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_415_, 0, v_lakeEnv_386_);
lean_ctor_set(v___x_415_, 1, v___x_408_);
lean_ctor_set(v___x_415_, 2, v_dir_399_);
lean_ctor_set(v___x_415_, 3, v_wsIdx_407_);
lean_ctor_set(v___x_415_, 4, v_name_403_);
lean_ctor_set(v___x_415_, 5, v_relPkgDir_401_);
lean_ctor_set(v___x_415_, 6, v_pkgDir_400_);
lean_ctor_set(v___x_415_, 7, v_configFile_405_);
lean_ctor_set(v___x_415_, 8, v___x_409_);
lean_ctor_set(v___x_415_, 9, v___x_408_);
lean_ctor_set(v___x_415_, 10, v___y_411_);
lean_ctor_set(v___x_415_, 11, v___x_412_);
lean_ctor_set(v___x_415_, 12, v_lakeOpts_381_);
lean_ctor_set(v___x_415_, 13, v_leanOpts_382_);
lean_ctor_set(v___x_415_, 14, v_scope_404_);
lean_ctor_set(v___x_415_, 15, v_remoteUrl_402_);
lean_ctor_set_uint8(v___x_415_, sizeof(void*)*16, v_reconfigure_383_);
lean_ctor_set_uint8(v___x_415_, sizeof(void*)*16 + 1, v___x_413_);
lean_ctor_set_uint8(v___x_415_, sizeof(void*)*16 + 2, v___x_414_);
v___x_416_ = l_Lean_Name_toString(v_name_403_, v___x_413_);
v___x_417_ = l_Lake_resolveConfigFile(v___x_416_, v___x_415_, v_a_384_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v_a_419_; lean_object* v___x_420_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc_n(v_a_418_, 2);
v_a_419_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_417_, 2);
v___x_420_ = l_Lake_loadConfigFile___redArg(v_a_418_, v_a_419_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_438_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_a_422_ = lean_ctor_get(v___x_420_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_438_ == 0)
{
v___x_424_ = v___x_420_;
v_isShared_425_ = v_isSharedCheck_438_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_438_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_facetDecls_426_; lean_object* v___x_427_; lean_object* v_keyName_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v_facetDecls_426_ = lean_ctor_get(v_a_421_, 2);
lean_inc_ref(v_facetDecls_426_);
v___x_427_ = l_Lake_mkPackage(v_a_418_, v_a_421_, v_wsIdx_407_);
lean_dec(v_a_418_);
v_keyName_428_ = lean_ctor_get(v___x_427_, 2);
lean_inc(v_keyName_428_);
lean_inc_ref(v___x_427_);
v___x_429_ = lean_array_push(v_packages_390_, v___x_427_);
v___x_430_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_428_, v___x_427_, v_packageMap_391_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 5, v___x_430_);
lean_ctor_set(v___x_394_, 4, v___x_429_);
v___x_432_ = v___x_394_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_lakeEnv_386_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_lakeConfig_387_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_lakeCache_388_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_lakeArgs_x3f_389_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_437_, 5, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_437_, 6, v_facetConfigs_392_);
v___x_432_ = v_reuseFailAlloc_437_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(v_facetDecls_426_, v___x_432_);
lean_dec_ref(v_facetDecls_426_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_433_);
v___x_435_ = v___x_424_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_a_422_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
lean_object* v_a_439_; lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec(v_a_418_);
lean_del_object(v___x_394_);
lean_dec(v_facetConfigs_392_);
lean_dec(v_packageMap_391_);
lean_dec_ref(v_packages_390_);
lean_dec(v_lakeArgs_x3f_389_);
lean_dec_ref(v_lakeCache_388_);
lean_dec_ref(v_lakeConfig_387_);
lean_dec_ref(v_lakeEnv_386_);
v_a_439_ = lean_ctor_get(v___x_420_, 0);
v_a_440_ = lean_ctor_get(v___x_420_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_420_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_inc(v_a_439_);
lean_dec(v___x_420_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_439_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
lean_object* v_a_448_; lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_del_object(v___x_394_);
lean_dec(v_facetConfigs_392_);
lean_dec(v_packageMap_391_);
lean_dec_ref(v_packages_390_);
lean_dec(v_lakeArgs_x3f_389_);
lean_dec_ref(v_lakeCache_388_);
lean_dec_ref(v_lakeConfig_387_);
lean_dec_ref(v_lakeEnv_386_);
v_a_448_ = lean_ctor_get(v___x_417_, 0);
v_a_449_ = lean_ctor_get(v___x_417_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_417_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_inc(v_a_448_);
lean_dec(v___x_417_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_448_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_379_ = stack[0].m_obj;
lean_object* v_dep_380_ = stack[1].m_obj;
lean_object* v_lakeOpts_381_ = stack[2].m_obj;
lean_object* v_leanOpts_382_ = stack[3].m_obj;
uint8_t v_reconfigure_383_ = stack[4].m_num;
lean_object* v_a_384_ = stack[5].m_obj;
lean_object* v_res_460_;
v_res_460_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_379_, v_dep_380_, v_lakeOpts_381_, v_leanOpts_382_, v_reconfigure_383_, v_a_384_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27___boxed(lean_object* v_ws_461_, lean_object* v_dep_462_, lean_object* v_lakeOpts_463_, lean_object* v_leanOpts_464_, lean_object* v_reconfigure_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
uint8_t v_reconfigure_boxed_468_; lean_object* v_res_469_; 
v_reconfigure_boxed_468_ = lean_unbox(v_reconfigure_465_);
v_res_469_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_461_, v_dep_462_, v_lakeOpts_463_, v_leanOpts_464_, v_reconfigure_boxed_468_, v_a_466_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0(lean_object* v_00_u03b2_470_, lean_object* v_k_471_, lean_object* v_v_472_, lean_object* v_t_473_, lean_object* v_hl_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_k_471_, v_v_472_, v_t_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(lean_object* v_self_476_, lean_object* v_pkg_477_, lean_object* v_depIdxs_478_){
_start:
{
lean_object* v_wsIdx_479_; lean_object* v_baseName_480_; lean_object* v_keyName_481_; lean_object* v_origName_482_; lean_object* v_dir_483_; lean_object* v_relDir_484_; lean_object* v_config_485_; lean_object* v_configFile_486_; lean_object* v_relConfigFile_487_; lean_object* v_relManifestFile_488_; lean_object* v_scope_489_; lean_object* v_remoteUrl_490_; lean_object* v_depConfigs_491_; lean_object* v_depPkgs_492_; lean_object* v_targetDecls_493_; lean_object* v_targetDeclMap_494_; lean_object* v_defaultTargets_495_; lean_object* v_scripts_496_; lean_object* v_defaultScripts_497_; lean_object* v_postUpdateHooks_498_; lean_object* v_buildArchive_499_; lean_object* v_testDriver_500_; lean_object* v_lintDriver_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_524_; 
v_wsIdx_479_ = lean_ctor_get(v_pkg_477_, 0);
v_baseName_480_ = lean_ctor_get(v_pkg_477_, 1);
v_keyName_481_ = lean_ctor_get(v_pkg_477_, 2);
v_origName_482_ = lean_ctor_get(v_pkg_477_, 3);
v_dir_483_ = lean_ctor_get(v_pkg_477_, 4);
v_relDir_484_ = lean_ctor_get(v_pkg_477_, 5);
v_config_485_ = lean_ctor_get(v_pkg_477_, 6);
v_configFile_486_ = lean_ctor_get(v_pkg_477_, 7);
v_relConfigFile_487_ = lean_ctor_get(v_pkg_477_, 8);
v_relManifestFile_488_ = lean_ctor_get(v_pkg_477_, 9);
v_scope_489_ = lean_ctor_get(v_pkg_477_, 10);
v_remoteUrl_490_ = lean_ctor_get(v_pkg_477_, 11);
v_depConfigs_491_ = lean_ctor_get(v_pkg_477_, 12);
v_depPkgs_492_ = lean_ctor_get(v_pkg_477_, 14);
v_targetDecls_493_ = lean_ctor_get(v_pkg_477_, 15);
v_targetDeclMap_494_ = lean_ctor_get(v_pkg_477_, 16);
v_defaultTargets_495_ = lean_ctor_get(v_pkg_477_, 17);
v_scripts_496_ = lean_ctor_get(v_pkg_477_, 18);
v_defaultScripts_497_ = lean_ctor_get(v_pkg_477_, 19);
v_postUpdateHooks_498_ = lean_ctor_get(v_pkg_477_, 20);
v_buildArchive_499_ = lean_ctor_get(v_pkg_477_, 21);
v_testDriver_500_ = lean_ctor_get(v_pkg_477_, 22);
v_lintDriver_501_ = lean_ctor_get(v_pkg_477_, 23);
v_isSharedCheck_524_ = !lean_is_exclusive(v_pkg_477_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v_pkg_477_, 13);
lean_dec(v_unused_525_);
v___x_503_ = v_pkg_477_;
v_isShared_504_ = v_isSharedCheck_524_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_lintDriver_501_);
lean_inc(v_testDriver_500_);
lean_inc(v_buildArchive_499_);
lean_inc(v_postUpdateHooks_498_);
lean_inc(v_defaultScripts_497_);
lean_inc(v_scripts_496_);
lean_inc(v_defaultTargets_495_);
lean_inc(v_targetDeclMap_494_);
lean_inc(v_targetDecls_493_);
lean_inc(v_depPkgs_492_);
lean_inc(v_depConfigs_491_);
lean_inc(v_remoteUrl_490_);
lean_inc(v_scope_489_);
lean_inc(v_relManifestFile_488_);
lean_inc(v_relConfigFile_487_);
lean_inc(v_configFile_486_);
lean_inc(v_config_485_);
lean_inc(v_relDir_484_);
lean_inc(v_dir_483_);
lean_inc(v_origName_482_);
lean_inc(v_keyName_481_);
lean_inc(v_baseName_480_);
lean_inc(v_wsIdx_479_);
lean_dec(v_pkg_477_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_524_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_lakeEnv_505_; lean_object* v_lakeConfig_506_; lean_object* v_lakeCache_507_; lean_object* v_lakeArgs_x3f_508_; lean_object* v_packages_509_; lean_object* v_packageMap_510_; lean_object* v_facetConfigs_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_523_; 
v_lakeEnv_505_ = lean_ctor_get(v_self_476_, 0);
v_lakeConfig_506_ = lean_ctor_get(v_self_476_, 1);
v_lakeCache_507_ = lean_ctor_get(v_self_476_, 2);
v_lakeArgs_x3f_508_ = lean_ctor_get(v_self_476_, 3);
v_packages_509_ = lean_ctor_get(v_self_476_, 4);
v_packageMap_510_ = lean_ctor_get(v_self_476_, 5);
v_facetConfigs_511_ = lean_ctor_get(v_self_476_, 6);
v_isSharedCheck_523_ = !lean_is_exclusive(v_self_476_);
if (v_isSharedCheck_523_ == 0)
{
v___x_513_ = v_self_476_;
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_facetConfigs_511_);
lean_inc(v_packageMap_510_);
lean_inc(v_packages_509_);
lean_inc(v_lakeArgs_x3f_508_);
lean_inc(v_lakeCache_507_);
lean_inc(v_lakeConfig_506_);
lean_inc(v_lakeEnv_505_);
lean_dec(v_self_476_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_pkg_516_; 
lean_inc(v_keyName_481_);
lean_inc(v_wsIdx_479_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 13, v_depIdxs_478_);
v_pkg_516_ = v___x_503_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_wsIdx_479_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_baseName_480_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_keyName_481_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_origName_482_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v_dir_483_);
lean_ctor_set(v_reuseFailAlloc_522_, 5, v_relDir_484_);
lean_ctor_set(v_reuseFailAlloc_522_, 6, v_config_485_);
lean_ctor_set(v_reuseFailAlloc_522_, 7, v_configFile_486_);
lean_ctor_set(v_reuseFailAlloc_522_, 8, v_relConfigFile_487_);
lean_ctor_set(v_reuseFailAlloc_522_, 9, v_relManifestFile_488_);
lean_ctor_set(v_reuseFailAlloc_522_, 10, v_scope_489_);
lean_ctor_set(v_reuseFailAlloc_522_, 11, v_remoteUrl_490_);
lean_ctor_set(v_reuseFailAlloc_522_, 12, v_depConfigs_491_);
lean_ctor_set(v_reuseFailAlloc_522_, 13, v_depIdxs_478_);
lean_ctor_set(v_reuseFailAlloc_522_, 14, v_depPkgs_492_);
lean_ctor_set(v_reuseFailAlloc_522_, 15, v_targetDecls_493_);
lean_ctor_set(v_reuseFailAlloc_522_, 16, v_targetDeclMap_494_);
lean_ctor_set(v_reuseFailAlloc_522_, 17, v_defaultTargets_495_);
lean_ctor_set(v_reuseFailAlloc_522_, 18, v_scripts_496_);
lean_ctor_set(v_reuseFailAlloc_522_, 19, v_defaultScripts_497_);
lean_ctor_set(v_reuseFailAlloc_522_, 20, v_postUpdateHooks_498_);
lean_ctor_set(v_reuseFailAlloc_522_, 21, v_buildArchive_499_);
lean_ctor_set(v_reuseFailAlloc_522_, 22, v_testDriver_500_);
lean_ctor_set(v_reuseFailAlloc_522_, 23, v_lintDriver_501_);
v_pkg_516_ = v_reuseFailAlloc_522_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
lean_inc_ref(v_pkg_516_);
v___x_517_ = lean_array_fset(v_packages_509_, v_wsIdx_479_, v_pkg_516_);
lean_dec(v_wsIdx_479_);
v___x_518_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_481_, v_pkg_516_, v_packageMap_510_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 5, v___x_518_);
lean_ctor_set(v___x_513_, 4, v___x_517_);
v___x_520_ = v___x_513_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_lakeEnv_505_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_lakeConfig_506_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_lakeCache_507_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_lakeArgs_x3f_508_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_521_, 5, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_521_, 6, v_facetConfigs_511_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs(lean_object* v_self_526_, lean_object* v_pkg_527_, lean_object* v_depIdxs_528_, lean_object* v_h__wsIdx_529_, lean_object* v_h__depIdxs_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_self_526_, v_pkg_527_, v_depIdxs_528_);
return v___x_531_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(lean_object* v_val_532_, size_t v_sz_533_, size_t v_i_534_, lean_object* v_bs_535_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = lean_usize_dec_lt(v_i_534_, v_sz_533_);
if (v___x_536_ == 0)
{
return v_bs_535_;
}
else
{
lean_object* v_v_537_; lean_object* v___x_538_; lean_object* v_bs_x27_539_; lean_object* v___x_540_; size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; 
v_v_537_ = lean_array_uget(v_bs_535_, v_i_534_);
v___x_538_ = lean_unsigned_to_nat(0u);
v_bs_x27_539_ = lean_array_uset(v_bs_535_, v_i_534_, v___x_538_);
v___x_540_ = lean_array_fget_borrowed(v_val_532_, v_v_537_);
lean_dec(v_v_537_);
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_add(v_i_534_, v___x_541_);
lean_inc(v___x_540_);
v___x_543_ = lean_array_uset(v_bs_x27_539_, v_i_534_, v___x_540_);
v_i_534_ = v___x_542_;
v_bs_535_ = v___x_543_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_532_ = stack[0].m_obj;
size_t v_sz_533_ = stack[1].m_num;
size_t v_i_534_ = stack[2].m_num;
lean_object* v_bs_535_ = stack[3].m_obj;
lean_object* v_res_545_;
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_val_532_, v_sz_533_, v_i_534_, v_bs_535_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0___boxed(lean_object* v_val_546_, lean_object* v_sz_547_, lean_object* v_i_548_, lean_object* v_bs_549_){
_start:
{
size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_sz_boxed_550_ = lean_unbox_usize(v_sz_547_);
lean_dec(v_sz_547_);
v_i_boxed_551_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_val_546_, v_sz_boxed_550_, v_i_boxed_551_, v_bs_549_);
lean_dec_ref(v_val_546_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
lean_object* v_zero_555_; uint8_t v_isZero_556_; 
v_zero_555_ = lean_unsigned_to_nat(0u);
v_isZero_556_ = lean_nat_dec_eq(v_x_553_, v_zero_555_);
if (v_isZero_556_ == 1)
{
lean_dec(v_x_553_);
return v_x_554_;
}
else
{
lean_object* v_one_557_; lean_object* v_n_558_; lean_object* v_pkg_559_; lean_object* v_wsIdx_560_; lean_object* v_baseName_561_; lean_object* v_keyName_562_; lean_object* v_origName_563_; lean_object* v_dir_564_; lean_object* v_relDir_565_; lean_object* v_config_566_; lean_object* v_configFile_567_; lean_object* v_relConfigFile_568_; lean_object* v_relManifestFile_569_; lean_object* v_scope_570_; lean_object* v_remoteUrl_571_; lean_object* v_depConfigs_572_; lean_object* v_depIdxs_573_; lean_object* v_targetDecls_574_; lean_object* v_targetDeclMap_575_; lean_object* v_defaultTargets_576_; lean_object* v_scripts_577_; lean_object* v_defaultScripts_578_; lean_object* v_postUpdateHooks_579_; lean_object* v_buildArchive_580_; lean_object* v_testDriver_581_; lean_object* v_lintDriver_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_594_; 
v_one_557_ = lean_unsigned_to_nat(1u);
v_n_558_ = lean_nat_sub(v_x_553_, v_one_557_);
lean_dec(v_x_553_);
v_pkg_559_ = lean_array_fget(v_x_554_, v_n_558_);
v_wsIdx_560_ = lean_ctor_get(v_pkg_559_, 0);
v_baseName_561_ = lean_ctor_get(v_pkg_559_, 1);
v_keyName_562_ = lean_ctor_get(v_pkg_559_, 2);
v_origName_563_ = lean_ctor_get(v_pkg_559_, 3);
v_dir_564_ = lean_ctor_get(v_pkg_559_, 4);
v_relDir_565_ = lean_ctor_get(v_pkg_559_, 5);
v_config_566_ = lean_ctor_get(v_pkg_559_, 6);
v_configFile_567_ = lean_ctor_get(v_pkg_559_, 7);
v_relConfigFile_568_ = lean_ctor_get(v_pkg_559_, 8);
v_relManifestFile_569_ = lean_ctor_get(v_pkg_559_, 9);
v_scope_570_ = lean_ctor_get(v_pkg_559_, 10);
v_remoteUrl_571_ = lean_ctor_get(v_pkg_559_, 11);
v_depConfigs_572_ = lean_ctor_get(v_pkg_559_, 12);
v_depIdxs_573_ = lean_ctor_get(v_pkg_559_, 13);
v_targetDecls_574_ = lean_ctor_get(v_pkg_559_, 15);
v_targetDeclMap_575_ = lean_ctor_get(v_pkg_559_, 16);
v_defaultTargets_576_ = lean_ctor_get(v_pkg_559_, 17);
v_scripts_577_ = lean_ctor_get(v_pkg_559_, 18);
v_defaultScripts_578_ = lean_ctor_get(v_pkg_559_, 19);
v_postUpdateHooks_579_ = lean_ctor_get(v_pkg_559_, 20);
v_buildArchive_580_ = lean_ctor_get(v_pkg_559_, 21);
v_testDriver_581_ = lean_ctor_get(v_pkg_559_, 22);
v_lintDriver_582_ = lean_ctor_get(v_pkg_559_, 23);
v_isSharedCheck_594_ = !lean_is_exclusive(v_pkg_559_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_pkg_559_, 14);
lean_dec(v_unused_595_);
v___x_584_ = v_pkg_559_;
v_isShared_585_ = v_isSharedCheck_594_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_lintDriver_582_);
lean_inc(v_testDriver_581_);
lean_inc(v_buildArchive_580_);
lean_inc(v_postUpdateHooks_579_);
lean_inc(v_defaultScripts_578_);
lean_inc(v_scripts_577_);
lean_inc(v_defaultTargets_576_);
lean_inc(v_targetDeclMap_575_);
lean_inc(v_targetDecls_574_);
lean_inc(v_depIdxs_573_);
lean_inc(v_depConfigs_572_);
lean_inc(v_remoteUrl_571_);
lean_inc(v_scope_570_);
lean_inc(v_relManifestFile_569_);
lean_inc(v_relConfigFile_568_);
lean_inc(v_configFile_567_);
lean_inc(v_config_566_);
lean_inc(v_relDir_565_);
lean_inc(v_dir_564_);
lean_inc(v_origName_563_);
lean_inc(v_keyName_562_);
lean_inc(v_baseName_561_);
lean_inc(v_wsIdx_560_);
lean_dec(v_pkg_559_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_594_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
size_t v_sz_586_; size_t v___x_587_; lean_object* v_depPkgs_588_; lean_object* v___x_590_; 
v_sz_586_ = lean_array_size(v_depIdxs_573_);
v___x_587_ = ((size_t)0ULL);
lean_inc_ref(v_depIdxs_573_);
v_depPkgs_588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_x_554_, v_sz_586_, v___x_587_, v_depIdxs_573_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 14, v_depPkgs_588_);
v___x_590_ = v___x_584_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_wsIdx_560_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_baseName_561_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_keyName_562_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_origName_563_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_dir_564_);
lean_ctor_set(v_reuseFailAlloc_593_, 5, v_relDir_565_);
lean_ctor_set(v_reuseFailAlloc_593_, 6, v_config_566_);
lean_ctor_set(v_reuseFailAlloc_593_, 7, v_configFile_567_);
lean_ctor_set(v_reuseFailAlloc_593_, 8, v_relConfigFile_568_);
lean_ctor_set(v_reuseFailAlloc_593_, 9, v_relManifestFile_569_);
lean_ctor_set(v_reuseFailAlloc_593_, 10, v_scope_570_);
lean_ctor_set(v_reuseFailAlloc_593_, 11, v_remoteUrl_571_);
lean_ctor_set(v_reuseFailAlloc_593_, 12, v_depConfigs_572_);
lean_ctor_set(v_reuseFailAlloc_593_, 13, v_depIdxs_573_);
lean_ctor_set(v_reuseFailAlloc_593_, 14, v_depPkgs_588_);
lean_ctor_set(v_reuseFailAlloc_593_, 15, v_targetDecls_574_);
lean_ctor_set(v_reuseFailAlloc_593_, 16, v_targetDeclMap_575_);
lean_ctor_set(v_reuseFailAlloc_593_, 17, v_defaultTargets_576_);
lean_ctor_set(v_reuseFailAlloc_593_, 18, v_scripts_577_);
lean_ctor_set(v_reuseFailAlloc_593_, 19, v_defaultScripts_578_);
lean_ctor_set(v_reuseFailAlloc_593_, 20, v_postUpdateHooks_579_);
lean_ctor_set(v_reuseFailAlloc_593_, 21, v_buildArchive_580_);
lean_ctor_set(v_reuseFailAlloc_593_, 22, v_testDriver_581_);
lean_ctor_set(v_reuseFailAlloc_593_, 23, v_lintDriver_582_);
v___x_590_ = v_reuseFailAlloc_593_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v_pkgs_x27_591_; 
v_pkgs_x27_591_ = lean_array_fset(v_x_554_, v_n_558_, v___x_590_);
v_x_553_ = v_n_558_;
v_x_554_ = v_pkgs_x27_591_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(lean_object* v___x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
lean_object* v_zero_599_; uint8_t v_isZero_600_; 
v_zero_599_ = lean_unsigned_to_nat(0u);
v_isZero_600_ = lean_nat_dec_eq(v_x_597_, v_zero_599_);
if (v_isZero_600_ == 1)
{
return v_x_598_;
}
else
{
lean_object* v_one_601_; lean_object* v_n_602_; lean_object* v_pkg_603_; lean_object* v_wsIdx_604_; lean_object* v_baseName_605_; lean_object* v_keyName_606_; lean_object* v_origName_607_; lean_object* v_dir_608_; lean_object* v_relDir_609_; lean_object* v_config_610_; lean_object* v_configFile_611_; lean_object* v_relConfigFile_612_; lean_object* v_relManifestFile_613_; lean_object* v_scope_614_; lean_object* v_remoteUrl_615_; lean_object* v_depConfigs_616_; lean_object* v_depIdxs_617_; lean_object* v_targetDecls_618_; lean_object* v_targetDeclMap_619_; lean_object* v_defaultTargets_620_; lean_object* v_scripts_621_; lean_object* v_defaultScripts_622_; lean_object* v_postUpdateHooks_623_; lean_object* v_buildArchive_624_; lean_object* v_testDriver_625_; lean_object* v_lintDriver_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_638_; 
v_one_601_ = lean_unsigned_to_nat(1u);
v_n_602_ = lean_nat_sub(v_x_597_, v_one_601_);
v_pkg_603_ = lean_array_fget(v_x_598_, v_n_602_);
v_wsIdx_604_ = lean_ctor_get(v_pkg_603_, 0);
v_baseName_605_ = lean_ctor_get(v_pkg_603_, 1);
v_keyName_606_ = lean_ctor_get(v_pkg_603_, 2);
v_origName_607_ = lean_ctor_get(v_pkg_603_, 3);
v_dir_608_ = lean_ctor_get(v_pkg_603_, 4);
v_relDir_609_ = lean_ctor_get(v_pkg_603_, 5);
v_config_610_ = lean_ctor_get(v_pkg_603_, 6);
v_configFile_611_ = lean_ctor_get(v_pkg_603_, 7);
v_relConfigFile_612_ = lean_ctor_get(v_pkg_603_, 8);
v_relManifestFile_613_ = lean_ctor_get(v_pkg_603_, 9);
v_scope_614_ = lean_ctor_get(v_pkg_603_, 10);
v_remoteUrl_615_ = lean_ctor_get(v_pkg_603_, 11);
v_depConfigs_616_ = lean_ctor_get(v_pkg_603_, 12);
v_depIdxs_617_ = lean_ctor_get(v_pkg_603_, 13);
v_targetDecls_618_ = lean_ctor_get(v_pkg_603_, 15);
v_targetDeclMap_619_ = lean_ctor_get(v_pkg_603_, 16);
v_defaultTargets_620_ = lean_ctor_get(v_pkg_603_, 17);
v_scripts_621_ = lean_ctor_get(v_pkg_603_, 18);
v_defaultScripts_622_ = lean_ctor_get(v_pkg_603_, 19);
v_postUpdateHooks_623_ = lean_ctor_get(v_pkg_603_, 20);
v_buildArchive_624_ = lean_ctor_get(v_pkg_603_, 21);
v_testDriver_625_ = lean_ctor_get(v_pkg_603_, 22);
v_lintDriver_626_ = lean_ctor_get(v_pkg_603_, 23);
v_isSharedCheck_638_ = !lean_is_exclusive(v_pkg_603_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v_pkg_603_, 14);
lean_dec(v_unused_639_);
v___x_628_ = v_pkg_603_;
v_isShared_629_ = v_isSharedCheck_638_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_lintDriver_626_);
lean_inc(v_testDriver_625_);
lean_inc(v_buildArchive_624_);
lean_inc(v_postUpdateHooks_623_);
lean_inc(v_defaultScripts_622_);
lean_inc(v_scripts_621_);
lean_inc(v_defaultTargets_620_);
lean_inc(v_targetDeclMap_619_);
lean_inc(v_targetDecls_618_);
lean_inc(v_depIdxs_617_);
lean_inc(v_depConfigs_616_);
lean_inc(v_remoteUrl_615_);
lean_inc(v_scope_614_);
lean_inc(v_relManifestFile_613_);
lean_inc(v_relConfigFile_612_);
lean_inc(v_configFile_611_);
lean_inc(v_config_610_);
lean_inc(v_relDir_609_);
lean_inc(v_dir_608_);
lean_inc(v_origName_607_);
lean_inc(v_keyName_606_);
lean_inc(v_baseName_605_);
lean_inc(v_wsIdx_604_);
lean_dec(v_pkg_603_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_638_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
size_t v_sz_630_; size_t v___x_631_; lean_object* v_depPkgs_632_; lean_object* v___x_634_; 
v_sz_630_ = lean_array_size(v_depIdxs_617_);
v___x_631_ = ((size_t)0ULL);
lean_inc_ref(v_depIdxs_617_);
v_depPkgs_632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_x_598_, v_sz_630_, v___x_631_, v_depIdxs_617_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 14, v_depPkgs_632_);
v___x_634_ = v___x_628_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_wsIdx_604_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_baseName_605_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_keyName_606_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_origName_607_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_dir_608_);
lean_ctor_set(v_reuseFailAlloc_637_, 5, v_relDir_609_);
lean_ctor_set(v_reuseFailAlloc_637_, 6, v_config_610_);
lean_ctor_set(v_reuseFailAlloc_637_, 7, v_configFile_611_);
lean_ctor_set(v_reuseFailAlloc_637_, 8, v_relConfigFile_612_);
lean_ctor_set(v_reuseFailAlloc_637_, 9, v_relManifestFile_613_);
lean_ctor_set(v_reuseFailAlloc_637_, 10, v_scope_614_);
lean_ctor_set(v_reuseFailAlloc_637_, 11, v_remoteUrl_615_);
lean_ctor_set(v_reuseFailAlloc_637_, 12, v_depConfigs_616_);
lean_ctor_set(v_reuseFailAlloc_637_, 13, v_depIdxs_617_);
lean_ctor_set(v_reuseFailAlloc_637_, 14, v_depPkgs_632_);
lean_ctor_set(v_reuseFailAlloc_637_, 15, v_targetDecls_618_);
lean_ctor_set(v_reuseFailAlloc_637_, 16, v_targetDeclMap_619_);
lean_ctor_set(v_reuseFailAlloc_637_, 17, v_defaultTargets_620_);
lean_ctor_set(v_reuseFailAlloc_637_, 18, v_scripts_621_);
lean_ctor_set(v_reuseFailAlloc_637_, 19, v_defaultScripts_622_);
lean_ctor_set(v_reuseFailAlloc_637_, 20, v_postUpdateHooks_623_);
lean_ctor_set(v_reuseFailAlloc_637_, 21, v_buildArchive_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 22, v_testDriver_625_);
lean_ctor_set(v_reuseFailAlloc_637_, 23, v_lintDriver_626_);
v___x_634_ = v_reuseFailAlloc_637_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v_pkgs_x27_635_; lean_object* v___x_636_; 
v_pkgs_x27_635_ = lean_array_fset(v_x_598_, v_n_602_, v___x_634_);
v___x_636_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(v_n_602_, v_pkgs_x27_635_);
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1___boxed(lean_object* v___x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(v___x_640_, v_x_641_, v_x_642_);
lean_dec(v_x_641_);
lean_dec(v___x_640_);
return v_res_643_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(lean_object* v_as_644_, size_t v_i_645_, size_t v_stop_646_, lean_object* v_b_647_){
_start:
{
uint8_t v___x_648_; 
v___x_648_ = lean_usize_dec_eq(v_i_645_, v_stop_646_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v_keyName_650_; lean_object* v___x_651_; size_t v___x_652_; size_t v___x_653_; 
v___x_649_ = lean_array_uget_borrowed(v_as_644_, v_i_645_);
v_keyName_650_ = lean_ctor_get(v___x_649_, 2);
lean_inc(v___x_649_);
lean_inc(v_keyName_650_);
v___x_651_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_650_, v___x_649_, v_b_647_);
v___x_652_ = ((size_t)1ULL);
v___x_653_ = lean_usize_add(v_i_645_, v___x_652_);
v_i_645_ = v___x_653_;
v_b_647_ = v___x_651_;
goto _start;
}
else
{
return v_b_647_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_644_ = stack[0].m_obj;
size_t v_i_645_ = stack[1].m_num;
size_t v_stop_646_ = stack[2].m_num;
lean_object* v_b_647_ = stack[3].m_obj;
lean_object* v_res_655_;
v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_as_644_, v_i_645_, v_stop_646_, v_b_647_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2___boxed(lean_object* v_as_656_, lean_object* v_i_657_, lean_object* v_stop_658_, lean_object* v_b_659_){
_start:
{
size_t v_i_boxed_660_; size_t v_stop_boxed_661_; lean_object* v_res_662_; 
v_i_boxed_660_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_stop_boxed_661_ = lean_unbox_usize(v_stop_658_);
lean_dec(v_stop_658_);
v_res_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_as_656_, v_i_boxed_660_, v_stop_boxed_661_, v_b_659_);
lean_dec_ref(v_as_656_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(lean_object* v_self_663_){
_start:
{
lean_object* v_lakeEnv_664_; lean_object* v_lakeConfig_665_; lean_object* v_lakeCache_666_; lean_object* v_lakeArgs_x3f_667_; lean_object* v_packages_668_; lean_object* v_facetConfigs_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_688_; 
v_lakeEnv_664_ = lean_ctor_get(v_self_663_, 0);
v_lakeConfig_665_ = lean_ctor_get(v_self_663_, 1);
v_lakeCache_666_ = lean_ctor_get(v_self_663_, 2);
v_lakeArgs_x3f_667_ = lean_ctor_get(v_self_663_, 3);
v_packages_668_ = lean_ctor_get(v_self_663_, 4);
v_facetConfigs_669_ = lean_ctor_get(v_self_663_, 6);
v_isSharedCheck_688_ = !lean_is_exclusive(v_self_663_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v_self_663_, 5);
lean_dec(v_unused_689_);
v___x_671_ = v_self_663_;
v_isShared_672_ = v_isSharedCheck_688_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_facetConfigs_669_);
lean_inc(v_packages_668_);
lean_inc(v_lakeArgs_x3f_667_);
lean_inc(v_lakeCache_666_);
lean_inc(v_lakeConfig_665_);
lean_inc(v_lakeEnv_664_);
lean_dec(v_self_663_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_688_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v_val_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_673_ = lean_array_get_size(v_packages_668_);
v_val_674_ = l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(v___x_673_, v___x_673_, v_packages_668_);
v___x_675_ = lean_box(1);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_array_get_size(v_val_674_);
v___x_678_ = lean_nat_dec_lt(v___x_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_680_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 5, v___x_675_);
lean_ctor_set(v___x_671_, 4, v_val_674_);
v___x_680_ = v___x_671_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_lakeEnv_664_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_lakeConfig_665_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_lakeCache_666_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_lakeArgs_x3f_667_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_val_674_);
lean_ctor_set(v_reuseFailAlloc_681_, 5, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_681_, 6, v_facetConfigs_669_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_677_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_val_674_, v___x_682_, v___x_683_, v___x_675_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 5, v___x_684_);
lean_ctor_set(v___x_671_, 4, v_val_674_);
v___x_686_ = v___x_671_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_lakeEnv_664_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_lakeConfig_665_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_lakeCache_666_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_lakeArgs_x3f_667_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_val_674_);
lean_ctor_set(v_reuseFailAlloc_687_, 5, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 6, v_facetConfigs_669_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(lean_object* v___x_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(v_x_691_, v_x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___boxed(lean_object* v___x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(v___x_694_, v_x_695_, v_x_696_);
lean_dec(v___x_694_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(lean_object* v_ws_698_, lean_object* v_size_699_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_mk_empty_array_with_capacity(v_size_699_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_ws_698_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init___boxed(lean_object* v_ws_702_, lean_object* v_size_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(v_ws_702_, v_size_703_);
lean_dec(v_size_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___redArg(lean_object* v_s_705_, lean_object* v_wsIdx_706_){
_start:
{
lean_object* v_ws_707_; lean_object* v_depIdxs_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_716_; 
v_ws_707_ = lean_ctor_get(v_s_705_, 0);
v_depIdxs_708_ = lean_ctor_get(v_s_705_, 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v_s_705_);
if (v_isSharedCheck_716_ == 0)
{
v___x_710_ = v_s_705_;
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_depIdxs_708_);
lean_inc(v_ws_707_);
lean_dec(v_s_705_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_array_push(v_depIdxs_708_, v_wsIdx_706_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_ws_707_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(lean_object* v_n_717_, lean_object* v_s_718_, lean_object* v_wsIdx_719_){
_start:
{
lean_object* v_ws_720_; lean_object* v_depIdxs_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_729_; 
v_ws_720_ = lean_ctor_get(v_s_718_, 0);
v_depIdxs_721_ = lean_ctor_get(v_s_718_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_s_718_);
if (v_isSharedCheck_729_ == 0)
{
v___x_723_ = v_s_718_;
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_depIdxs_721_);
lean_inc(v_ws_720_);
lean_dec(v_s_718_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_array_push(v_depIdxs_721_, v_wsIdx_719_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_ws_720_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___boxed(lean_object* v_n_730_, lean_object* v_s_731_, lean_object* v_wsIdx_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(v_n_730_, v_s_731_, v_wsIdx_732_);
lean_dec(v_n_730_);
return v_res_733_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(lean_object* v_s_734_, lean_object* v_dep_735_, lean_object* v_lakeOpts_736_, lean_object* v_leanOpts_737_, uint8_t v_reconfigure_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_ws_741_; lean_object* v_depIdxs_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_771_; 
v_ws_741_ = lean_ctor_get(v_s_734_, 0);
v_depIdxs_742_ = lean_ctor_get(v_s_734_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_s_734_);
if (v_isSharedCheck_771_ == 0)
{
v___x_744_ = v_s_734_;
v_isShared_745_ = v_isSharedCheck_771_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_depIdxs_742_);
lean_inc(v_ws_741_);
lean_dec(v_s_734_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_771_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_packages_746_; lean_object* v_wsIdx_747_; lean_object* v___x_748_; 
v_packages_746_ = lean_ctor_get(v_ws_741_, 4);
v_wsIdx_747_ = lean_array_get_size(v_packages_746_);
v___x_748_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_741_, v_dep_735_, v_lakeOpts_736_, v_leanOpts_737_, v_reconfigure_738_, v_a_739_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_761_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_a_750_ = lean_ctor_get(v___x_748_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_761_ == 0)
{
v___x_752_ = v___x_748_;
v_isShared_753_ = v_isSharedCheck_761_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_761_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = lean_array_push(v_depIdxs_742_, v_wsIdx_747_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_754_);
lean_ctor_set(v___x_744_, 0, v_a_749_);
v___x_756_ = v___x_744_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_749_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_760_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_756_);
v___x_758_ = v___x_752_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_a_750_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_del_object(v___x_744_);
lean_dec_ref(v_depIdxs_742_);
v_a_762_ = lean_ctor_get(v___x_748_, 0);
v_a_763_ = lean_ctor_get(v___x_748_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_748_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_inc(v_a_762_);
lean_dec(v___x_748_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_762_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_734_ = stack[0].m_obj;
lean_object* v_dep_735_ = stack[1].m_obj;
lean_object* v_lakeOpts_736_ = stack[2].m_obj;
lean_object* v_leanOpts_737_ = stack[3].m_obj;
uint8_t v_reconfigure_738_ = stack[4].m_num;
lean_object* v_a_739_ = stack[5].m_obj;
lean_object* v_res_772_;
v_res_772_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(v_s_734_, v_dep_735_, v_lakeOpts_736_, v_leanOpts_737_, v_reconfigure_738_, v_a_739_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg___boxed(lean_object* v_s_773_, lean_object* v_dep_774_, lean_object* v_lakeOpts_775_, lean_object* v_leanOpts_776_, lean_object* v_reconfigure_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
uint8_t v_reconfigure_boxed_780_; lean_object* v_res_781_; 
v_reconfigure_boxed_780_ = lean_unbox(v_reconfigure_777_);
v_res_781_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(v_s_773_, v_dep_774_, v_lakeOpts_775_, v_leanOpts_776_, v_reconfigure_boxed_780_, v_a_778_);
return v_res_781_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(lean_object* v_n_782_, lean_object* v_s_783_, lean_object* v_dep_784_, lean_object* v_lakeOpts_785_, lean_object* v_leanOpts_786_, uint8_t v_reconfigure_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_ws_790_; lean_object* v_depIdxs_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_820_; 
v_ws_790_ = lean_ctor_get(v_s_783_, 0);
v_depIdxs_791_ = lean_ctor_get(v_s_783_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_s_783_);
if (v_isSharedCheck_820_ == 0)
{
v___x_793_ = v_s_783_;
v_isShared_794_ = v_isSharedCheck_820_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_depIdxs_791_);
lean_inc(v_ws_790_);
lean_dec(v_s_783_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_820_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_packages_795_; lean_object* v_wsIdx_796_; lean_object* v___x_797_; 
v_packages_795_ = lean_ctor_get(v_ws_790_, 4);
v_wsIdx_796_ = lean_array_get_size(v_packages_795_);
v___x_797_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_790_, v_dep_784_, v_lakeOpts_785_, v_leanOpts_786_, v_reconfigure_787_, v_a_788_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_810_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_a_799_ = lean_ctor_get(v___x_797_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_810_ == 0)
{
v___x_801_ = v___x_797_;
v_isShared_802_ = v_isSharedCheck_810_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_810_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_array_push(v_depIdxs_791_, v_wsIdx_796_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___x_803_);
lean_ctor_set(v___x_793_, 0, v_a_798_);
v___x_805_ = v___x_793_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_798_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_803_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_805_);
v___x_807_ = v___x_801_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_a_799_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_del_object(v___x_793_);
lean_dec_ref(v_depIdxs_791_);
v_a_811_ = lean_ctor_get(v___x_797_, 0);
v_a_812_ = lean_ctor_get(v___x_797_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_797_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_inc(v_a_811_);
lean_dec(v___x_797_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_811_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_782_ = stack[0].m_obj;
lean_object* v_s_783_ = stack[1].m_obj;
lean_object* v_dep_784_ = stack[2].m_obj;
lean_object* v_lakeOpts_785_ = stack[3].m_obj;
lean_object* v_leanOpts_786_ = stack[4].m_obj;
uint8_t v_reconfigure_787_ = stack[5].m_num;
lean_object* v_a_788_ = stack[6].m_obj;
lean_object* v_res_821_;
v_res_821_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(v_n_782_, v_s_783_, v_dep_784_, v_lakeOpts_785_, v_leanOpts_786_, v_reconfigure_787_, v_a_788_);
stack->m_obj
 = v_res_821_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed(lean_object* v_n_822_, lean_object* v_s_823_, lean_object* v_dep_824_, lean_object* v_lakeOpts_825_, lean_object* v_leanOpts_826_, lean_object* v_reconfigure_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
uint8_t v_reconfigure_boxed_830_; lean_object* v_res_831_; 
v_reconfigure_boxed_830_ = lean_unbox(v_reconfigure_827_);
v_res_831_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(v_n_822_, v_s_823_, v_dep_824_, v_lakeOpts_825_, v_leanOpts_826_, v_reconfigure_boxed_830_, v_a_828_);
lean_dec(v_n_822_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___redArg(lean_object* v_inst_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = lean_apply_2(v_inst_832_, lean_box(0), lean_box(0));
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(lean_object* v_m_834_, lean_object* v_00_u03b1_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_as_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_apply_2(v_inst_836_, lean_box(0), lean_box(0));
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___boxed(lean_object* v_m_840_, lean_object* v_00_u03b1_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_as_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(v_m_840_, v_00_u03b1_841_, v_inst_842_, v_inst_843_, v_as_844_);
lean_dec_ref(v_as_844_);
lean_dec(v_inst_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object* v_resolve_846_, lean_object* v_pkg_847_, lean_object* v_dep_848_, lean_object* v_ws_849_, lean_object* v_toBind_850_, lean_object* v___f_851_, lean_object* v_____r_852_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_apply_3(v_resolve_846_, v_pkg_847_, v_dep_848_, v_ws_849_);
v___x_854_ = lean_apply_4(v_toBind_850_, lean_box(0), lean_box(0), v___x_853_, v___f_851_);
return v___x_854_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object* v_start_855_, lean_object* v_s_856_, lean_object* v_opts_857_, lean_object* v_leanOpts_858_, uint8_t v_reconfigure_859_, lean_object* v_inst_860_, lean_object* v_matDep_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_box(v_reconfigure_859_);
v___x_863_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed), 8, 6);
lean_closure_set(v___x_863_, 0, v_start_855_);
lean_closure_set(v___x_863_, 1, v_s_856_);
lean_closure_set(v___x_863_, 2, v_matDep_861_);
lean_closure_set(v___x_863_, 3, v_opts_857_);
lean_closure_set(v___x_863_, 4, v_leanOpts_858_);
lean_closure_set(v___x_863_, 5, v___x_862_);
v___x_864_ = lean_apply_2(v_inst_860_, lean_box(0), v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_855_ = stack[0].m_obj;
lean_object* v_s_856_ = stack[1].m_obj;
lean_object* v_opts_857_ = stack[2].m_obj;
lean_object* v_leanOpts_858_ = stack[3].m_obj;
uint8_t v_reconfigure_859_ = stack[4].m_num;
lean_object* v_inst_860_ = stack[5].m_obj;
lean_object* v_matDep_861_ = stack[6].m_obj;
lean_object* v_res_865_;
v_res_865_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(v_start_855_, v_s_856_, v_opts_857_, v_leanOpts_858_, v_reconfigure_859_, v_inst_860_, v_matDep_861_);
stack->m_obj
 = v_res_865_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object* v_start_866_, lean_object* v_s_867_, lean_object* v_opts_868_, lean_object* v_leanOpts_869_, lean_object* v_reconfigure_870_, lean_object* v_inst_871_, lean_object* v_matDep_872_){
_start:
{
uint8_t v_reconfigure_boxed_873_; lean_object* v_res_874_; 
v_reconfigure_boxed_873_ = lean_unbox(v_reconfigure_870_);
v_res_874_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(v_start_866_, v_s_867_, v_opts_868_, v_leanOpts_869_, v_reconfigure_boxed_873_, v_inst_871_, v_matDep_872_);
return v_res_874_;
}
}
uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object* v_dep_875_, lean_object* v_x_876_){
_start:
{
lean_object* v_baseName_877_; lean_object* v_name_878_; uint8_t v___x_879_; 
v_baseName_877_ = lean_ctor_get(v_x_876_, 1);
v_name_878_ = lean_ctor_get(v_dep_875_, 0);
v___x_879_ = lean_name_eq(v_baseName_877_, v_name_878_);
return v___x_879_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_dep_875_ = stack[0].m_obj;
lean_object* v_x_876_ = stack[1].m_obj;
uint8_t v_res_880_;
v_res_880_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(v_dep_875_, v_x_876_);
stack->m_num = v_res_880_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed(lean_object* v_dep_881_, lean_object* v_x_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(v_dep_881_, v_x_882_);
lean_dec_ref(v_x_882_);
lean_dec_ref(v_dep_881_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object* v___f_885_, lean_object* v_____r_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_apply_1(v___f_885_, v_____r_886_);
return v___x_887_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object* v_toPure_889_, lean_object* v_start_890_, lean_object* v_leanOpts_891_, uint8_t v_reconfigure_892_, lean_object* v_inst_893_, lean_object* v_resolve_894_, lean_object* v_pkg_895_, lean_object* v_toBind_896_, lean_object* v_baseName_897_, lean_object* v_inst_898_, lean_object* v_dep_899_, lean_object* v_s_900_){
_start:
{
lean_object* v_ws_901_; lean_object* v_depIdxs_902_; lean_object* v_packages_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_ws_901_ = lean_ctor_get(v_s_900_, 0);
lean_inc_ref(v_ws_901_);
v_depIdxs_902_ = lean_ctor_get(v_s_900_, 1);
v_packages_903_ = lean_ctor_get(v_ws_901_, 4);
lean_inc_ref(v_dep_899_);
v___f_904_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_904_, 0, v_dep_899_);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_904_, v_packages_903_, v___x_905_);
if (lean_obj_tag(v___x_906_) == 1)
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_916_; 
lean_inc_ref(v_depIdxs_902_);
lean_dec_ref(v_dep_899_);
lean_dec(v_inst_898_);
lean_dec(v_baseName_897_);
lean_dec(v_toBind_896_);
lean_dec_ref(v_pkg_895_);
lean_dec(v_resolve_894_);
lean_dec(v_inst_893_);
lean_dec_ref(v_leanOpts_891_);
lean_dec(v_start_890_);
v_isSharedCheck_916_ = !lean_is_exclusive(v_s_900_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; lean_object* v_unused_918_; 
v_unused_917_ = lean_ctor_get(v_s_900_, 1);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_s_900_, 0);
lean_dec(v_unused_918_);
v___x_908_ = v_s_900_;
v_isShared_909_ = v_isSharedCheck_916_;
goto v_resetjp_907_;
}
else
{
lean_dec(v_s_900_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_916_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_val_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v_val_910_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_val_910_);
lean_dec_ref_known(v___x_906_, 1);
v___x_911_ = lean_array_push(v_depIdxs_902_, v_val_910_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v___x_911_);
v___x_913_ = v___x_908_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_ws_901_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_911_);
v___x_913_ = v_reuseFailAlloc_915_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; 
v___x_914_ = lean_apply_2(v_toPure_889_, lean_box(0), v___x_913_);
return v___x_914_;
}
}
}
else
{
lean_object* v_name_919_; lean_object* v_opts_920_; lean_object* v___x_921_; lean_object* v___f_922_; lean_object* v___f_923_; uint8_t v___x_924_; 
lean_dec(v___x_906_);
lean_dec(v_toPure_889_);
v_name_919_ = lean_ctor_get(v_dep_899_, 0);
v_opts_920_ = lean_ctor_get(v_dep_899_, 4);
v___x_921_ = lean_box(v_reconfigure_892_);
lean_inc(v_opts_920_);
v___f_922_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_922_, 0, v_start_890_);
lean_closure_set(v___f_922_, 1, v_s_900_);
lean_closure_set(v___f_922_, 2, v_opts_920_);
lean_closure_set(v___f_922_, 3, v_leanOpts_891_);
lean_closure_set(v___f_922_, 4, v___x_921_);
lean_closure_set(v___f_922_, 5, v_inst_893_);
lean_inc_ref(v___f_922_);
lean_inc(v_toBind_896_);
lean_inc_ref(v_ws_901_);
lean_inc_ref(v_dep_899_);
lean_inc_ref(v_pkg_895_);
lean_inc(v_resolve_894_);
v___f_923_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4), 7, 6);
lean_closure_set(v___f_923_, 0, v_resolve_894_);
lean_closure_set(v___f_923_, 1, v_pkg_895_);
lean_closure_set(v___f_923_, 2, v_dep_899_);
lean_closure_set(v___f_923_, 3, v_ws_901_);
lean_closure_set(v___f_923_, 4, v_toBind_896_);
lean_closure_set(v___f_923_, 5, v___f_922_);
v___x_924_ = lean_name_eq(v_baseName_897_, v_name_919_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref(v___f_923_);
lean_dec(v_inst_898_);
lean_dec(v_baseName_897_);
v___x_925_ = lean_box(0);
v___x_926_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(v_resolve_894_, v_pkg_895_, v_dep_899_, v_ws_901_, v_toBind_896_, v___f_922_, v___x_925_);
return v___x_926_;
}
else
{
lean_object* v___f_927_; uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v___f_922_);
lean_dec_ref(v_ws_901_);
lean_dec_ref(v_dep_899_);
lean_dec_ref(v_pkg_895_);
lean_dec(v_resolve_894_);
v___f_927_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5), 2, 1);
lean_closure_set(v___f_927_, 0, v___f_923_);
v___x_928_ = 0;
v___x_929_ = l_Lean_Name_toString(v_baseName_897_, v___x_928_);
v___x_930_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_931_ = lean_string_append(v___x_929_, v___x_930_);
v___x_932_ = lean_apply_2(v_inst_898_, lean_box(0), v___x_931_);
v___x_933_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_932_, v___f_927_);
return v___x_933_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_889_ = stack[0].m_obj;
lean_object* v_start_890_ = stack[1].m_obj;
lean_object* v_leanOpts_891_ = stack[2].m_obj;
uint8_t v_reconfigure_892_ = stack[3].m_num;
lean_object* v_inst_893_ = stack[4].m_obj;
lean_object* v_resolve_894_ = stack[5].m_obj;
lean_object* v_pkg_895_ = stack[6].m_obj;
lean_object* v_toBind_896_ = stack[7].m_obj;
lean_object* v_baseName_897_ = stack[8].m_obj;
lean_object* v_inst_898_ = stack[9].m_obj;
lean_object* v_dep_899_ = stack[10].m_obj;
lean_object* v_s_900_ = stack[11].m_obj;
lean_object* v_res_934_;
v_res_934_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(v_toPure_889_, v_start_890_, v_leanOpts_891_, v_reconfigure_892_, v_inst_893_, v_resolve_894_, v_pkg_895_, v_toBind_896_, v_baseName_897_, v_inst_898_, v_dep_899_, v_s_900_);
stack->m_obj
 = v_res_934_;
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
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object* v_pkg_960_, lean_object* v_next_961_, lean_object* v_toPure_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_resolve_966_, lean_object* v_leanOpts_967_, uint8_t v_reconfigure_968_, lean_object* v_toBind_969_, lean_object* v_____x_970_){
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
v___x_975_ = lean_array_get_size(v_packages_974_);
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
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_960_ = stack[0].m_obj;
lean_object* v_next_961_ = stack[1].m_obj;
lean_object* v_toPure_962_ = stack[2].m_obj;
lean_object* v_inst_963_ = stack[3].m_obj;
lean_object* v_inst_964_ = stack[4].m_obj;
lean_object* v_inst_965_ = stack[5].m_obj;
lean_object* v_resolve_966_ = stack[6].m_obj;
lean_object* v_leanOpts_967_ = stack[7].m_obj;
uint8_t v_reconfigure_968_ = stack[8].m_num;
lean_object* v_toBind_969_ = stack[9].m_obj;
lean_object* v_____x_970_ = stack[10].m_obj;
lean_object* v_res_982_;
v_res_982_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(v_pkg_960_, v_next_961_, v_toPure_962_, v_inst_963_, v_inst_964_, v_inst_965_, v_resolve_966_, v_leanOpts_967_, v_reconfigure_968_, v_toBind_969_, v_____x_970_);
stack->m_obj
 = v_res_982_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed(lean_object* v_pkg_983_, lean_object* v_next_984_, lean_object* v_toPure_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_resolve_989_, lean_object* v_leanOpts_990_, lean_object* v_reconfigure_991_, lean_object* v_toBind_992_, lean_object* v_____x_993_){
_start:
{
uint8_t v_reconfigure_boxed_994_; lean_object* v_res_995_; 
v_reconfigure_boxed_994_ = lean_unbox(v_reconfigure_991_);
v_res_995_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(v_pkg_983_, v_next_984_, v_toPure_985_, v_inst_986_, v_inst_987_, v_inst_988_, v_resolve_989_, v_leanOpts_990_, v_reconfigure_boxed_994_, v_toBind_992_, v_____x_993_);
return v_res_995_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_resolve_999_, lean_object* v_leanOpts_1000_, uint8_t v_reconfigure_1001_, lean_object* v_ws_1002_, lean_object* v_i_1003_, lean_object* v_next_1004_){
_start:
{
lean_object* v_packages_1005_; lean_object* v_pkg_1006_; lean_object* v_toApplicative_1007_; lean_object* v_baseName_1008_; lean_object* v_depConfigs_1009_; lean_object* v_toBind_1010_; lean_object* v_toPure_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_s_1014_; lean_object* v___x_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_packages_1005_ = lean_ctor_get(v_ws_1002_, 4);
lean_inc_ref(v_packages_1005_);
v_pkg_1006_ = lean_array_fget(v_packages_1005_, v_i_1003_);
v_toApplicative_1007_ = lean_ctor_get(v_inst_996_, 0);
v_baseName_1008_ = lean_ctor_get(v_pkg_1006_, 1);
lean_inc(v_baseName_1008_);
v_depConfigs_1009_ = lean_ctor_get(v_pkg_1006_, 12);
lean_inc_ref(v_depConfigs_1009_);
v_toBind_1010_ = lean_ctor_get(v_inst_996_, 1);
lean_inc_n(v_toBind_1010_, 2);
v_toPure_1011_ = lean_ctor_get(v_toApplicative_1007_, 1);
v___x_1012_ = lean_array_get_size(v_depConfigs_1009_);
v___x_1013_ = lean_mk_empty_array_with_capacity(v___x_1012_);
v_s_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_1014_, 0, v_ws_1002_);
lean_ctor_set(v_s_1014_, 1, v___x_1013_);
v___x_1015_ = lean_box(v_reconfigure_1001_);
lean_inc_ref(v_leanOpts_1000_);
lean_inc(v_resolve_999_);
lean_inc(v_inst_998_);
lean_inc(v_inst_997_);
lean_inc_ref(v_inst_996_);
lean_inc(v_toPure_1011_);
lean_inc(v_pkg_1006_);
v___f_1016_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_1016_, 0, v_pkg_1006_);
lean_closure_set(v___f_1016_, 1, v_next_1004_);
lean_closure_set(v___f_1016_, 2, v_toPure_1011_);
lean_closure_set(v___f_1016_, 3, v_inst_996_);
lean_closure_set(v___f_1016_, 4, v_inst_997_);
lean_closure_set(v___f_1016_, 5, v_inst_998_);
lean_closure_set(v___f_1016_, 6, v_resolve_999_);
lean_closure_set(v___f_1016_, 7, v_leanOpts_1000_);
lean_closure_set(v___f_1016_, 8, v___x_1015_);
lean_closure_set(v___f_1016_, 9, v_toBind_1010_);
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lean_nat_dec_lt(v___x_1017_, v___x_1012_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_inc(v_toPure_1011_);
lean_dec_ref(v_depConfigs_1009_);
lean_dec(v_baseName_1008_);
lean_dec(v_pkg_1006_);
lean_dec_ref(v_packages_1005_);
lean_dec_ref(v_leanOpts_1000_);
lean_dec(v_resolve_999_);
lean_dec(v_inst_998_);
lean_dec(v_inst_997_);
lean_dec_ref(v_inst_996_);
v___x_1019_ = lean_apply_2(v_toPure_1011_, lean_box(0), v_s_1014_);
v___x_1020_ = lean_apply_4(v_toBind_1010_, lean_box(0), lean_box(0), v___x_1019_, v___f_1016_);
return v___x_1020_;
}
else
{
lean_object* v_start_1021_; lean_object* v___x_1022_; lean_object* v___f_1023_; size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_start_1021_ = lean_array_get_size(v_packages_1005_);
lean_dec_ref(v_packages_1005_);
v___x_1022_ = lean_box(v_reconfigure_1001_);
lean_inc(v_toBind_1010_);
lean_inc(v_toPure_1011_);
v___f_1023_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed), 12, 10);
lean_closure_set(v___f_1023_, 0, v_toPure_1011_);
lean_closure_set(v___f_1023_, 1, v_start_1021_);
lean_closure_set(v___f_1023_, 2, v_leanOpts_1000_);
lean_closure_set(v___f_1023_, 3, v___x_1022_);
lean_closure_set(v___f_1023_, 4, v_inst_998_);
lean_closure_set(v___f_1023_, 5, v_resolve_999_);
lean_closure_set(v___f_1023_, 6, v_pkg_1006_);
lean_closure_set(v___f_1023_, 7, v_toBind_1010_);
lean_closure_set(v___f_1023_, 8, v_baseName_1008_);
lean_closure_set(v___f_1023_, 9, v_inst_997_);
v___x_1024_ = lean_usize_of_nat(v___x_1012_);
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_996_, v___f_1023_, v_depConfigs_1009_, v___x_1024_, v___x_1025_, v_s_1014_);
v___x_1027_ = lean_apply_4(v_toBind_1010_, lean_box(0), lean_box(0), v___x_1026_, v___f_1016_);
return v___x_1027_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_996_ = stack[0].m_obj;
lean_object* v_inst_997_ = stack[1].m_obj;
lean_object* v_inst_998_ = stack[2].m_obj;
lean_object* v_resolve_999_ = stack[3].m_obj;
lean_object* v_leanOpts_1000_ = stack[4].m_obj;
uint8_t v_reconfigure_1001_ = stack[5].m_num;
lean_object* v_ws_1002_ = stack[6].m_obj;
lean_object* v_i_1003_ = stack[7].m_obj;
lean_object* v_next_1004_ = stack[8].m_obj;
lean_object* v_res_1028_;
v_res_1028_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_996_, v_inst_997_, v_inst_998_, v_resolve_999_, v_leanOpts_1000_, v_reconfigure_1001_, v_ws_1002_, v_i_1003_, v_next_1004_);
stack->m_obj
 = v_res_1028_;
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object* v_next_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_resolve_1033_, lean_object* v_leanOpts_1034_, uint8_t v_reconfigure_1035_, lean_object* v_ws_1036_, lean_object* v_____x_1037_){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_unsigned_to_nat(1u);
v___x_1039_ = lean_nat_add(v_next_1029_, v___x_1038_);
v___x_1040_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1030_, v_inst_1031_, v_inst_1032_, v_resolve_1033_, v_leanOpts_1034_, v_reconfigure_1035_, v_ws_1036_, v_next_1029_, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_next_1029_ = stack[0].m_obj;
lean_object* v_inst_1030_ = stack[1].m_obj;
lean_object* v_inst_1031_ = stack[2].m_obj;
lean_object* v_inst_1032_ = stack[3].m_obj;
lean_object* v_resolve_1033_ = stack[4].m_obj;
lean_object* v_leanOpts_1034_ = stack[5].m_obj;
uint8_t v_reconfigure_1035_ = stack[6].m_num;
lean_object* v_ws_1036_ = stack[7].m_obj;
lean_object* v_res_1041_;
v_res_1041_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(v_next_1029_, v_inst_1030_, v_inst_1031_, v_inst_1032_, v_resolve_1033_, v_leanOpts_1034_, v_reconfigure_1035_, v_ws_1036_, lean_box(0));
stack->m_obj
 = v_res_1041_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_resolve_1045_, lean_object* v_leanOpts_1046_, lean_object* v_reconfigure_1047_, lean_object* v_ws_1048_, lean_object* v_i_1049_, lean_object* v_next_1050_){
_start:
{
uint8_t v_reconfigure_boxed_1051_; lean_object* v_res_1052_; 
v_reconfigure_boxed_1051_ = lean_unbox(v_reconfigure_1047_);
v_res_1052_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1042_, v_inst_1043_, v_inst_1044_, v_resolve_1045_, v_leanOpts_1046_, v_reconfigure_boxed_1051_, v_ws_1048_, v_i_1049_, v_next_1050_);
lean_dec(v_i_1049_);
return v_res_1052_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* v_m_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_resolve_1057_, lean_object* v_leanOpts_1058_, uint8_t v_reconfigure_1059_, lean_object* v_ws_1060_, lean_object* v_i_1061_, lean_object* v_i__lt_1062_, lean_object* v_next_1063_, lean_object* v_lt__next_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1054_, v_inst_1055_, v_inst_1056_, v_resolve_1057_, v_leanOpts_1058_, v_reconfigure_1059_, v_ws_1060_, v_i_1061_, v_next_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1054_ = stack[1].m_obj;
lean_object* v_inst_1055_ = stack[2].m_obj;
lean_object* v_inst_1056_ = stack[3].m_obj;
lean_object* v_resolve_1057_ = stack[4].m_obj;
lean_object* v_leanOpts_1058_ = stack[5].m_obj;
uint8_t v_reconfigure_1059_ = stack[6].m_num;
lean_object* v_ws_1060_ = stack[7].m_obj;
lean_object* v_i_1061_ = stack[8].m_obj;
lean_object* v_next_1063_ = stack[10].m_obj;
lean_object* v_res_1066_;
v_res_1066_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_box(0), v_inst_1054_, v_inst_1055_, v_inst_1056_, v_resolve_1057_, v_leanOpts_1058_, v_reconfigure_1059_, v_ws_1060_, v_i_1061_, lean_box(0), v_next_1063_, lean_box(0));
stack->m_obj
 = v_res_1066_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object* v_m_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_resolve_1071_, lean_object* v_leanOpts_1072_, lean_object* v_reconfigure_1073_, lean_object* v_ws_1074_, lean_object* v_i_1075_, lean_object* v_i__lt_1076_, lean_object* v_next_1077_, lean_object* v_lt__next_1078_){
_start:
{
uint8_t v_reconfigure_boxed_1079_; lean_object* v_res_1080_; 
v_reconfigure_boxed_1079_ = lean_unbox(v_reconfigure_1073_);
v_res_1080_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(v_m_1067_, v_inst_1068_, v_inst_1069_, v_inst_1070_, v_resolve_1071_, v_leanOpts_1072_, v_reconfigure_boxed_1079_, v_ws_1074_, v_i_1075_, v_i__lt_1076_, v_next_1077_, v_lt__next_1078_);
lean_dec(v_i_1075_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___redArg(lean_object* v_x_1081_, lean_object* v_h__1_1082_, lean_object* v_h__2_1083_){
_start:
{
if (lean_obj_tag(v_x_1081_) == 1)
{
lean_object* v_val_1084_; lean_object* v___x_1085_; 
lean_dec(v_h__2_1083_);
v_val_1084_ = lean_ctor_get(v_x_1081_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v_x_1081_, 1);
v___x_1085_ = lean_apply_1(v_h__1_1082_, v_val_1084_);
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; 
lean_dec(v_h__1_1082_);
v___x_1086_ = lean_apply_2(v_h__2_1083_, v_x_1081_, lean_box(0));
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(lean_object* v_ws_1087_, lean_object* v_s_1088_, lean_object* v_motive_1089_, lean_object* v_x_1090_, lean_object* v_h__1_1091_, lean_object* v_h__2_1092_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 1)
{
lean_object* v_val_1093_; lean_object* v___x_1094_; 
lean_dec(v_h__2_1092_);
v_val_1093_ = lean_ctor_get(v_x_1090_, 0);
lean_inc(v_val_1093_);
lean_dec_ref_known(v_x_1090_, 1);
v___x_1094_ = lean_apply_1(v_h__1_1091_, v_val_1093_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; 
lean_dec(v_h__1_1091_);
v___x_1095_ = lean_apply_2(v_h__2_1092_, v_x_1090_, lean_box(0));
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___boxed(lean_object* v_ws_1096_, lean_object* v_s_1097_, lean_object* v_motive_1098_, lean_object* v_x_1099_, lean_object* v_h__1_1100_, lean_object* v_h__2_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(v_ws_1096_, v_s_1097_, v_motive_1098_, v_x_1099_, v_h__1_1100_, v_h__2_1101_);
lean_dec_ref(v_s_1097_);
lean_dec_ref(v_ws_1096_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___redArg(lean_object* v_x_1103_, lean_object* v_h__1_1104_){
_start:
{
lean_object* v_ws_1105_; lean_object* v_depIdxs_1106_; lean_object* v___x_1107_; 
v_ws_1105_ = lean_ctor_get(v_x_1103_, 0);
lean_inc_ref(v_ws_1105_);
v_depIdxs_1106_ = lean_ctor_get(v_x_1103_, 1);
lean_inc_ref(v_depIdxs_1106_);
lean_dec_ref(v_x_1103_);
v___x_1107_ = lean_apply_4(v_h__1_1104_, v_ws_1105_, v_depIdxs_1106_, lean_box(0), lean_box(0));
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(lean_object* v_ws_1108_, lean_object* v_motive_1109_, lean_object* v_x_1110_, lean_object* v_h__1_1111_){
_start:
{
lean_object* v_ws_1112_; lean_object* v_depIdxs_1113_; lean_object* v___x_1114_; 
v_ws_1112_ = lean_ctor_get(v_x_1110_, 0);
lean_inc_ref(v_ws_1112_);
v_depIdxs_1113_ = lean_ctor_get(v_x_1110_, 1);
lean_inc_ref(v_depIdxs_1113_);
lean_dec_ref(v_x_1110_);
v___x_1114_ = lean_apply_4(v_h__1_1111_, v_ws_1112_, v_depIdxs_1113_, lean_box(0), lean_box(0));
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___boxed(lean_object* v_ws_1115_, lean_object* v_motive_1116_, lean_object* v_x_1117_, lean_object* v_h__1_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(v_ws_1115_, v_motive_1116_, v_x_1117_, v_h__1_1118_);
lean_dec_ref(v_ws_1115_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___redArg(lean_object* v_h__1_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_apply_1(v_h__1_1120_, lean_box(0));
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(lean_object* v_ws_1122_, lean_object* v_motive_1123_, lean_object* v_x_1124_, lean_object* v_h__1_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_apply_1(v_h__1_1125_, lean_box(0));
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___boxed(lean_object* v_ws_1127_, lean_object* v_motive_1128_, lean_object* v_x_1129_, lean_object* v_h__1_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(v_ws_1127_, v_motive_1128_, v_x_1129_, v_h__1_1130_);
lean_dec_ref(v_ws_1127_);
return v_res_1131_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_ws_1136_, lean_object* v_resolve_1137_, lean_object* v_root_1138_, lean_object* v_next_1139_, lean_object* v_leanOpts_1140_, uint8_t v_reconfigure_1141_){
_start:
{
lean_object* v_toApplicative_1142_; lean_object* v_toFunctor_1143_; lean_object* v_map_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_toApplicative_1142_ = lean_ctor_get(v_inst_1133_, 0);
v_toFunctor_1143_ = lean_ctor_get(v_toApplicative_1142_, 0);
v_map_1144_ = lean_ctor_get(v_toFunctor_1143_, 0);
lean_inc(v_map_1144_);
v___f_1145_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0));
v___x_1146_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1133_, v_inst_1134_, v_inst_1135_, v_resolve_1137_, v_leanOpts_1140_, v_reconfigure_1141_, v_ws_1136_, v_root_1138_, v_next_1139_);
v___x_1147_ = lean_apply_4(v_map_1144_, lean_box(0), lean_box(0), v___f_1145_, v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1133_ = stack[0].m_obj;
lean_object* v_inst_1134_ = stack[1].m_obj;
lean_object* v_inst_1135_ = stack[2].m_obj;
lean_object* v_ws_1136_ = stack[3].m_obj;
lean_object* v_resolve_1137_ = stack[4].m_obj;
lean_object* v_root_1138_ = stack[5].m_obj;
lean_object* v_next_1139_ = stack[6].m_obj;
lean_object* v_leanOpts_1140_ = stack[7].m_obj;
uint8_t v_reconfigure_1141_ = stack[8].m_num;
lean_object* v_res_1148_;
v_res_1148_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(v_inst_1133_, v_inst_1134_, v_inst_1135_, v_ws_1136_, v_resolve_1137_, v_root_1138_, v_next_1139_, v_leanOpts_1140_, v_reconfigure_1141_);
stack->m_obj
 = v_res_1148_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_ws_1152_, lean_object* v_resolve_1153_, lean_object* v_root_1154_, lean_object* v_next_1155_, lean_object* v_leanOpts_1156_, lean_object* v_reconfigure_1157_){
_start:
{
uint8_t v_reconfigure_boxed_1158_; lean_object* v_res_1159_; 
v_reconfigure_boxed_1158_ = lean_unbox(v_reconfigure_1157_);
v_res_1159_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(v_inst_1149_, v_inst_1150_, v_inst_1151_, v_ws_1152_, v_resolve_1153_, v_root_1154_, v_next_1155_, v_leanOpts_1156_, v_reconfigure_boxed_1158_);
lean_dec(v_root_1154_);
return v_res_1159_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* v_m_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_, lean_object* v_ws_1164_, lean_object* v_resolve_1165_, lean_object* v_root_1166_, lean_object* v_root__lt_1167_, lean_object* v_next_1168_, lean_object* v_next__lt_1169_, lean_object* v_leanOpts_1170_, uint8_t v_reconfigure_1171_){
_start:
{
lean_object* v_toApplicative_1172_; lean_object* v_toFunctor_1173_; lean_object* v_map_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_toApplicative_1172_ = lean_ctor_get(v_inst_1161_, 0);
v_toFunctor_1173_ = lean_ctor_get(v_toApplicative_1172_, 0);
v_map_1174_ = lean_ctor_get(v_toFunctor_1173_, 0);
lean_inc(v_map_1174_);
v___f_1175_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0));
v___x_1176_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1161_, v_inst_1162_, v_inst_1163_, v_resolve_1165_, v_leanOpts_1170_, v_reconfigure_1171_, v_ws_1164_, v_root_1166_, v_next_1168_);
v___x_1177_ = lean_apply_4(v_map_1174_, lean_box(0), lean_box(0), v___f_1175_, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1161_ = stack[1].m_obj;
lean_object* v_inst_1162_ = stack[2].m_obj;
lean_object* v_inst_1163_ = stack[3].m_obj;
lean_object* v_ws_1164_ = stack[4].m_obj;
lean_object* v_resolve_1165_ = stack[5].m_obj;
lean_object* v_root_1166_ = stack[6].m_obj;
lean_object* v_next_1168_ = stack[8].m_obj;
lean_object* v_leanOpts_1170_ = stack[10].m_obj;
uint8_t v_reconfigure_1171_ = stack[11].m_num;
lean_object* v_res_1178_;
v_res_1178_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_box(0), v_inst_1161_, v_inst_1162_, v_inst_1163_, v_ws_1164_, v_resolve_1165_, v_root_1166_, lean_box(0), v_next_1168_, lean_box(0), v_leanOpts_1170_, v_reconfigure_1171_);
stack->m_obj
 = v_res_1178_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object* v_m_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_ws_1183_, lean_object* v_resolve_1184_, lean_object* v_root_1185_, lean_object* v_root__lt_1186_, lean_object* v_next_1187_, lean_object* v_next__lt_1188_, lean_object* v_leanOpts_1189_, lean_object* v_reconfigure_1190_){
_start:
{
uint8_t v_reconfigure_boxed_1191_; lean_object* v_res_1192_; 
v_reconfigure_boxed_1191_ = lean_unbox(v_reconfigure_1190_);
v_res_1192_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(v_m_1179_, v_inst_1180_, v_inst_1181_, v_inst_1182_, v_ws_1183_, v_resolve_1184_, v_root_1185_, v_root__lt_1186_, v_next_1187_, v_next__lt_1188_, v_leanOpts_1189_, v_reconfigure_boxed_1191_);
lean_dec(v_root_1185_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object* v_x_1193_, lean_object* v_init_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_apply_1(v_x_1193_, v_init_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object* v_m_1196_, lean_object* v_00_u03b1_1197_, lean_object* v_x_1198_, lean_object* v_init_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_apply_1(v_x_1198_, v_init_1199_);
return v___x_1200_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(lean_object* v_as_1201_, size_t v_i_1202_, size_t v_stop_1203_, lean_object* v_b_1204_){
_start:
{
uint8_t v___x_1205_; 
v___x_1205_ = lean_usize_dec_eq(v_i_1202_, v_stop_1203_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v_name_1207_; lean_object* v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; 
v___x_1206_ = lean_array_uget_borrowed(v_as_1201_, v_i_1202_);
v_name_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_name_1207_);
v___x_1208_ = l_Lean_NameSet_insert(v_b_1204_, v_name_1207_);
v___x_1209_ = ((size_t)1ULL);
v___x_1210_ = lean_usize_add(v_i_1202_, v___x_1209_);
v_i_1202_ = v___x_1210_;
v_b_1204_ = v___x_1208_;
goto _start;
}
else
{
return v_b_1204_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1201_ = stack[0].m_obj;
size_t v_i_1202_ = stack[1].m_num;
size_t v_stop_1203_ = stack[2].m_num;
lean_object* v_b_1204_ = stack[3].m_obj;
lean_object* v_res_1212_;
v_res_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_as_1201_, v_i_1202_, v_stop_1203_, v_b_1204_);
stack->m_obj
 = v_res_1212_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2___boxed(lean_object* v_as_1213_, lean_object* v_i_1214_, lean_object* v_stop_1215_, lean_object* v_b_1216_){
_start:
{
size_t v_i_boxed_1217_; size_t v_stop_boxed_1218_; lean_object* v_res_1219_; 
v_i_boxed_1217_ = lean_unbox_usize(v_i_1214_);
lean_dec(v_i_1214_);
v_stop_boxed_1218_ = lean_unbox_usize(v_stop_1215_);
lean_dec(v_stop_1215_);
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_as_1213_, v_i_boxed_1217_, v_stop_boxed_1218_, v_b_1216_);
lean_dec_ref(v_as_1213_);
return v_res_1219_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(lean_object* v_as_1220_, size_t v_sz_1221_, size_t v_i_1222_, lean_object* v_b_1223_, lean_object* v___y_1224_){
_start:
{
uint8_t v___x_1226_; 
v___x_1226_ = lean_usize_dec_lt(v_i_1222_, v_sz_1221_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_b_1223_);
lean_ctor_set(v___x_1227_, 1, v___y_1224_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
else
{
lean_object* v_a_1229_; lean_object* v_name_1230_; lean_object* v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; 
v_a_1229_ = lean_array_uget_borrowed(v_as_1220_, v_i_1222_);
v_name_1230_ = lean_ctor_get(v_a_1229_, 0);
lean_inc(v_name_1230_);
v___x_1231_ = l_Lean_NameSet_insert(v_b_1223_, v_name_1230_);
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_add(v_i_1222_, v___x_1232_);
v_i_1222_ = v___x_1233_;
v_b_1223_ = v___x_1231_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1220_ = stack[0].m_obj;
size_t v_sz_1221_ = stack[1].m_num;
size_t v_i_1222_ = stack[2].m_num;
lean_object* v_b_1223_ = stack[3].m_obj;
lean_object* v___y_1224_ = stack[4].m_obj;
lean_object* v_res_1235_;
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1220_, v_sz_1221_, v_i_1222_, v_b_1223_, v___y_1224_);
stack->m_obj
 = v_res_1235_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg___boxed(lean_object* v_as_1236_, lean_object* v_sz_1237_, lean_object* v_i_1238_, lean_object* v_b_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
size_t v_sz_boxed_1242_; size_t v_i_boxed_1243_; lean_object* v_res_1244_; 
v_sz_boxed_1242_ = lean_unbox_usize(v_sz_1237_);
lean_dec(v_sz_1237_);
v_i_boxed_1243_ = lean_unbox_usize(v_i_1238_);
lean_dec(v_i_1238_);
v_res_1244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1236_, v_sz_boxed_1242_, v_i_boxed_1243_, v_b_1239_, v___y_1240_);
lean_dec_ref(v_as_1236_);
return v_res_1244_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_fst_1247_, lean_object* v_init_1248_, lean_object* v_x_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
if (lean_obj_tag(v_x_1249_) == 0)
{
lean_object* v_k_1253_; lean_object* v_l_1254_; lean_object* v_r_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_k_1253_ = lean_ctor_get(v_x_1249_, 1);
lean_inc(v_k_1253_);
v_l_1254_ = lean_ctor_get(v_x_1249_, 3);
lean_inc(v_l_1254_);
v_r_1255_ = lean_ctor_get(v_x_1249_, 4);
lean_inc(v_r_1255_);
lean_dec_ref_known(v_x_1249_, 5);
v___x_1256_ = lean_box(0);
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1247_, v_init_1248_, v_l_1254_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1276_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1276_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1276_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_snd_1262_; uint8_t v___x_1263_; 
v_snd_1262_ = lean_ctor_get(v_a_1258_, 1);
lean_inc(v_snd_1262_);
lean_dec(v_a_1258_);
v___x_1263_ = l_Lean_NameSet_contains(v_fst_1247_, v_k_1253_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
lean_dec(v_snd_1262_);
lean_dec(v_r_1255_);
v___x_1264_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__0));
v___x_1265_ = l_Lean_Name_toString(v_k_1253_, v___x_1263_);
v___x_1266_ = lean_string_append(v___x_1264_, v___x_1265_);
lean_dec_ref(v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__1));
v___x_1268_ = lean_string_append(v___x_1266_, v___x_1267_);
v___x_1269_ = 3;
v___x_1270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*1, v___x_1269_);
lean_inc_ref(v___y_1251_);
v___x_1271_ = lean_apply_2(v___y_1251_, v___x_1270_, lean_box(0));
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 1);
lean_ctor_set(v___x_1260_, 0, v___x_1256_);
v___x_1273_ = v___x_1260_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1256_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
else
{
lean_del_object(v___x_1260_);
lean_dec(v_k_1253_);
v_init_1248_ = v___x_1256_;
v_x_1249_ = v_r_1255_;
v___y_1250_ = v_snd_1262_;
goto _start;
}
}
}
else
{
lean_dec(v_r_1255_);
lean_dec(v_k_1253_);
return v___x_1257_;
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v_init_1248_);
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v___y_1250_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1247_ = stack[0].m_obj;
lean_object* v_init_1248_ = stack[1].m_obj;
lean_object* v_x_1249_ = stack[2].m_obj;
lean_object* v___y_1250_ = stack[3].m_obj;
lean_object* v___y_1251_ = stack[4].m_obj;
lean_object* v_res_1280_;
v_res_1280_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1247_, v_init_1248_, v_x_1249_, v___y_1250_, v___y_1251_);
stack->m_obj
 = v_res_1280_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_fst_1281_, lean_object* v_init_1282_, lean_object* v_x_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1281_, v_init_1282_, v_x_1283_, v___y_1284_, v___y_1285_);
lean_dec_ref(v___y_1285_);
lean_dec(v_fst_1281_);
return v_res_1287_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(lean_object* v_toUpdate_1288_, lean_object* v___x_1289_, lean_object* v___x_1290_, lean_object* v_entries_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___y_1296_; 
if (lean_obj_tag(v_toUpdate_1288_) == 0)
{
lean_object* v_depConfigs_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_depConfigs_1338_ = lean_ctor_get(v___x_1289_, 12);
v___x_1339_ = l_Lean_NameSet_empty;
v___x_1340_ = lean_array_get_size(v_depConfigs_1338_);
v___x_1341_ = lean_nat_dec_lt(v___x_1290_, v___x_1340_);
if (v___x_1341_ == 0)
{
v___y_1296_ = v___x_1339_;
goto v___jp_1295_;
}
else
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_nat_dec_le(v___x_1340_, v___x_1340_);
if (v___x_1342_ == 0)
{
if (v___x_1341_ == 0)
{
v___y_1296_ = v___x_1339_;
goto v___jp_1295_;
}
else
{
size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; 
v___x_1343_ = ((size_t)0ULL);
v___x_1344_ = lean_usize_of_nat(v___x_1340_);
v___x_1345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_1338_, v___x_1343_, v___x_1344_, v___x_1339_);
v___y_1296_ = v___x_1345_;
goto v___jp_1295_;
}
}
else
{
size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = lean_usize_of_nat(v___x_1340_);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_1338_, v___x_1346_, v___x_1347_, v___x_1339_);
v___y_1296_ = v___x_1348_;
goto v___jp_1295_;
}
}
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___y_1292_);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
v___jp_1295_:
{
size_t v_sz_1297_; size_t v___x_1298_; lean_object* v___x_1299_; 
v_sz_1297_ = lean_array_size(v_entries_1291_);
v___x_1298_ = ((size_t)0ULL);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_entries_1291_, v_sz_1297_, v___x_1298_, v___y_1296_, v___y_1292_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v_fst_1301_; lean_object* v_snd_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v_fst_1301_ = lean_ctor_get(v_a_1300_, 0);
lean_inc(v_fst_1301_);
v_snd_1302_ = lean_ctor_get(v_a_1300_, 1);
lean_inc(v_snd_1302_);
lean_dec(v_a_1300_);
v___x_1303_ = lean_box(0);
v___x_1304_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1301_, v___x_1303_, v_toUpdate_1288_, v_snd_1302_, v___y_1293_);
lean_dec(v_fst_1301_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1321_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1321_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1321_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_snd_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1319_; 
v_snd_1309_ = lean_ctor_get(v_a_1305_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_a_1305_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v_a_1305_, 0);
lean_dec(v_unused_1320_);
v___x_1311_ = v_a_1305_;
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_snd_1309_);
lean_dec(v_a_1305_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1303_);
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_snd_1309_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1314_);
v___x_1316_ = v___x_1307_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
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
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
v_a_1322_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1304_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1304_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_toUpdate_1288_);
v_a_1330_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1299_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1299_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toUpdate_1288_ = stack[0].m_obj;
lean_object* v___x_1289_ = stack[1].m_obj;
lean_object* v___x_1290_ = stack[2].m_obj;
lean_object* v_entries_1291_ = stack[3].m_obj;
lean_object* v___y_1292_ = stack[4].m_obj;
lean_object* v___y_1293_ = stack[5].m_obj;
lean_object* v_res_1352_;
v_res_1352_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1288_, v___x_1289_, v___x_1290_, v_entries_1291_, v___y_1292_, v___y_1293_);
stack->m_obj
 = v_res_1352_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0___boxed(lean_object* v_toUpdate_1353_, lean_object* v___x_1354_, lean_object* v___x_1355_, lean_object* v_entries_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1353_, v___x_1354_, v___x_1355_, v_entries_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v_entries_1356_);
lean_dec(v___x_1355_);
lean_dec_ref(v___x_1354_);
return v_res_1360_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(lean_object* v_as_1361_, size_t v_i_1362_, size_t v_stop_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_){
_start:
{
uint8_t v___x_1367_; 
v___x_1367_ = lean_usize_dec_eq(v_i_1362_, v_stop_1363_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; 
v___x_1368_ = lean_array_uget_borrowed(v_as_1361_, v_i_1362_);
lean_inc_ref(v___y_1365_);
lean_inc(v___x_1368_);
v___x_1369_ = lean_apply_2(v___y_1365_, v___x_1368_, lean_box(0));
v___x_1370_ = ((size_t)1ULL);
v___x_1371_ = lean_usize_add(v_i_1362_, v___x_1370_);
v_i_1362_ = v___x_1371_;
v_b_1364_ = v___x_1369_;
goto _start;
}
else
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_b_1364_);
return v___x_1373_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1361_ = stack[0].m_obj;
size_t v_i_1362_ = stack[1].m_num;
size_t v_stop_1363_ = stack[2].m_num;
lean_object* v_b_1364_ = stack[3].m_obj;
lean_object* v___y_1365_ = stack[4].m_obj;
lean_object* v_res_1374_;
v_res_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_as_1361_, v_i_1362_, v_stop_1363_, v_b_1364_, v___y_1365_);
stack->m_obj
 = v_res_1374_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3___boxed(lean_object* v_as_1375_, lean_object* v_i_1376_, lean_object* v_stop_1377_, lean_object* v_b_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
size_t v_i_boxed_1381_; size_t v_stop_boxed_1382_; lean_object* v_res_1383_; 
v_i_boxed_1381_ = lean_unbox_usize(v_i_1376_);
lean_dec(v_i_1376_);
v_stop_boxed_1382_ = lean_unbox_usize(v_stop_1377_);
lean_dec(v_stop_1377_);
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_as_1375_, v_i_boxed_1381_, v_stop_boxed_1382_, v_b_1378_, v___y_1379_);
lean_dec_ref(v___y_1379_);
lean_dec_ref(v_as_1375_);
return v_res_1383_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(lean_object* v_toUpdate_1384_, lean_object* v_as_1385_, size_t v_i_1386_, size_t v_stop_1387_, lean_object* v_b_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_fst_1392_; lean_object* v_snd_1393_; uint8_t v___x_1399_; 
v___x_1399_ = lean_usize_dec_eq(v_i_1386_, v_stop_1387_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; uint8_t v_inherited_1401_; 
v___x_1400_ = lean_array_uget_borrowed(v_as_1385_, v_i_1386_);
v_inherited_1401_ = lean_ctor_get_uint8(v___x_1400_, sizeof(void*)*5);
if (v_inherited_1401_ == 0)
{
lean_object* v_name_1402_; uint8_t v___x_1403_; 
v_name_1402_ = lean_ctor_get(v___x_1400_, 0);
v___x_1403_ = l_Lean_NameSet_contains(v_toUpdate_1384_, v_name_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_box(0);
lean_inc(v___x_1400_);
lean_inc(v_name_1402_);
v___x_1405_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1402_, v___x_1400_, v___y_1389_);
v_fst_1392_ = v___x_1404_;
v_snd_1393_ = v___x_1405_;
goto v___jp_1391_;
}
else
{
goto v___jp_1397_;
}
}
else
{
goto v___jp_1397_;
}
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_b_1388_);
lean_ctor_set(v___x_1406_, 1, v___y_1389_);
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
v___jp_1391_:
{
size_t v___x_1394_; size_t v___x_1395_; 
v___x_1394_ = ((size_t)1ULL);
v___x_1395_ = lean_usize_add(v_i_1386_, v___x_1394_);
v_i_1386_ = v___x_1395_;
v_b_1388_ = v_fst_1392_;
v___y_1389_ = v_snd_1393_;
goto _start;
}
v___jp_1397_:
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_box(0);
v_fst_1392_ = v___x_1398_;
v_snd_1393_ = v___y_1389_;
goto v___jp_1391_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_toUpdate_1384_ = stack[0].m_obj;
lean_object* v_as_1385_ = stack[1].m_obj;
size_t v_i_1386_ = stack[2].m_num;
size_t v_stop_1387_ = stack[3].m_num;
lean_object* v_b_1388_ = stack[4].m_obj;
lean_object* v___y_1389_ = stack[5].m_obj;
lean_object* v_res_1408_;
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1384_, v_as_1385_, v_i_1386_, v_stop_1387_, v_b_1388_, v___y_1389_);
stack->m_obj
 = v_res_1408_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg___boxed(lean_object* v_toUpdate_1409_, lean_object* v_as_1410_, lean_object* v_i_1411_, lean_object* v_stop_1412_, lean_object* v_b_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
size_t v_i_boxed_1416_; size_t v_stop_boxed_1417_; lean_object* v_res_1418_; 
v_i_boxed_1416_ = lean_unbox_usize(v_i_1411_);
lean_dec(v_i_1411_);
v_stop_boxed_1417_ = lean_unbox_usize(v_stop_1412_);
lean_dec(v_stop_1412_);
v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1409_, v_as_1410_, v_i_boxed_1416_, v_stop_boxed_1417_, v_b_1413_, v___y_1414_);
lean_dec_ref(v_as_1410_);
lean_dec(v_toUpdate_1409_);
return v_res_1418_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1426_ = lean_array_get_size(v___x_1425_);
return v___x_1426_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = lean_nat_dec_lt(v___x_1428_, v___x_1427_);
return v___x_1429_;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7(void){
_start:
{
lean_object* v___x_1430_; size_t v___x_1431_; 
v___x_1430_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1431_ = lean_usize_of_nat(v___x_1430_);
return v___x_1431_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* v_ws_1434_, lean_object* v_toUpdate_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___y_1440_; lean_object* v___y_1445_; lean_object* v_fst_1446_; lean_object* v_snd_1447_; lean_object* v_packages_1466_; lean_object* v___x_1467_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v_val_1472_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___x_1508_; lean_object* v_baseName_1509_; lean_object* v_dir_1510_; lean_object* v_config_1511_; lean_object* v_relManifestFile_1512_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; uint8_t v_fst_1517_; lean_object* v_snd_1518_; lean_object* v_packagesDir_x3f_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1563_; lean_object* v___y_1564_; uint8_t v___x_1568_; lean_object* v_rootName_1569_; lean_object* v_fst_1571_; lean_object* v_snd_1572_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_val_1641_; lean_object* v___x_1655_; 
v_packages_1466_ = lean_ctor_get(v_ws_1434_, 4);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_array_fget_borrowed(v_packages_1466_, v___x_1467_);
v_baseName_1509_ = lean_ctor_get(v___x_1508_, 1);
v_dir_1510_ = lean_ctor_get(v___x_1508_, 4);
v_config_1511_ = lean_ctor_get(v___x_1508_, 6);
v_relManifestFile_1512_ = lean_ctor_get(v___x_1508_, 9);
v___x_1568_ = 0;
lean_inc(v_baseName_1509_);
v_rootName_1569_ = l_Lean_Name_toString(v_baseName_1509_, v___x_1568_);
lean_inc_ref(v_relManifestFile_1512_);
lean_inc_ref(v_dir_1510_);
v___x_1638_ = l_Lake_joinRelative(v_dir_1510_, v_relManifestFile_1512_);
v___x_1639_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1655_ = l_Lake_Manifest_load(v___x_1638_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 1);
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
v_val_1641_ = v___x_1661_;
goto v___jp_1640_;
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_a_1664_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1655_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1655_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set_tag(v___x_1666_, 0);
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
v_val_1641_ = v___x_1669_;
goto v___jp_1640_;
}
}
}
v___jp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v___y_1440_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
v___jp_1444_:
{
if (lean_obj_tag(v_fst_1446_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_snd_1447_);
v_a_1448_ = lean_ctor_get(v_fst_1446_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_fst_1446_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1450_ = v_fst_1446_;
v_isShared_1451_ = v_isSharedCheck_1462_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v_fst_1446_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1462_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1452_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_1453_ = lean_io_error_to_string(v_a_1448_);
v___x_1454_ = lean_string_append(v___x_1452_, v___x_1453_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = 3;
v___x_1456_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*1, v___x_1455_);
lean_inc_ref(v___y_1445_);
v___x_1457_ = lean_apply_2(v___y_1445_, v___x_1456_, lean_box(0));
v___x_1458_ = lean_box(0);
if (v_isShared_1451_ == 0)
{
lean_ctor_set_tag(v___x_1450_, 1);
lean_ctor_set(v___x_1450_, 0, v___x_1458_);
v___x_1460_ = v___x_1450_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec_ref(v_fst_1446_);
v___x_1463_ = lean_box(0);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
lean_ctor_set(v___x_1464_, 1, v_snd_1447_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
}
v___jp_1468_:
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = lean_array_get_size(v___y_1470_);
v___x_1474_ = lean_nat_dec_lt(v___x_1467_, v___x_1473_);
if (v___x_1474_ == 0)
{
v___y_1445_ = v___y_1471_;
v_fst_1446_ = v_val_1472_;
v_snd_1447_ = v___y_1469_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1475_; size_t v___x_1476_; size_t v___x_1477_; lean_object* v___x_1478_; 
v___x_1475_ = lean_box(0);
v___x_1476_ = ((size_t)0ULL);
v___x_1477_ = lean_usize_of_nat(v___x_1473_);
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1470_, v___x_1476_, v___x_1477_, v___x_1475_, v___y_1471_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_dec_ref_known(v___x_1478_, 1);
v___y_1445_ = v___y_1471_;
v_fst_1446_ = v_val_1472_;
v_snd_1447_ = v___y_1469_;
goto v___jp_1444_;
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_val_1472_);
lean_dec(v___y_1469_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
v___jp_1487_:
{
if (lean_obj_tag(v___y_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
v_a_1492_ = lean_ctor_get(v___y_1491_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___y_1491_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___y_1491_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___y_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 1);
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
v___y_1469_ = v___y_1489_;
v___y_1470_ = v___y_1488_;
v___y_1471_ = v___y_1490_;
v_val_1472_ = v___x_1497_;
goto v___jp_1468_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_a_1500_ = lean_ctor_get(v___y_1491_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___y_1491_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___y_1491_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___y_1491_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 0);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
v___y_1469_ = v___y_1489_;
v___y_1470_ = v___y_1488_;
v___y_1471_ = v___y_1490_;
v_val_1472_ = v___x_1505_;
goto v___jp_1468_;
}
}
}
}
v___jp_1513_:
{
lean_object* v_toWorkspaceConfig_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_toWorkspaceConfig_1519_ = lean_ctor_get(v_config_1511_, 0);
v___x_1520_ = l_System_FilePath_normalize(v___y_1516_);
lean_inc_ref(v_toWorkspaceConfig_1519_);
v___x_1521_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1519_);
lean_inc_ref(v___x_1521_);
v___x_1522_ = l_System_FilePath_normalize(v___x_1521_);
v___x_1523_ = lean_string_dec_eq(v___x_1520_, v___x_1522_);
lean_dec_ref(v___x_1522_);
lean_dec_ref(v___x_1520_);
if (v___x_1523_ == 0)
{
if (v_fst_1517_ == 0)
{
lean_dec_ref(v___x_1521_);
lean_dec_ref(v___y_1515_);
v___y_1440_ = v_snd_1518_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1524_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_1525_ = lean_string_append(v___x_1524_, v___y_1515_);
v___x_1526_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_1527_ = lean_string_append(v___x_1525_, v___x_1526_);
lean_inc_ref(v_dir_1510_);
v___x_1528_ = l_Lake_joinRelative(v_dir_1510_, v___x_1521_);
v___x_1529_ = lean_string_append(v___x_1527_, v___x_1528_);
v___x_1530_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1531_ = lean_string_append(v___x_1529_, v___x_1530_);
v___x_1532_ = 1;
v___x_1533_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set_uint8(v___x_1533_, sizeof(void*)*1, v___x_1532_);
lean_inc_ref(v___y_1514_);
v___x_1534_ = lean_apply_2(v___y_1514_, v___x_1533_, lean_box(0));
v___x_1535_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_1528_);
v___x_1536_ = l_Lake_createParentDirs(v___x_1528_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v___x_1537_; 
lean_dec_ref_known(v___x_1536_, 1);
v___x_1537_ = lean_io_rename(v___y_1515_, v___x_1528_);
lean_dec_ref(v___x_1528_);
lean_dec_ref(v___y_1515_);
v___y_1488_ = v___x_1535_;
v___y_1489_ = v_snd_1518_;
v___y_1490_ = v___y_1514_;
v___y_1491_ = v___x_1537_;
goto v___jp_1487_;
}
else
{
lean_dec_ref(v___x_1528_);
lean_dec_ref(v___y_1515_);
v___y_1488_ = v___x_1535_;
v___y_1489_ = v_snd_1518_;
v___y_1490_ = v___y_1514_;
v___y_1491_ = v___x_1536_;
goto v___jp_1487_;
}
}
}
else
{
lean_dec_ref(v___x_1521_);
lean_dec_ref(v___y_1515_);
v___y_1440_ = v_snd_1518_;
goto v___jp_1439_;
}
}
v___jp_1538_:
{
if (lean_obj_tag(v_packagesDir_x3f_1539_) == 1)
{
lean_object* v_val_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; uint8_t v___x_1546_; 
v_val_1542_ = lean_ctor_get(v_packagesDir_x3f_1539_, 0);
lean_inc_n(v_val_1542_, 2);
lean_dec_ref_known(v_packagesDir_x3f_1539_, 1);
lean_inc_ref(v_dir_1510_);
v___x_1543_ = l_Lake_joinRelative(v_dir_1510_, v_val_1542_);
v___x_1544_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1545_ = l_System_FilePath_pathExists(v___x_1543_);
v___x_1546_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1546_ == 0)
{
v___y_1514_ = v___y_1541_;
v___y_1515_ = v___x_1543_;
v___y_1516_ = v_val_1542_;
v_fst_1517_ = v___x_1545_;
v_snd_1518_ = v___y_1540_;
goto v___jp_1513_;
}
else
{
lean_object* v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
v___x_1547_ = lean_box(0);
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1544_, v___x_1548_, v___x_1549_, v___x_1547_, v___y_1541_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_dec_ref_known(v___x_1550_, 1);
v___y_1514_ = v___y_1541_;
v___y_1515_ = v___x_1543_;
v___y_1516_ = v_val_1542_;
v_fst_1517_ = v___x_1545_;
v_snd_1518_ = v___y_1540_;
goto v___jp_1513_;
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v___x_1543_);
lean_dec(v_val_1542_);
lean_dec(v___y_1540_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_packagesDir_x3f_1539_);
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v___y_1540_);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
}
v___jp_1562_:
{
if (lean_obj_tag(v___y_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v_snd_1566_; lean_object* v_packagesDir_x3f_1567_; 
v_a_1565_ = lean_ctor_get(v___y_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___y_1564_, 1);
v_snd_1566_ = lean_ctor_get(v_a_1565_, 1);
lean_inc(v_snd_1566_);
lean_dec(v_a_1565_);
v_packagesDir_x3f_1567_ = lean_ctor_get(v___y_1563_, 2);
lean_inc(v_packagesDir_x3f_1567_);
lean_dec_ref(v___y_1563_);
v_packagesDir_x3f_1539_ = v_packagesDir_x3f_1567_;
v___y_1540_ = v_snd_1566_;
v___y_1541_ = v_a_1437_;
goto v___jp_1538_;
}
else
{
lean_dec_ref(v___y_1563_);
return v___y_1564_;
}
}
v___jp_1570_:
{
if (lean_obj_tag(v_fst_1571_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1620_; 
v_a_1573_ = lean_ctor_get(v_fst_1571_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_fst_1571_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1575_ = v_fst_1571_;
v_isShared_1576_ = v_isSharedCheck_1620_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v_fst_1571_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1620_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
if (lean_obj_tag(v_a_1573_) == 11)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec_ref_known(v_a_1573_, 2);
lean_del_object(v___x_1575_);
v___x_1577_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_1578_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1435_, v___x_1508_, v___x_1467_, v___x_1577_, v_snd_1572_, v_a_1437_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1600_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1600_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1600_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v_snd_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1598_; 
v_snd_1583_ = lean_ctor_get(v_a_1579_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_a_1579_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v_a_1579_, 0);
lean_dec(v_unused_1599_);
v___x_1585_ = v_a_1579_;
v_isShared_1586_ = v_isSharedCheck_1598_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_snd_1583_);
lean_dec(v_a_1579_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1598_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1587_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8));
v___x_1588_ = lean_string_append(v_rootName_1569_, v___x_1587_);
v___x_1589_ = 1;
v___x_1590_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*1, v___x_1589_);
lean_inc_ref(v_a_1437_);
v___x_1591_ = lean_apply_2(v_a_1437_, v___x_1590_, lean_box(0));
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1591_);
v___x_1593_ = v___x_1585_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_snd_1583_);
v___x_1593_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1595_; 
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1593_);
v___x_1595_ = v___x_1581_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_1569_);
return v___x_1578_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_1435_) == 0)
{
lean_object* v___x_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
lean_dec_ref_known(v_toUpdate_1435_, 5);
lean_dec(v_snd_1572_);
lean_dec_ref(v_rootName_1569_);
v___x_1601_ = lean_io_error_to_string(v_a_1573_);
v___x_1602_ = 3;
v___x_1603_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*1, v___x_1602_);
lean_inc_ref(v_a_1437_);
v___x_1604_ = lean_apply_2(v_a_1437_, v___x_1603_, lean_box(0));
v___x_1605_ = lean_box(0);
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 1);
lean_ctor_set(v___x_1575_, 0, v___x_1605_);
v___x_1607_ = v___x_1575_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1609_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_1610_ = lean_string_append(v_rootName_1569_, v___x_1609_);
v___x_1611_ = lean_io_error_to_string(v_a_1573_);
v___x_1612_ = lean_string_append(v___x_1610_, v___x_1611_);
lean_dec_ref(v___x_1611_);
v___x_1613_ = 2;
v___x_1614_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set_uint8(v___x_1614_, sizeof(void*)*1, v___x_1613_);
lean_inc_ref(v_a_1437_);
v___x_1615_ = lean_apply_2(v_a_1437_, v___x_1614_, lean_box(0));
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v_snd_1572_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1616_);
v___x_1618_ = v___x_1575_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v_packagesDir_x3f_1622_; lean_object* v_packages_1623_; lean_object* v___x_1624_; 
lean_dec_ref(v_rootName_1569_);
v_a_1621_ = lean_ctor_get(v_fst_1571_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v_fst_1571_, 1);
v_packagesDir_x3f_1622_ = lean_ctor_get(v_a_1621_, 2);
v_packages_1623_ = lean_ctor_get(v_a_1621_, 3);
lean_inc(v_toUpdate_1435_);
v___x_1624_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1435_, v___x_1508_, v___x_1467_, v_packages_1623_, v_snd_1572_, v_a_1437_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
if (lean_obj_tag(v_toUpdate_1435_) == 0)
{
lean_object* v_snd_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v_snd_1626_ = lean_ctor_get(v_a_1625_, 1);
lean_inc(v_snd_1626_);
lean_dec(v_a_1625_);
v___x_1627_ = lean_array_get_size(v_packages_1623_);
v___x_1628_ = lean_nat_dec_lt(v___x_1467_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_inc(v_packagesDir_x3f_1622_);
lean_dec_ref_known(v_toUpdate_1435_, 5);
lean_dec(v_a_1621_);
v_packagesDir_x3f_1539_ = v_packagesDir_x3f_1622_;
v___y_1540_ = v_snd_1626_;
v___y_1541_ = v_a_1437_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_nat_dec_le(v___x_1627_, v___x_1627_);
if (v___x_1630_ == 0)
{
if (v___x_1628_ == 0)
{
lean_inc(v_packagesDir_x3f_1622_);
lean_dec_ref_known(v_toUpdate_1435_, 5);
lean_dec(v_a_1621_);
v_packagesDir_x3f_1539_ = v_packagesDir_x3f_1622_;
v___y_1540_ = v_snd_1626_;
v___y_1541_ = v_a_1437_;
goto v___jp_1538_;
}
else
{
size_t v___x_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = lean_usize_of_nat(v___x_1627_);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1435_, v_packages_1623_, v___x_1631_, v___x_1632_, v___x_1629_, v_snd_1626_);
lean_dec_ref_known(v_toUpdate_1435_, 5);
v___y_1563_ = v_a_1621_;
v___y_1564_ = v___x_1633_;
goto v___jp_1562_;
}
}
else
{
size_t v___x_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = ((size_t)0ULL);
v___x_1635_ = lean_usize_of_nat(v___x_1627_);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1435_, v_packages_1623_, v___x_1634_, v___x_1635_, v___x_1629_, v_snd_1626_);
lean_dec_ref_known(v_toUpdate_1435_, 5);
v___y_1563_ = v_a_1621_;
v___y_1564_ = v___x_1636_;
goto v___jp_1562_;
}
}
}
else
{
lean_object* v_snd_1637_; 
lean_inc(v_packagesDir_x3f_1622_);
lean_dec(v_a_1621_);
v_snd_1637_ = lean_ctor_get(v_a_1625_, 1);
lean_inc(v_snd_1637_);
lean_dec(v_a_1625_);
v_packagesDir_x3f_1539_ = v_packagesDir_x3f_1622_;
v___y_1540_ = v_snd_1637_;
v___y_1541_ = v_a_1437_;
goto v___jp_1538_;
}
}
else
{
lean_dec(v_a_1621_);
lean_dec(v_toUpdate_1435_);
return v___x_1624_;
}
}
}
v___jp_1640_:
{
uint8_t v___x_1642_; 
v___x_1642_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1642_ == 0)
{
v_fst_1571_ = v_val_1641_;
v_snd_1572_ = v_a_1436_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1643_; size_t v___x_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
v___x_1643_ = lean_box(0);
v___x_1644_ = ((size_t)0ULL);
v___x_1645_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1639_, v___x_1644_, v___x_1645_, v___x_1643_, v_a_1437_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_dec_ref_known(v___x_1646_, 1);
v_fst_1571_ = v_val_1641_;
v_snd_1572_ = v_a_1436_;
goto v___jp_1570_;
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref(v_val_1641_);
lean_dec_ref(v_rootName_1569_);
lean_dec(v_a_1436_);
lean_dec(v_toUpdate_1435_);
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_reuseManifest_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_1434_ = stack[0].m_obj;
lean_object* v_toUpdate_1435_ = stack[1].m_obj;
lean_object* v_a_1436_ = stack[2].m_obj;
lean_object* v_a_1437_ = stack[3].m_obj;
lean_object* v_res_1672_;
v_res_1672_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1434_, v_toUpdate_1435_, v_a_1436_, v_a_1437_);
stack->m_obj
 = v_res_1672_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_1673_, lean_object* v_toUpdate_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1673_, v_toUpdate_1674_, v_a_1675_, v_a_1676_);
lean_dec_ref(v_a_1676_);
lean_dec_ref(v_ws_1673_);
return v_res_1678_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* v_as_1679_, size_t v_sz_1680_, size_t v_i_1681_, lean_object* v_b_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1679_, v_sz_1680_, v_i_1681_, v_b_1682_, v___y_1683_);
return v___x_1686_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1679_ = stack[0].m_obj;
size_t v_sz_1680_ = stack[1].m_num;
size_t v_i_1681_ = stack[2].m_num;
lean_object* v_b_1682_ = stack[3].m_obj;
lean_object* v___y_1683_ = stack[4].m_obj;
lean_object* v___y_1684_ = stack[5].m_obj;
lean_object* v_res_1687_;
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_1679_, v_sz_1680_, v_i_1681_, v_b_1682_, v___y_1683_, v___y_1684_);
stack->m_obj
 = v_res_1687_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* v_as_1688_, lean_object* v_sz_1689_, lean_object* v_i_1690_, lean_object* v_b_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
size_t v_sz_boxed_1695_; size_t v_i_boxed_1696_; lean_object* v_res_1697_; 
v_sz_boxed_1695_ = lean_unbox_usize(v_sz_1689_);
lean_dec(v_sz_1689_);
v_i_boxed_1696_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_res_1697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_1688_, v_sz_boxed_1695_, v_i_boxed_1696_, v_b_1691_, v___y_1692_, v___y_1693_);
lean_dec_ref(v___y_1693_);
lean_dec_ref(v_as_1688_);
return v_res_1697_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(lean_object* v_toUpdate_1698_, lean_object* v_as_1699_, size_t v_i_1700_, size_t v_stop_1701_, lean_object* v_b_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1698_, v_as_1699_, v_i_1700_, v_stop_1701_, v_b_1702_, v___y_1703_);
return v___x_1706_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_toUpdate_1698_ = stack[0].m_obj;
lean_object* v_as_1699_ = stack[1].m_obj;
size_t v_i_1700_ = stack[2].m_num;
size_t v_stop_1701_ = stack[3].m_num;
lean_object* v_b_1702_ = stack[4].m_obj;
lean_object* v___y_1703_ = stack[5].m_obj;
lean_object* v___y_1704_ = stack[6].m_obj;
lean_object* v_res_1707_;
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(v_toUpdate_1698_, v_as_1699_, v_i_1700_, v_stop_1701_, v_b_1702_, v___y_1703_, v___y_1704_);
stack->m_obj
 = v_res_1707_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___boxed(lean_object* v_toUpdate_1708_, lean_object* v_as_1709_, lean_object* v_i_1710_, lean_object* v_stop_1711_, lean_object* v_b_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
size_t v_i_boxed_1716_; size_t v_stop_boxed_1717_; lean_object* v_res_1718_; 
v_i_boxed_1716_ = lean_unbox_usize(v_i_1710_);
lean_dec(v_i_1710_);
v_stop_boxed_1717_ = lean_unbox_usize(v_stop_1711_);
lean_dec(v_stop_1711_);
v_res_1718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(v_toUpdate_1708_, v_as_1709_, v_i_boxed_1716_, v_stop_boxed_1717_, v_b_1712_, v___y_1713_, v___y_1714_);
lean_dec_ref(v___y_1714_);
lean_dec_ref(v_as_1709_);
lean_dec(v_toUpdate_1708_);
return v_res_1718_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_dep_1719_, lean_object* v_as_1720_, size_t v_i_1721_, size_t v_stop_1722_, lean_object* v_b_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_fst_1727_; lean_object* v_snd_1728_; lean_object* v___y_1733_; lean_object* v_name_1734_; uint8_t v___x_1737_; 
v___x_1737_ = lean_usize_dec_eq(v_i_1721_, v_stop_1722_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v_name_1739_; lean_object* v_scope_1740_; lean_object* v_configFile_1741_; lean_object* v_manifestFile_x3f_1742_; lean_object* v_src_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1770_; 
v___x_1738_ = lean_array_uget(v_as_1720_, v_i_1721_);
v_name_1739_ = lean_ctor_get(v___x_1738_, 0);
v_scope_1740_ = lean_ctor_get(v___x_1738_, 1);
v_configFile_1741_ = lean_ctor_get(v___x_1738_, 2);
v_manifestFile_x3f_1742_ = lean_ctor_get(v___x_1738_, 3);
v_src_1743_ = lean_ctor_get(v___x_1738_, 4);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1745_ = v___x_1738_;
v_isShared_1746_ = v_isSharedCheck_1770_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_src_1743_);
lean_inc(v_manifestFile_x3f_1742_);
lean_inc(v_configFile_1741_);
lean_inc(v_scope_1740_);
lean_inc(v_name_1739_);
lean_dec(v___x_1738_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1770_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
uint8_t v___x_1747_; 
v___x_1747_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1739_, v___y_1724_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; 
v___x_1748_ = 1;
if (lean_obj_tag(v_src_1743_) == 0)
{
uint8_t v_copy_1749_; 
v_copy_1749_ = lean_ctor_get_uint8(v_src_1743_, sizeof(void*)*1);
if (v_copy_1749_ == 0)
{
lean_object* v_dir_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1762_; 
v_dir_1750_ = lean_ctor_get(v_src_1743_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_src_1743_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1752_ = v_src_1743_;
v_isShared_1753_ = v_isSharedCheck_1762_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_dir_1750_);
lean_dec(v_src_1743_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1762_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v_relPkgDir_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v_relPkgDir_1754_ = lean_ctor_get(v_dep_1719_, 1);
lean_inc_ref(v_relPkgDir_1754_);
v___x_1755_ = l_Lake_joinRelative(v_relPkgDir_1754_, v_dir_1750_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1755_);
lean_ctor_set_uint8(v_reuseFailAlloc_1761_, sizeof(void*)*1, v_copy_1749_);
v___x_1757_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1759_; 
lean_inc(v_name_1739_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 4, v___x_1757_);
v___x_1759_ = v___x_1745_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_name_1739_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_scope_1740_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_configFile_1741_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_manifestFile_x3f_1742_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*5, v___x_1748_);
v___y_1733_ = v___x_1759_;
v_name_1734_ = v_name_1739_;
goto v___jp_1732_;
}
}
}
}
else
{
lean_object* v___x_1764_; 
lean_inc(v_name_1739_);
if (v_isShared_1746_ == 0)
{
v___x_1764_ = v___x_1745_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_name_1739_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_scope_1740_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_configFile_1741_);
lean_ctor_set(v_reuseFailAlloc_1765_, 3, v_manifestFile_x3f_1742_);
lean_ctor_set(v_reuseFailAlloc_1765_, 4, v_src_1743_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_ctor_set_uint8(v___x_1764_, sizeof(void*)*5, v___x_1748_);
v___y_1733_ = v___x_1764_;
v_name_1734_ = v_name_1739_;
goto v___jp_1732_;
}
}
}
else
{
lean_object* v___x_1767_; 
lean_inc(v_name_1739_);
if (v_isShared_1746_ == 0)
{
v___x_1767_ = v___x_1745_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_name_1739_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_scope_1740_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_configFile_1741_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_manifestFile_x3f_1742_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_src_1743_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*5, v___x_1748_);
v___y_1733_ = v___x_1767_;
v_name_1734_ = v_name_1739_;
goto v___jp_1732_;
}
}
}
else
{
lean_object* v___x_1769_; 
lean_del_object(v___x_1745_);
lean_dec_ref(v_src_1743_);
lean_dec(v_manifestFile_x3f_1742_);
lean_dec_ref(v_configFile_1741_);
lean_dec_ref(v_scope_1740_);
lean_dec(v_name_1739_);
v___x_1769_ = lean_box(0);
v_fst_1727_ = v___x_1769_;
v_snd_1728_ = v___y_1724_;
goto v___jp_1726_;
}
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec_ref(v_dep_1719_);
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v_b_1723_);
lean_ctor_set(v___x_1771_, 1, v___y_1724_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
v___jp_1726_:
{
size_t v___x_1729_; size_t v___x_1730_; 
v___x_1729_ = ((size_t)1ULL);
v___x_1730_ = lean_usize_add(v_i_1721_, v___x_1729_);
v_i_1721_ = v___x_1730_;
v_b_1723_ = v_fst_1727_;
v___y_1724_ = v_snd_1728_;
goto _start;
}
v___jp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = lean_box(0);
v___x_1736_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1734_, v___y_1733_, v___y_1724_);
v_fst_1727_ = v___x_1735_;
v_snd_1728_ = v___x_1736_;
goto v___jp_1726_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_dep_1719_ = stack[0].m_obj;
lean_object* v_as_1720_ = stack[1].m_obj;
size_t v_i_1721_ = stack[2].m_num;
size_t v_stop_1722_ = stack[3].m_num;
lean_object* v_b_1723_ = stack[4].m_obj;
lean_object* v___y_1724_ = stack[5].m_obj;
lean_object* v_res_1773_;
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1719_, v_as_1720_, v_i_1721_, v_stop_1722_, v_b_1723_, v___y_1724_);
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1774_, lean_object* v_as_1775_, lean_object* v_i_1776_, lean_object* v_stop_1777_, lean_object* v_b_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
size_t v_i_boxed_1781_; size_t v_stop_boxed_1782_; lean_object* v_res_1783_; 
v_i_boxed_1781_ = lean_unbox_usize(v_i_1776_);
lean_dec(v_i_1776_);
v_stop_boxed_1782_ = lean_unbox_usize(v_stop_1777_);
lean_dec(v_stop_1777_);
v_res_1783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1774_, v_as_1775_, v_i_boxed_1781_, v_stop_boxed_1782_, v_b_1778_, v___y_1779_);
lean_dec_ref(v_as_1775_);
return v_res_1783_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_manifestEntry_1790_; lean_object* v_pkgDir_1791_; lean_object* v_name_1792_; lean_object* v_manifestFile_x3f_1793_; lean_object* v___y_1795_; lean_object* v_fst_1796_; lean_object* v_snd_1797_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v_val_1857_; lean_object* v___y_1873_; 
v_manifestEntry_1790_ = lean_ctor_get(v_dep_1786_, 4);
v_pkgDir_1791_ = lean_ctor_get(v_dep_1786_, 0);
v_name_1792_ = lean_ctor_get(v_manifestEntry_1790_, 0);
v_manifestFile_x3f_1793_ = lean_ctor_get(v_manifestEntry_1790_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1793_) == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1791_);
v___x_1894_ = l_Lake_joinRelative(v_pkgDir_1791_, v___x_1893_);
v___y_1873_ = v___x_1894_;
goto v___jp_1872_;
}
else
{
lean_object* v_val_1895_; lean_object* v___x_1896_; 
v_val_1895_ = lean_ctor_get(v_manifestFile_x3f_1793_, 0);
lean_inc(v_val_1895_);
lean_inc_ref(v_pkgDir_1791_);
v___x_1896_ = l_Lake_joinRelative(v_pkgDir_1791_, v_val_1895_);
v___y_1873_ = v___x_1896_;
goto v___jp_1872_;
}
v___jp_1794_:
{
if (lean_obj_tag(v_fst_1796_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1827_; 
lean_inc(v_name_1792_);
lean_dec_ref(v_dep_1786_);
v_a_1798_ = lean_ctor_get(v_fst_1796_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_fst_1796_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1800_ = v_fst_1796_;
v_isShared_1801_ = v_isSharedCheck_1827_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v_fst_1796_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1827_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
if (lean_obj_tag(v_a_1798_) == 11)
{
uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1812_; 
lean_dec_ref_known(v_a_1798_, 2);
v___x_1802_ = 0;
v___x_1803_ = l_Lean_Name_toString(v_name_1792_, v___x_1802_);
v___x_1804_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1805_ = lean_string_append(v___x_1803_, v___x_1804_);
v___x_1806_ = lean_string_append(v___x_1805_, v___y_1795_);
lean_dec_ref(v___y_1795_);
v___x_1807_ = 2;
v___x_1808_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set_uint8(v___x_1808_, sizeof(void*)*1, v___x_1807_);
lean_inc_ref(v_a_1788_);
v___x_1809_ = lean_apply_2(v_a_1788_, v___x_1808_, lean_box(0));
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v_snd_1797_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1810_);
v___x_1812_ = v___x_1800_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
else
{
uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_dec_ref(v___y_1795_);
v___x_1814_ = 0;
v___x_1815_ = l_Lean_Name_toString(v_name_1792_, v___x_1814_);
v___x_1816_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1817_ = lean_string_append(v___x_1815_, v___x_1816_);
v___x_1818_ = lean_io_error_to_string(v_a_1798_);
v___x_1819_ = lean_string_append(v___x_1817_, v___x_1818_);
lean_dec_ref(v___x_1818_);
v___x_1820_ = 2;
v___x_1821_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*1, v___x_1820_);
lean_inc_ref(v_a_1788_);
v___x_1822_ = lean_apply_2(v_a_1788_, v___x_1821_, lean_box(0));
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v_snd_1797_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1823_);
v___x_1825_ = v___x_1800_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v___y_1795_);
v_a_1828_ = lean_ctor_get(v_fst_1796_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_fst_1796_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1830_ = v_fst_1796_;
v_isShared_1831_ = v_isSharedCheck_1852_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v_fst_1796_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1852_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_packages_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v_packages_1832_ = lean_ctor_get(v_a_1828_, 3);
lean_inc_ref(v_packages_1832_);
lean_dec(v_a_1828_);
v___x_1833_ = lean_unsigned_to_nat(0u);
v___x_1834_ = lean_array_get_size(v_packages_1832_);
v___x_1835_ = lean_box(0);
v___x_1836_ = lean_nat_dec_lt(v___x_1833_, v___x_1834_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec_ref(v_packages_1832_);
lean_dec_ref(v_dep_1786_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v_snd_1797_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1837_);
v___x_1839_ = v___x_1830_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_nat_dec_le(v___x_1834_, v___x_1834_);
if (v___x_1841_ == 0)
{
if (v___x_1836_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
lean_dec_ref(v_packages_1832_);
lean_dec_ref(v_dep_1786_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1835_);
lean_ctor_set(v___x_1842_, 1, v_snd_1797_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1842_);
v___x_1844_ = v___x_1830_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
else
{
size_t v___x_1846_; size_t v___x_1847_; lean_object* v___x_1848_; 
lean_del_object(v___x_1830_);
v___x_1846_ = ((size_t)0ULL);
v___x_1847_ = lean_usize_of_nat(v___x_1834_);
v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1786_, v_packages_1832_, v___x_1846_, v___x_1847_, v___x_1835_, v_snd_1797_);
lean_dec_ref(v_packages_1832_);
return v___x_1848_;
}
}
else
{
size_t v___x_1849_; size_t v___x_1850_; lean_object* v___x_1851_; 
lean_del_object(v___x_1830_);
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = lean_usize_of_nat(v___x_1834_);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1786_, v_packages_1832_, v___x_1849_, v___x_1850_, v___x_1835_, v_snd_1797_);
lean_dec_ref(v_packages_1832_);
return v___x_1851_;
}
}
}
}
}
v___jp_1853_:
{
lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1858_ = lean_array_get_size(v___y_1854_);
v___x_1859_ = lean_nat_dec_lt(v___y_1856_, v___x_1858_);
if (v___x_1859_ == 0)
{
v___y_1795_ = v___y_1855_;
v_fst_1796_ = v_val_1857_;
v_snd_1797_ = v_a_1787_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = ((size_t)0ULL);
v___x_1862_ = lean_usize_of_nat(v___x_1858_);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1854_, v___x_1861_, v___x_1862_, v___x_1860_, v_a_1788_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_dec_ref_known(v___x_1863_, 1);
v___y_1795_ = v___y_1855_;
v_fst_1796_ = v_val_1857_;
v_snd_1797_ = v_a_1787_;
goto v___jp_1794_;
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec_ref(v_val_1857_);
lean_dec_ref(v___y_1855_);
lean_dec(v_a_1787_);
lean_dec_ref(v_dep_1786_);
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
v___jp_1872_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = lean_unsigned_to_nat(0u);
v___x_1875_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1873_);
v___x_1876_ = l_Lake_Manifest_load(v___y_1873_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 1);
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
v___y_1854_ = v___x_1875_;
v___y_1855_ = v___y_1873_;
v___y_1856_ = v___x_1874_;
v_val_1857_ = v___x_1882_;
goto v___jp_1853_;
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
v_a_1885_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1876_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1876_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 0);
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
v___y_1854_ = v___x_1875_;
v___y_1855_ = v___y_1873_;
v___y_1856_ = v___x_1874_;
v_val_1857_ = v___x_1890_;
goto v___jp_1853_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries_0interp(lean_interpreter_value* stack)
{
lean_object* v_dep_1786_ = stack[0].m_obj;
lean_object* v_a_1787_ = stack[1].m_obj;
lean_object* v_a_1788_ = stack[2].m_obj;
lean_object* v_res_1897_;
v_res_1897_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1786_, v_a_1787_, v_a_1788_);
stack->m_obj
 = v_res_1897_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1898_, v_a_1899_, v_a_1900_);
lean_dec_ref(v_a_1900_);
return v_res_1902_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1903_, lean_object* v_as_1904_, size_t v_i_1905_, size_t v_stop_1906_, lean_object* v_b_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1903_, v_as_1904_, v_i_1905_, v_stop_1906_, v_b_1907_, v___y_1908_);
return v___x_1911_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_dep_1903_ = stack[0].m_obj;
lean_object* v_as_1904_ = stack[1].m_obj;
size_t v_i_1905_ = stack[2].m_num;
size_t v_stop_1906_ = stack[3].m_num;
lean_object* v_b_1907_ = stack[4].m_obj;
lean_object* v___y_1908_ = stack[5].m_obj;
lean_object* v___y_1909_ = stack[6].m_obj;
lean_object* v_res_1912_;
v_res_1912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1903_, v_as_1904_, v_i_1905_, v_stop_1906_, v_b_1907_, v___y_1908_, v___y_1909_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1913_, lean_object* v_as_1914_, lean_object* v_i_1915_, lean_object* v_stop_1916_, lean_object* v_b_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
size_t v_i_boxed_1921_; size_t v_stop_boxed_1922_; lean_object* v_res_1923_; 
v_i_boxed_1921_ = lean_unbox_usize(v_i_1915_);
lean_dec(v_i_1915_);
v_stop_boxed_1922_ = lean_unbox_usize(v_stop_1916_);
lean_dec(v_stop_1916_);
v_res_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1913_, v_as_1914_, v_i_boxed_1921_, v_stop_boxed_1922_, v_b_1917_, v___y_1918_, v___y_1919_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_as_1914_);
return v_res_1923_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1925_, lean_object* v_pkg_1926_, lean_object* v_dep_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
uint8_t v___y_1932_; lean_object* v___y_1933_; lean_object* v_name_1963_; lean_object* v___x_1964_; 
v_name_1963_ = lean_ctor_get(v_dep_1927_, 0);
v___x_1964_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1928_, v_name_1963_);
if (lean_obj_tag(v___x_1964_) == 1)
{
lean_object* v_val_1965_; lean_object* v_lakeEnv_1966_; lean_object* v_packages_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v_config_1970_; lean_object* v_dir_1971_; lean_object* v_toWorkspaceConfig_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec_ref(v_dep_1927_);
lean_dec_ref(v_pkg_1926_);
v_val_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_val_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v_lakeEnv_1966_ = lean_ctor_get(v_ws_1925_, 0);
lean_inc_ref(v_lakeEnv_1966_);
v_packages_1967_ = lean_ctor_get(v_ws_1925_, 4);
lean_inc_ref(v_packages_1967_);
lean_dec_ref(v_ws_1925_);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = lean_array_fget(v_packages_1967_, v___x_1968_);
lean_dec_ref(v_packages_1967_);
v_config_1970_ = lean_ctor_get(v___x_1969_, 6);
lean_inc_ref(v_config_1970_);
v_dir_1971_ = lean_ctor_get(v___x_1969_, 4);
lean_inc_ref(v_dir_1971_);
lean_dec(v___x_1969_);
v_toWorkspaceConfig_1972_ = lean_ctor_get(v_config_1970_, 0);
lean_inc_ref(v_toWorkspaceConfig_1972_);
lean_dec_ref(v_config_1970_);
v___x_1973_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1972_);
v___x_1974_ = l_Lake_PackageEntry_materialize(v_val_1965_, v_lakeEnv_1966_, v_dir_1971_, v___x_1973_, v_a_1929_);
lean_dec_ref(v_lakeEnv_1966_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1983_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1983_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1983_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v_a_1975_);
lean_ctor_set(v___x_1979_, 1, v_a_1928_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1979_);
v___x_1981_ = v___x_1977_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_a_1928_);
v_a_1984_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1974_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1974_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_wsIdx_1992_; lean_object* v_relDir_1993_; uint8_t v___y_1995_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
lean_dec(v___x_1964_);
v_wsIdx_1992_ = lean_ctor_get(v_pkg_1926_, 0);
lean_inc(v_wsIdx_1992_);
v_relDir_1993_ = lean_ctor_get(v_pkg_1926_, 5);
lean_inc_ref(v_relDir_1993_);
lean_dec_ref(v_pkg_1926_);
v___x_1999_ = lean_unsigned_to_nat(0u);
v___x_2000_ = lean_nat_dec_eq(v_wsIdx_1992_, v___x_1999_);
lean_dec(v_wsIdx_1992_);
if (v___x_2000_ == 0)
{
uint8_t v___x_2001_; 
v___x_2001_ = 1;
v___y_1995_ = v___x_2001_;
goto v___jp_1994_;
}
else
{
uint8_t v___x_2002_; 
v___x_2002_ = 0;
v___y_1995_ = v___x_2002_;
goto v___jp_1994_;
}
v___jp_1994_:
{
lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1997_ = lean_string_dec_eq(v_relDir_1993_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lake_joinRelative(v_relDir_1993_, v___x_1996_);
v___y_1932_ = v___y_1995_;
v___y_1933_ = v___x_1998_;
goto v___jp_1931_;
}
else
{
v___y_1932_ = v___y_1995_;
v___y_1933_ = v_relDir_1993_;
goto v___jp_1931_;
}
}
}
v___jp_1931_:
{
lean_object* v_lakeEnv_1934_; lean_object* v_packages_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_config_1938_; lean_object* v_dir_1939_; lean_object* v_toWorkspaceConfig_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_lakeEnv_1934_ = lean_ctor_get(v_ws_1925_, 0);
lean_inc_ref(v_lakeEnv_1934_);
v_packages_1935_ = lean_ctor_get(v_ws_1925_, 4);
lean_inc_ref(v_packages_1935_);
lean_dec_ref(v_ws_1925_);
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
v___x_1942_ = l_Lake_Dependency_materialize(v_dep_1927_, v___y_1932_, v_lakeEnv_1934_, v_dir_1939_, v___x_1941_, v___y_1933_, v_a_1929_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1954_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1954_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1954_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_manifestEntry_1947_; lean_object* v_name_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v_manifestEntry_1947_ = lean_ctor_get(v_a_1943_, 4);
v_name_1948_ = lean_ctor_get(v_manifestEntry_1947_, 0);
lean_inc_ref(v_manifestEntry_1947_);
lean_inc(v_name_1948_);
v___x_1949_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1948_, v_manifestEntry_1947_, v_a_1928_);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v_a_1943_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1950_);
v___x_1952_ = v___x_1945_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_a_1928_);
v_a_1955_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1942_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1942_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_1925_ = stack[0].m_obj;
lean_object* v_pkg_1926_ = stack[1].m_obj;
lean_object* v_dep_1927_ = stack[2].m_obj;
lean_object* v_a_1928_ = stack[3].m_obj;
lean_object* v_a_1929_ = stack[4].m_obj;
lean_object* v_res_2003_;
v_res_2003_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1925_, v_pkg_1926_, v_dep_1927_, v_a_1928_, v_a_1929_);
stack->m_obj
 = v_res_2003_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_2004_, lean_object* v_pkg_2005_, lean_object* v_dep_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2004_, v_pkg_2005_, v_dep_2006_, v_a_2007_, v_a_2008_);
lean_dec_ref(v_a_2008_);
return v_res_2010_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_2011_; 
v___x_2011_ = 4;
return v___x_2011_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_2012_, lean_object* v_tc_x3f_2013_, uint8_t v_fixed_2014_, lean_object* v_self_2015_){
_start:
{
lean_object* v_clashes_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_clashes_2016_ = lean_ctor_get(v_self_2015_, 2);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_self_2015_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; lean_object* v_unused_2025_; 
v_unused_2024_ = lean_ctor_get(v_self_2015_, 1);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v_self_2015_, 0);
lean_dec(v_unused_2025_);
v___x_2018_ = v_self_2015_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_clashes_2016_);
lean_dec(v_self_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 1, v_tc_x3f_2013_);
lean_ctor_set(v___x_2018_, 0, v_src_2012_);
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_src_2012_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_tc_x3f_2013_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_clashes_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*3, v_fixed_2014_);
return v___x_2021_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_2012_ = stack[0].m_obj;
lean_object* v_tc_x3f_2013_ = stack[1].m_obj;
uint8_t v_fixed_2014_ = stack[2].m_num;
lean_object* v_self_2015_ = stack[3].m_obj;
lean_object* v_res_2026_;
v_res_2026_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_2012_, v_tc_x3f_2013_, v_fixed_2014_, v_self_2015_);
stack->m_obj
 = v_res_2026_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_2027_, lean_object* v_tc_x3f_2028_, lean_object* v_fixed_2029_, lean_object* v_self_2030_){
_start:
{
uint8_t v_fixed_boxed_2031_; lean_object* v_res_2032_; 
v_fixed_boxed_2031_ = lean_unbox(v_fixed_2029_);
v_res_2032_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_2027_, v_tc_x3f_2028_, v_fixed_boxed_2031_, v_self_2030_);
return v_res_2032_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_2033_, lean_object* v_ver_2034_, uint8_t v_fixed_2035_, lean_object* v_self_2036_){
_start:
{
lean_object* v_src_2037_; lean_object* v_tc_x3f_2038_; lean_object* v_clashes_2039_; uint8_t v_fixed_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2049_; 
v_src_2037_ = lean_ctor_get(v_self_2036_, 0);
v_tc_x3f_2038_ = lean_ctor_get(v_self_2036_, 1);
v_clashes_2039_ = lean_ctor_get(v_self_2036_, 2);
v_fixed_2040_ = lean_ctor_get_uint8(v_self_2036_, sizeof(void*)*3);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_self_2036_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2042_ = v_self_2036_;
v_isShared_2043_ = v_isSharedCheck_2049_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_clashes_2039_);
lean_inc(v_tc_x3f_2038_);
lean_inc(v_src_2037_);
lean_dec(v_self_2036_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2049_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2044_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2044_, 0, v_src_2033_);
lean_ctor_set(v___x_2044_, 1, v_ver_2034_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*2, v_fixed_2035_);
v___x_2045_ = lean_array_push(v_clashes_2039_, v___x_2044_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 2, v___x_2045_);
v___x_2047_ = v___x_2042_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_src_2037_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_tc_x3f_2038_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v___x_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2048_, sizeof(void*)*3, v_fixed_2040_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_2033_ = stack[0].m_obj;
lean_object* v_ver_2034_ = stack[1].m_obj;
uint8_t v_fixed_2035_ = stack[2].m_num;
lean_object* v_self_2036_ = stack[3].m_obj;
lean_object* v_res_2050_;
v_res_2050_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_2033_, v_ver_2034_, v_fixed_2035_, v_self_2036_);
stack->m_obj
 = v_res_2050_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_2051_, lean_object* v_ver_2052_, lean_object* v_fixed_2053_, lean_object* v_self_2054_){
_start:
{
uint8_t v_fixed_boxed_2055_; lean_object* v_res_2056_; 
v_fixed_boxed_2055_ = lean_unbox(v_fixed_2053_);
v_res_2056_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_2051_, v_ver_2052_, v_fixed_boxed_2055_, v_self_2054_);
return v_res_2056_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v___x_2061_, lean_object* v_as_2062_, size_t v_i_2063_, size_t v_stop_2064_, lean_object* v_b_2065_){
_start:
{
uint8_t v___x_2066_; 
v___x_2066_ = lean_usize_dec_eq(v_i_2063_, v_stop_2064_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v_src_2068_; lean_object* v_ver_2069_; uint8_t v_fixed_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2087_; 
v___x_2067_ = lean_array_uget_borrowed(v_as_2062_, v_i_2063_);
v_src_2068_ = lean_ctor_get(v___x_2067_, 0);
v_ver_2069_ = lean_ctor_get(v___x_2067_, 1);
v_fixed_2070_ = lean_ctor_get_uint8(v___x_2067_, sizeof(void*)*2);
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_nat_dec_lt(v___x_2071_, v___x_2061_);
if (v_fixed_2070_ == 0)
{
lean_object* v___x_2091_; 
v___x_2091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2087_ = v___x_2091_;
goto v___jp_2086_;
}
else
{
lean_object* v___x_2092_; 
v___x_2092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2087_ = v___x_2092_;
goto v___jp_2086_;
}
v___jp_2073_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; 
v___x_2077_ = lean_string_append(v___y_2075_, v___y_2076_);
lean_dec_ref(v___y_2076_);
v___x_2078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2079_ = lean_string_append(v___x_2077_, v___x_2078_);
lean_inc(v_src_2068_);
v___x_2080_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2068_, v___x_2072_);
v___x_2081_ = lean_string_append(v___x_2079_, v___x_2080_);
lean_dec_ref(v___x_2080_);
v___x_2082_ = lean_string_append(v___x_2081_, v___y_2074_);
v___x_2083_ = ((size_t)1ULL);
v___x_2084_ = lean_usize_add(v_i_2063_, v___x_2083_);
v_i_2063_ = v___x_2084_;
v_b_2065_ = v___x_2082_;
goto _start;
}
v___jp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v_toString_2090_; 
v___x_2088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2089_ = lean_string_append(v_b_2065_, v___x_2088_);
v_toString_2090_ = lean_ctor_get(v_ver_2069_, 0);
lean_inc_ref(v_toString_2090_);
v___y_2074_ = v___y_2087_;
v___y_2075_ = v___x_2089_;
v___y_2076_ = v_toString_2090_;
goto v___jp_2073_;
}
}
else
{
return v_b_2065_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2061_ = stack[0].m_obj;
lean_object* v_as_2062_ = stack[1].m_obj;
size_t v_i_2063_ = stack[2].m_num;
size_t v_stop_2064_ = stack[3].m_num;
lean_object* v_b_2065_ = stack[4].m_obj;
lean_object* v_res_2093_;
v_res_2093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2061_, v_as_2062_, v_i_2063_, v_stop_2064_, v_b_2065_);
stack->m_obj
 = v_res_2093_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v___x_2094_, lean_object* v_as_2095_, lean_object* v_i_2096_, lean_object* v_stop_2097_, lean_object* v_b_2098_){
_start:
{
size_t v_i_boxed_2099_; size_t v_stop_boxed_2100_; lean_object* v_res_2101_; 
v_i_boxed_2099_ = lean_unbox_usize(v_i_2096_);
lean_dec(v_i_2096_);
v_stop_boxed_2100_ = lean_unbox_usize(v_stop_2097_);
lean_dec(v_stop_2097_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2094_, v_as_2095_, v_i_boxed_2099_, v_stop_boxed_2100_, v_b_2098_);
lean_dec_ref(v_as_2095_);
lean_dec(v___x_2094_);
return v_res_2101_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v___x_2102_, lean_object* v_as_2103_, size_t v_i_2104_, size_t v_stop_2105_, lean_object* v_b_2106_){
_start:
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_usize_dec_eq(v_i_2104_, v_stop_2105_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v_src_2109_; lean_object* v_ver_2110_; uint8_t v_fixed_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2128_; 
v___x_2108_ = lean_array_uget_borrowed(v_as_2103_, v_i_2104_);
v_src_2109_ = lean_ctor_get(v___x_2108_, 0);
v_ver_2110_ = lean_ctor_get(v___x_2108_, 1);
v_fixed_2111_ = lean_ctor_get_uint8(v___x_2108_, sizeof(void*)*2);
v___x_2112_ = lean_unsigned_to_nat(0u);
v___x_2113_ = lean_nat_dec_lt(v___x_2112_, v___x_2102_);
if (v_fixed_2111_ == 0)
{
lean_object* v___x_2132_; 
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2128_ = v___x_2132_;
goto v___jp_2127_;
}
else
{
lean_object* v___x_2133_; 
v___x_2133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2128_ = v___x_2133_;
goto v___jp_2127_;
}
v___jp_2114_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; size_t v___x_2124_; size_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2118_ = lean_string_append(v___y_2116_, v___y_2117_);
lean_dec_ref(v___y_2117_);
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2120_ = lean_string_append(v___x_2118_, v___x_2119_);
lean_inc(v_src_2109_);
v___x_2121_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2109_, v___x_2113_);
v___x_2122_ = lean_string_append(v___x_2120_, v___x_2121_);
lean_dec_ref(v___x_2121_);
v___x_2123_ = lean_string_append(v___x_2122_, v___y_2115_);
v___x_2124_ = ((size_t)1ULL);
v___x_2125_ = lean_usize_add(v_i_2104_, v___x_2124_);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2102_, v_as_2103_, v___x_2125_, v_stop_2105_, v___x_2123_);
return v___x_2126_;
}
v___jp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v_toString_2131_; 
v___x_2129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2130_ = lean_string_append(v_b_2106_, v___x_2129_);
v_toString_2131_ = lean_ctor_get(v_ver_2110_, 0);
lean_inc_ref(v_toString_2131_);
v___y_2115_ = v___y_2128_;
v___y_2116_ = v___x_2130_;
v___y_2117_ = v_toString_2131_;
goto v___jp_2114_;
}
}
else
{
return v_b_2106_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2102_ = stack[0].m_obj;
lean_object* v_as_2103_ = stack[1].m_obj;
size_t v_i_2104_ = stack[2].m_num;
size_t v_stop_2105_ = stack[3].m_num;
lean_object* v_b_2106_ = stack[4].m_obj;
lean_object* v_res_2134_;
v_res_2134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___x_2102_, v_as_2103_, v_i_2104_, v_stop_2105_, v_b_2106_);
stack->m_obj
 = v_res_2134_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v___x_2135_, lean_object* v_as_2136_, lean_object* v_i_2137_, lean_object* v_stop_2138_, lean_object* v_b_2139_){
_start:
{
size_t v_i_boxed_2140_; size_t v_stop_boxed_2141_; lean_object* v_res_2142_; 
v_i_boxed_2140_ = lean_unbox_usize(v_i_2137_);
lean_dec(v_i_2137_);
v_stop_boxed_2141_ = lean_unbox_usize(v_stop_2138_);
lean_dec(v_stop_2138_);
v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___x_2135_, v_as_2136_, v_i_boxed_2140_, v_stop_boxed_2141_, v_b_2139_);
lean_dec_ref(v_as_2136_);
lean_dec(v___x_2135_);
return v_res_2142_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_2143_, lean_object* v_as_2144_, size_t v_i_2145_, size_t v_stop_2146_, lean_object* v_b_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v_a_2151_; uint8_t v___x_2155_; 
v___x_2155_ = lean_usize_dec_eq(v_i_2145_, v_stop_2146_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v_relPkgDir_2157_; lean_object* v_manifestEntry_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2156_ = lean_array_uget_borrowed(v_as_2144_, v_i_2145_);
v_relPkgDir_2157_ = lean_ctor_get(v___x_2156_, 1);
v_manifestEntry_2158_ = lean_ctor_get(v___x_2156_, 4);
lean_inc_ref(v_relPkgDir_2157_);
lean_inc_ref(v___x_2143_);
v___x_2159_ = l_Lake_joinRelative(v___x_2143_, v_relPkgDir_2157_);
v___x_2160_ = l_Lake_toolchainFileName;
v___x_2161_ = l_System_FilePath_join(v___x_2159_, v___x_2160_);
v___x_2162_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2161_);
lean_dec_ref(v___x_2161_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
if (lean_obj_tag(v_a_2163_) == 1)
{
lean_object* v_tc_x3f_2164_; 
v_tc_x3f_2164_ = lean_ctor_get(v_b_2147_, 1);
if (lean_obj_tag(v_tc_x3f_2164_) == 1)
{
lean_object* v_val_2165_; lean_object* v_src_2166_; lean_object* v_clashes_2167_; uint8_t v_fixed_2168_; lean_object* v_val_2169_; uint8_t v___x_2170_; uint8_t v___y_2172_; 
v_val_2165_ = lean_ctor_get(v_a_2163_, 0);
v_src_2166_ = lean_ctor_get(v_b_2147_, 0);
v_clashes_2167_ = lean_ctor_get(v_b_2147_, 2);
v_fixed_2168_ = lean_ctor_get_uint8(v_b_2147_, sizeof(void*)*3);
v_val_2169_ = lean_ctor_get(v_tc_x3f_2164_, 0);
v___x_2170_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2156_);
if (v___x_2170_ == 0)
{
uint8_t v___x_2181_; 
v___x_2181_ = l_Lake_ToolchainVer_ble(v_val_2165_, v_val_2169_);
if (v___x_2181_ == 0)
{
lean_inc_ref(v_clashes_2167_);
lean_inc(v_src_2166_);
lean_inc_ref(v_tc_x3f_2164_);
lean_dec_ref(v_b_2147_);
if (v_fixed_2168_ == 0)
{
goto v___jp_2179_;
}
else
{
if (v___x_2181_ == 0)
{
v___y_2172_ = v___x_2181_;
goto v___jp_2171_;
}
else
{
goto v___jp_2179_;
}
}
}
else
{
lean_dec_ref_known(v_a_2163_, 1);
v_a_2151_ = v_b_2147_;
goto v___jp_2150_;
}
}
else
{
if (v_fixed_2168_ == 0)
{
lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2196_; 
lean_inc_ref(v_clashes_2167_);
lean_inc(v_src_2166_);
lean_inc_ref(v_tc_x3f_2164_);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_b_2147_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; lean_object* v_unused_2198_; lean_object* v_unused_2199_; 
v_unused_2197_ = lean_ctor_get(v_b_2147_, 2);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_b_2147_, 1);
lean_dec(v_unused_2198_);
v_unused_2199_ = lean_ctor_get(v_b_2147_, 0);
lean_dec(v_unused_2199_);
v___x_2183_ = v_b_2147_;
v_isShared_2184_ = v_isSharedCheck_2196_;
goto v_resetjp_2182_;
}
else
{
lean_dec(v_b_2147_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2196_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
uint8_t v___x_2185_; 
v___x_2185_ = l_Lake_ToolchainVer_ble(v_val_2169_, v_val_2165_);
if (v___x_2185_ == 0)
{
lean_object* v_name_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
lean_inc(v_val_2165_);
lean_dec_ref_known(v_a_2163_, 1);
v_name_2186_ = lean_ctor_get(v_manifestEntry_2158_, 0);
lean_inc(v_name_2186_);
v___x_2187_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2187_, 0, v_name_2186_);
lean_ctor_set(v___x_2187_, 1, v_val_2165_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*2, v___x_2170_);
v___x_2188_ = lean_array_push(v_clashes_2167_, v___x_2187_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 2, v___x_2188_);
v___x_2190_ = v___x_2183_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_src_2166_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_tc_x3f_2164_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v___x_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2191_, sizeof(void*)*3, v_fixed_2168_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
v_a_2151_ = v___x_2190_;
goto v___jp_2150_;
}
}
else
{
lean_object* v_name_2192_; lean_object* v___x_2194_; 
lean_dec(v_src_2166_);
lean_dec_ref_known(v_tc_x3f_2164_, 1);
v_name_2192_ = lean_ctor_get(v_manifestEntry_2158_, 0);
lean_inc(v_name_2192_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 1, v_a_2163_);
lean_ctor_set(v___x_2183_, 0, v_name_2192_);
v___x_2194_ = v___x_2183_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_name_2192_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_a_2163_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_clashes_2167_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*3, v___x_2170_);
v_a_2151_ = v___x_2194_;
goto v___jp_2150_;
}
}
}
}
else
{
uint8_t v___x_2200_; 
lean_inc_n(v_val_2165_, 2);
lean_dec_ref_known(v_a_2163_, 1);
lean_inc(v_val_2169_);
v___x_2200_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2169_, v_val_2165_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2210_; 
lean_inc_ref(v_clashes_2167_);
lean_inc(v_src_2166_);
lean_inc_ref(v_tc_x3f_2164_);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_b_2147_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; lean_object* v_unused_2212_; lean_object* v_unused_2213_; 
v_unused_2211_ = lean_ctor_get(v_b_2147_, 2);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v_b_2147_, 1);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_b_2147_, 0);
lean_dec(v_unused_2213_);
v___x_2202_ = v_b_2147_;
v_isShared_2203_ = v_isSharedCheck_2210_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v_b_2147_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2210_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_name_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v_name_2204_ = lean_ctor_get(v_manifestEntry_2158_, 0);
lean_inc(v_name_2204_);
v___x_2205_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2205_, 0, v_name_2204_);
lean_ctor_set(v___x_2205_, 1, v_val_2165_);
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*2, v___x_2170_);
v___x_2206_ = lean_array_push(v_clashes_2167_, v___x_2205_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 2, v___x_2206_);
v___x_2208_ = v___x_2202_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_src_2166_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_tc_x3f_2164_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v___x_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2209_, sizeof(void*)*3, v_fixed_2168_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
v_a_2151_ = v___x_2208_;
goto v___jp_2150_;
}
}
}
else
{
lean_dec(v_val_2165_);
v_a_2151_ = v_b_2147_;
goto v___jp_2150_;
}
}
}
v___jp_2171_:
{
if (v___y_2172_ == 0)
{
lean_object* v_name_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_inc(v_val_2165_);
lean_dec_ref_known(v_a_2163_, 1);
v_name_2173_ = lean_ctor_get(v_manifestEntry_2158_, 0);
lean_inc(v_name_2173_);
v___x_2174_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2174_, 0, v_name_2173_);
lean_ctor_set(v___x_2174_, 1, v_val_2165_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*2, v___x_2170_);
v___x_2175_ = lean_array_push(v_clashes_2167_, v___x_2174_);
v___x_2176_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2176_, 0, v_src_2166_);
lean_ctor_set(v___x_2176_, 1, v_tc_x3f_2164_);
lean_ctor_set(v___x_2176_, 2, v___x_2175_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*3, v_fixed_2168_);
v_a_2151_ = v___x_2176_;
goto v___jp_2150_;
}
else
{
lean_object* v_name_2177_; lean_object* v___x_2178_; 
lean_dec(v_src_2166_);
lean_dec_ref_known(v_tc_x3f_2164_, 1);
v_name_2177_ = lean_ctor_get(v_manifestEntry_2158_, 0);
lean_inc(v_name_2177_);
v___x_2178_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2178_, 0, v_name_2177_);
lean_ctor_set(v___x_2178_, 1, v_a_2163_);
lean_ctor_set(v___x_2178_, 2, v_clashes_2167_);
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*3, v___x_2170_);
v_a_2151_ = v___x_2178_;
goto v___jp_2150_;
}
}
v___jp_2179_:
{
uint8_t v___x_2180_; 
v___x_2180_ = l_Lake_ToolchainVer_blt(v_val_2169_, v_val_2165_);
v___y_2172_ = v___x_2180_;
goto v___jp_2171_;
}
}
else
{
lean_object* v_clashes_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2223_; 
v_clashes_2214_ = lean_ctor_get(v_b_2147_, 2);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_b_2147_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; lean_object* v_unused_2225_; 
v_unused_2224_ = lean_ctor_get(v_b_2147_, 1);
lean_dec(v_unused_2224_);
v_unused_2225_ = lean_ctor_get(v_b_2147_, 0);
lean_dec(v_unused_2225_);
v___x_2216_ = v_b_2147_;
v_isShared_2217_ = v_isSharedCheck_2223_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_clashes_2214_);
lean_dec(v_b_2147_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2223_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v_name_2218_; uint8_t v___x_2219_; lean_object* v___x_2221_; 
v_name_2218_ = lean_ctor_get(v_manifestEntry_2158_, 0);
v___x_2219_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2156_);
lean_inc(v_name_2218_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 1, v_a_2163_);
lean_ctor_set(v___x_2216_, 0, v_name_2218_);
v___x_2221_ = v___x_2216_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_name_2218_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_a_2163_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_clashes_2214_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*3, v___x_2219_);
v_a_2151_ = v___x_2221_;
goto v___jp_2150_;
}
}
}
}
else
{
lean_dec(v_a_2163_);
v_a_2151_ = v_b_2147_;
goto v___jp_2150_;
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v_b_2147_);
lean_dec_ref(v___x_2143_);
v_a_2226_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2228_ = v___x_2162_;
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2162_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2230_ = lean_io_error_to_string(v_a_2226_);
v___x_2231_ = 3;
v___x_2232_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2232_, 0, v___x_2230_);
lean_ctor_set_uint8(v___x_2232_, sizeof(void*)*1, v___x_2231_);
lean_inc_ref(v___y_2148_);
v___x_2233_ = lean_apply_2(v___y_2148_, v___x_2232_, lean_box(0));
v___x_2234_ = lean_box(0);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2234_);
v___x_2236_ = v___x_2228_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v___x_2239_; 
lean_dec_ref(v___x_2143_);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v_b_2147_);
return v___x_2239_;
}
v___jp_2150_:
{
size_t v___x_2152_; size_t v___x_2153_; 
v___x_2152_ = ((size_t)1ULL);
v___x_2153_ = lean_usize_add(v_i_2145_, v___x_2152_);
v_i_2145_ = v___x_2153_;
v_b_2147_ = v_a_2151_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2143_ = stack[0].m_obj;
lean_object* v_as_2144_ = stack[1].m_obj;
size_t v_i_2145_ = stack[2].m_num;
size_t v_stop_2146_ = stack[3].m_num;
lean_object* v_b_2147_ = stack[4].m_obj;
lean_object* v___y_2148_ = stack[5].m_obj;
lean_object* v_res_2240_;
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2143_, v_as_2144_, v_i_2145_, v_stop_2146_, v_b_2147_, v___y_2148_);
stack->m_obj
 = v_res_2240_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2241_, lean_object* v_as_2242_, lean_object* v_i_2243_, lean_object* v_stop_2244_, lean_object* v_b_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
size_t v_i_boxed_2248_; size_t v_stop_boxed_2249_; lean_object* v_res_2250_; 
v_i_boxed_2248_ = lean_unbox_usize(v_i_2243_);
lean_dec(v_i_2243_);
v_stop_boxed_2249_ = lean_unbox_usize(v_stop_2244_);
lean_dec(v_stop_2244_);
v_res_2250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2241_, v_as_2242_, v_i_boxed_2248_, v_stop_boxed_2249_, v_b_2245_, v___y_2246_);
lean_dec_ref(v___y_2246_);
lean_dec_ref(v_as_2242_);
return v_res_2250_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2261_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2262_ = lean_unsigned_to_nat(4u);
v___x_2263_ = lean_mk_empty_array_with_capacity(v___x_2262_);
v___x_2264_ = lean_array_push(v___x_2263_, v___x_2261_);
return v___x_2264_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2265_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2266_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2267_ = lean_array_push(v___x_2266_, v___x_2265_);
return v___x_2267_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2288_, lean_object* v_rootDeps_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v___y_2293_; uint8_t v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; uint8_t v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; uint8_t v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v_lakeEnv_2329_; lean_object* v_lakeArgs_x3f_2330_; lean_object* v_packages_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v_baseName_2334_; lean_object* v_dir_2335_; lean_object* v_config_2336_; lean_object* v___x_2337_; lean_object* v_rootToolchainFile_2338_; uint8_t v___y_2340_; lean_object* v___y_2341_; uint8_t v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2484_; uint8_t v___y_2485_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_lakeEnv_2329_ = lean_ctor_get(v_ws_2288_, 0);
lean_inc_ref(v_lakeEnv_2329_);
v_lakeArgs_x3f_2330_ = lean_ctor_get(v_ws_2288_, 3);
lean_inc(v_lakeArgs_x3f_2330_);
v_packages_2331_ = lean_ctor_get(v_ws_2288_, 4);
lean_inc_ref(v_packages_2331_);
lean_dec_ref(v_ws_2288_);
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = lean_array_fget(v_packages_2331_, v___x_2332_);
lean_dec_ref(v_packages_2331_);
v_baseName_2334_ = lean_ctor_get(v___x_2333_, 1);
lean_inc(v_baseName_2334_);
v_dir_2335_ = lean_ctor_get(v___x_2333_, 4);
lean_inc_ref_n(v_dir_2335_, 3);
v_config_2336_ = lean_ctor_get(v___x_2333_, 6);
lean_inc_ref(v_config_2336_);
lean_dec(v___x_2333_);
v___x_2337_ = l_Lake_toolchainFileName;
v_rootToolchainFile_2338_ = l_Lake_joinRelative(v_dir_2335_, v___x_2337_);
v___x_2489_ = l_System_FilePath_join(v_dir_2335_, v___x_2337_);
v___x_2490_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2489_);
lean_dec_ref(v___x_2489_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2549_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2549_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2549_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v_src_2496_; lean_object* v_tc_x3f_2497_; lean_object* v_clashes_2498_; uint8_t v_fixed_2499_; lean_object* v___y_2523_; uint8_t v_fixedToolchain_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v_fixedToolchain_2537_ = lean_ctor_get_uint8(v_config_2336_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_2336_);
v___x_2538_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___x_2539_ = lean_array_get_size(v_rootDeps_2289_);
v___x_2540_ = lean_nat_dec_lt(v___x_2332_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_dec_ref(v_dir_2335_);
lean_inc(v_a_2491_);
v_src_2496_ = v_baseName_2334_;
v_tc_x3f_2497_ = v_a_2491_;
v_clashes_2498_ = v___x_2538_;
v_fixed_2499_ = v_fixedToolchain_2537_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
lean_inc(v_a_2491_);
lean_inc(v_baseName_2334_);
v___x_2541_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2541_, 0, v_baseName_2334_);
lean_ctor_set(v___x_2541_, 1, v_a_2491_);
lean_ctor_set(v___x_2541_, 2, v___x_2538_);
lean_ctor_set_uint8(v___x_2541_, sizeof(void*)*3, v_fixedToolchain_2537_);
v___x_2542_ = lean_nat_dec_le(v___x_2539_, v___x_2539_);
if (v___x_2542_ == 0)
{
if (v___x_2540_ == 0)
{
lean_dec_ref_known(v___x_2541_, 3);
lean_dec_ref(v_dir_2335_);
lean_inc(v_a_2491_);
v_src_2496_ = v_baseName_2334_;
v_tc_x3f_2497_ = v_a_2491_;
v_clashes_2498_ = v___x_2538_;
v_fixed_2499_ = v_fixedToolchain_2537_;
goto v___jp_2495_;
}
else
{
size_t v___x_2543_; size_t v___x_2544_; lean_object* v___x_2545_; 
lean_dec(v_baseName_2334_);
v___x_2543_ = ((size_t)0ULL);
v___x_2544_ = lean_usize_of_nat(v___x_2539_);
v___x_2545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2335_, v_rootDeps_2289_, v___x_2543_, v___x_2544_, v___x_2541_, v_a_2290_);
v___y_2523_ = v___x_2545_;
goto v___jp_2522_;
}
}
else
{
size_t v___x_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
lean_dec(v_baseName_2334_);
v___x_2546_ = ((size_t)0ULL);
v___x_2547_ = lean_usize_of_nat(v___x_2539_);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2335_, v_rootDeps_2289_, v___x_2546_, v___x_2547_, v___x_2541_, v_a_2290_);
v___y_2523_ = v___x_2548_;
goto v___jp_2522_;
}
}
v___jp_2495_:
{
lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2500_ = lean_array_get_size(v_clashes_2498_);
v___x_2501_ = lean_nat_dec_lt(v___x_2332_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_dec_ref(v_clashes_2498_);
lean_dec(v_src_2496_);
if (lean_obj_tag(v_tc_x3f_2497_) == 1)
{
if (lean_obj_tag(v_a_2491_) == 0)
{
lean_object* v_val_2502_; 
lean_del_object(v___x_2493_);
v_val_2502_ = lean_ctor_get(v_tc_x3f_2497_, 0);
lean_inc(v_val_2502_);
lean_dec_ref_known(v_tc_x3f_2497_, 1);
v___y_2484_ = v_val_2502_;
v___y_2485_ = v___x_2501_;
goto v___jp_2483_;
}
else
{
lean_object* v_val_2503_; lean_object* v_val_2504_; uint8_t v___x_2505_; 
v_val_2503_ = lean_ctor_get(v_tc_x3f_2497_, 0);
lean_inc_n(v_val_2503_, 2);
lean_dec_ref_known(v_tc_x3f_2497_, 1);
v_val_2504_ = lean_ctor_get(v_a_2491_, 0);
lean_inc(v_val_2504_);
lean_dec_ref_known(v_a_2491_, 1);
v___x_2505_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2504_, v_val_2503_);
if (v___x_2505_ == 0)
{
lean_del_object(v___x_2493_);
v___y_2484_ = v_val_2503_;
v___y_2485_ = v___x_2505_;
goto v___jp_2483_;
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2510_; 
lean_dec(v_val_2503_);
lean_dec_ref(v_rootToolchainFile_2338_);
lean_dec(v_lakeArgs_x3f_2330_);
lean_dec_ref(v_lakeEnv_2329_);
v___x_2506_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15));
lean_inc_ref(v_a_2290_);
v___x_2507_ = lean_apply_2(v_a_2290_, v___x_2506_, lean_box(0));
v___x_2508_ = lean_box(0);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2508_);
v___x_2510_ = v___x_2493_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
lean_dec(v_tc_x3f_2497_);
lean_dec(v_a_2491_);
lean_dec_ref(v_rootToolchainFile_2338_);
lean_dec(v_lakeArgs_x3f_2330_);
lean_dec_ref(v_lakeEnv_2329_);
v___x_2512_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17));
lean_inc_ref(v_a_2290_);
v___x_2513_ = lean_apply_2(v_a_2290_, v___x_2512_, lean_box(0));
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2513_);
v___x_2515_ = v___x_2493_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
else
{
lean_del_object(v___x_2493_);
lean_dec(v_a_2491_);
lean_dec_ref(v_rootToolchainFile_2338_);
lean_dec(v_lakeArgs_x3f_2330_);
lean_dec_ref(v_lakeEnv_2329_);
if (lean_obj_tag(v_tc_x3f_2497_) == 1)
{
if (v_fixed_2499_ == 0)
{
lean_object* v_val_2517_; lean_object* v___x_2518_; 
v_val_2517_ = lean_ctor_get(v_tc_x3f_2497_, 0);
lean_inc(v_val_2517_);
lean_dec_ref_known(v_tc_x3f_2497_, 1);
v___x_2518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2321_ = v___x_2501_;
v___y_2322_ = v_clashes_2498_;
v___y_2323_ = v_val_2517_;
v___y_2324_ = v_src_2496_;
v___y_2325_ = v___x_2500_;
v___y_2326_ = v___x_2518_;
goto v___jp_2320_;
}
else
{
lean_object* v_val_2519_; lean_object* v___x_2520_; 
v_val_2519_ = lean_ctor_get(v_tc_x3f_2497_, 0);
lean_inc(v_val_2519_);
lean_dec_ref_known(v_tc_x3f_2497_, 1);
v___x_2520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2321_ = v___x_2501_;
v___y_2322_ = v_clashes_2498_;
v___y_2323_ = v_val_2519_;
v___y_2324_ = v_src_2496_;
v___y_2325_ = v___x_2500_;
v___y_2326_ = v___x_2520_;
goto v___jp_2320_;
}
}
else
{
lean_object* v___x_2521_; 
lean_dec(v_tc_x3f_2497_);
lean_dec(v_src_2496_);
v___x_2521_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
v___y_2299_ = v___x_2501_;
v___y_2300_ = v_clashes_2498_;
v___y_2301_ = v___x_2500_;
v___y_2302_ = v___x_2521_;
goto v___jp_2298_;
}
}
}
v___jp_2522_:
{
if (lean_obj_tag(v___y_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v_src_2525_; lean_object* v_tc_x3f_2526_; lean_object* v_clashes_2527_; uint8_t v_fixed_2528_; 
v_a_2524_ = lean_ctor_get(v___y_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___y_2523_, 1);
v_src_2525_ = lean_ctor_get(v_a_2524_, 0);
lean_inc(v_src_2525_);
v_tc_x3f_2526_ = lean_ctor_get(v_a_2524_, 1);
lean_inc(v_tc_x3f_2526_);
v_clashes_2527_ = lean_ctor_get(v_a_2524_, 2);
lean_inc_ref(v_clashes_2527_);
v_fixed_2528_ = lean_ctor_get_uint8(v_a_2524_, sizeof(void*)*3);
lean_dec(v_a_2524_);
v_src_2496_ = v_src_2525_;
v_tc_x3f_2497_ = v_tc_x3f_2526_;
v_clashes_2498_ = v_clashes_2527_;
v_fixed_2499_ = v_fixed_2528_;
goto v___jp_2495_;
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_del_object(v___x_2493_);
lean_dec(v_a_2491_);
lean_dec_ref(v_rootToolchainFile_2338_);
lean_dec(v_lakeArgs_x3f_2330_);
lean_dec_ref(v_lakeEnv_2329_);
v_a_2529_ = lean_ctor_get(v___y_2523_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___y_2523_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___y_2523_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___y_2523_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v_rootToolchainFile_2338_);
lean_dec_ref(v_config_2336_);
lean_dec_ref(v_dir_2335_);
lean_dec(v_baseName_2334_);
lean_dec(v_lakeArgs_x3f_2330_);
lean_dec_ref(v_lakeEnv_2329_);
v_a_2550_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2552_ = v___x_2490_;
v_isShared_2553_ = v_isSharedCheck_2562_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2490_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2562_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; uint8_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2554_ = lean_io_error_to_string(v_a_2550_);
v___x_2555_ = 3;
v___x_2556_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set_uint8(v___x_2556_, sizeof(void*)*1, v___x_2555_);
lean_inc_ref(v_a_2290_);
v___x_2557_ = lean_apply_2(v_a_2290_, v___x_2556_, lean_box(0));
v___x_2558_ = lean_box(0);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2558_);
v___x_2560_ = v___x_2552_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
v___jp_2292_:
{
uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2294_ = 2;
v___x_2295_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2295_, 0, v___y_2293_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1, v___x_2294_);
lean_inc_ref(v_a_2290_);
v___x_2296_ = lean_apply_2(v_a_2290_, v___x_2295_, lean_box(0));
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
v___jp_2298_:
{
if (v___y_2299_ == 0)
{
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
v___y_2293_ = v___y_2302_;
goto v___jp_2292_;
}
else
{
size_t v___x_2303_; size_t v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = ((size_t)0ULL);
v___x_2304_ = lean_usize_of_nat(v___y_2301_);
v___x_2305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2301_, v___y_2300_, v___x_2303_, v___x_2304_, v___y_2302_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2301_);
v___y_2293_ = v___x_2305_;
goto v___jp_2292_;
}
}
v___jp_2306_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_inc_ref(v___y_2308_);
v___x_2314_ = lean_string_append(v___y_2308_, v___y_2313_);
lean_dec_ref(v___y_2313_);
v___x_2315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2316_ = lean_string_append(v___x_2314_, v___x_2315_);
v___x_2317_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2312_, v___y_2307_);
v___x_2318_ = lean_string_append(v___x_2316_, v___x_2317_);
lean_dec_ref(v___x_2317_);
v___x_2319_ = lean_string_append(v___x_2318_, v___y_2310_);
v___y_2299_ = v___y_2307_;
v___y_2300_ = v___y_2309_;
v___y_2301_ = v___y_2311_;
v___y_2302_ = v___x_2319_;
goto v___jp_2298_;
}
v___jp_2320_:
{
lean_object* v___x_2327_; lean_object* v_toString_2328_; 
v___x_2327_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_2328_ = lean_ctor_get(v___y_2323_, 0);
lean_inc_ref(v_toString_2328_);
lean_dec_ref(v___y_2323_);
v___y_2307_ = v___y_2321_;
v___y_2308_ = v___x_2327_;
v___y_2309_ = v___y_2322_;
v___y_2310_ = v___y_2326_;
v___y_2311_ = v___y_2325_;
v___y_2312_ = v___y_2324_;
v___y_2313_ = v_toString_2328_;
goto v___jp_2306_;
}
v___jp_2339_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_inc_ref(v___y_2341_);
v___x_2344_ = lean_string_append(v___y_2341_, v___y_2343_);
v___x_2345_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2346_ = lean_string_append(v___x_2344_, v___x_2345_);
v___x_2347_ = 1;
v___x_2348_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set_uint8(v___x_2348_, sizeof(void*)*1, v___x_2347_);
lean_inc_ref(v_a_2290_);
v___x_2349_ = lean_apply_2(v_a_2290_, v___x_2348_, lean_box(0));
v___x_2350_ = l_IO_FS_writeFile(v_rootToolchainFile_2338_, v___y_2343_);
lean_dec_ref(v_rootToolchainFile_2338_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_dec_ref_known(v___x_2350_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2330_) == 1)
{
lean_object* v_elan_x3f_2351_; 
v_elan_x3f_2351_ = lean_ctor_get(v_lakeEnv_2329_, 2);
if (lean_obj_tag(v_elan_x3f_2351_) == 1)
{
lean_object* v_val_2352_; lean_object* v_val_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v_elan_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_val_2352_ = lean_ctor_get(v_lakeArgs_x3f_2330_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v_lakeArgs_x3f_2330_, 1);
v_val_2353_ = lean_ctor_get(v_elan_x3f_2351_, 0);
v___x_2354_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_2290_);
v___x_2355_ = lean_apply_2(v_a_2290_, v___x_2354_, lean_box(0));
v___x_2356_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_2357_ = lean_ctor_get(v_val_2353_, 1);
lean_inc_ref(v_elan_2357_);
v___x_2358_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_2359_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_2360_ = lean_array_push(v___x_2359_, v___y_2343_);
v___x_2361_ = lean_array_push(v___x_2360_, v___x_2358_);
v___x_2362_ = l_Array_append___redArg(v___x_2361_, v_val_2352_);
lean_dec(v_val_2352_);
v___x_2363_ = lean_box(0);
v___x_2364_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2329_);
v___x_2365_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2365_, 0, v___x_2356_);
lean_ctor_set(v___x_2365_, 1, v_elan_2357_);
lean_ctor_set(v___x_2365_, 2, v___x_2362_);
lean_ctor_set(v___x_2365_, 3, v___x_2363_);
lean_ctor_set(v___x_2365_, 4, v___x_2364_);
lean_ctor_set_uint8(v___x_2365_, sizeof(void*)*5, v___y_2342_);
lean_ctor_set_uint8(v___x_2365_, sizeof(void*)*5 + 1, v___y_2340_);
v___x_2366_ = lean_io_process_spawn(v___x_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = lean_io_process_child_wait(v___x_2356_, v_a_2367_);
lean_dec(v_a_2367_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; uint32_t v___x_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2368_, 1);
v___x_2370_ = lean_unbox_uint32(v_a_2369_);
lean_dec(v_a_2369_);
v___x_2371_ = lean_uint32_to_uint8(v___x_2370_);
v___x_2372_ = lean_io_exit(v___x_2371_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2393_; 
v_a_2381_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2383_ = v___x_2372_;
v_isShared_2384_ = v_isSharedCheck_2393_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2372_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2393_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2385_ = lean_io_error_to_string(v_a_2381_);
v___x_2386_ = 3;
v___x_2387_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set_uint8(v___x_2387_, sizeof(void*)*1, v___x_2386_);
lean_inc_ref(v_a_2290_);
v___x_2388_ = lean_apply_2(v_a_2290_, v___x_2387_, lean_box(0));
v___x_2389_ = lean_box(0);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2389_);
v___x_2391_ = v___x_2383_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2406_; 
v_a_2394_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2396_ = v___x_2368_;
v_isShared_2397_ = v_isSharedCheck_2406_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2368_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2406_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2398_ = lean_io_error_to_string(v_a_2394_);
v___x_2399_ = 3;
v___x_2400_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set_uint8(v___x_2400_, sizeof(void*)*1, v___x_2399_);
lean_inc_ref(v_a_2290_);
v___x_2401_ = lean_apply_2(v_a_2290_, v___x_2400_, lean_box(0));
v___x_2402_ = lean_box(0);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2402_);
v___x_2404_ = v___x_2396_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2419_; 
v_a_2407_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2409_ = v___x_2366_;
v_isShared_2410_ = v_isSharedCheck_2419_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2366_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2419_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2411_ = lean_io_error_to_string(v_a_2407_);
v___x_2412_ = 3;
v___x_2413_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set_uint8(v___x_2413_, sizeof(void*)*1, v___x_2412_);
lean_inc_ref(v_a_2290_);
v___x_2414_ = lean_apply_2(v_a_2290_, v___x_2413_, lean_box(0));
v___x_2415_ = lean_box(0);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2415_);
v___x_2417_ = v___x_2409_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; 
lean_dec_ref_known(v_lakeArgs_x3f_2330_, 1);
lean_dec_ref(v___y_2343_);
lean_dec_ref(v_lakeEnv_2329_);
v___x_2420_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_2290_);
v___x_2421_ = lean_apply_2(v_a_2290_, v___x_2420_, lean_box(0));
v___x_2422_ = 4;
v___x_2423_ = lean_io_exit(v___x_2422_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2444_; 
v_a_2432_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2434_ = v___x_2423_;
v_isShared_2435_ = v_isSharedCheck_2444_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2423_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2444_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2436_ = lean_io_error_to_string(v_a_2432_);
v___x_2437_ = 3;
v___x_2438_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*1, v___x_2437_);
lean_inc_ref(v_a_2290_);
v___x_2439_ = lean_apply_2(v_a_2290_, v___x_2438_, lean_box(0));
v___x_2440_ = lean_box(0);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2440_);
v___x_2442_ = v___x_2434_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
else
{
lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; lean_object* v___x_2448_; 
lean_dec_ref(v___y_2343_);
lean_dec(v_lakeArgs_x3f_2330_);
lean_dec_ref(v_lakeEnv_2329_);
v___x_2445_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2290_);
v___x_2446_ = lean_apply_2(v_a_2290_, v___x_2445_, lean_box(0));
v___x_2447_ = 4;
v___x_2448_ = lean_io_exit(v___x_2447_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2469_; 
v_a_2457_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2459_ = v___x_2448_;
v_isShared_2460_ = v_isSharedCheck_2469_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2448_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2469_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; uint8_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2461_ = lean_io_error_to_string(v_a_2457_);
v___x_2462_ = 3;
v___x_2463_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*1, v___x_2462_);
lean_inc_ref(v_a_2290_);
v___x_2464_ = lean_apply_2(v_a_2290_, v___x_2463_, lean_box(0));
v___x_2465_ = lean_box(0);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2465_);
v___x_2467_ = v___x_2459_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2482_; 
lean_dec_ref(v___y_2343_);
lean_dec(v_lakeArgs_x3f_2330_);
lean_dec_ref(v_lakeEnv_2329_);
v_a_2470_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2472_ = v___x_2350_;
v_isShared_2473_ = v_isSharedCheck_2482_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2350_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2482_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; uint8_t v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
v___x_2474_ = lean_io_error_to_string(v_a_2470_);
v___x_2475_ = 3;
v___x_2476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set_uint8(v___x_2476_, sizeof(void*)*1, v___x_2475_);
lean_inc_ref(v_a_2290_);
v___x_2477_ = lean_apply_2(v_a_2290_, v___x_2476_, lean_box(0));
v___x_2478_ = lean_box(0);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2478_);
v___x_2480_ = v___x_2472_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
v___jp_2483_:
{
uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v_toString_2488_; 
v___x_2486_ = 1;
v___x_2487_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2488_ = lean_ctor_get(v___y_2484_, 0);
lean_inc_ref(v_toString_2488_);
lean_dec_ref(v___y_2484_);
v___y_2340_ = v___y_2485_;
v___y_2341_ = v___x_2487_;
v___y_2342_ = v___x_2486_;
v___y_2343_ = v_toString_2488_;
goto v___jp_2339_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_2288_ = stack[0].m_obj;
lean_object* v_rootDeps_2289_ = stack[1].m_obj;
lean_object* v_a_2290_ = stack[2].m_obj;
lean_object* v_res_2563_;
v_res_2563_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2288_, v_rootDeps_2289_, v_a_2290_);
stack->m_obj
 = v_res_2563_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2564_, lean_object* v_rootDeps_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2564_, v_rootDeps_2565_, v_a_2566_);
lean_dec_ref(v_a_2566_);
lean_dec_ref(v_rootDeps_2565_);
return v_res_2568_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2569_, lean_object* v_dep_2570_, lean_object* v_ws_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2571_, v_pkg_2569_, v_dep_2570_, v_a_2572_, v_a_2573_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v_fst_2577_; lean_object* v_snd_2578_; lean_object* v___x_2579_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v_fst_2577_ = lean_ctor_get(v_a_2576_, 0);
lean_inc_n(v_fst_2577_, 2);
v_snd_2578_ = lean_ctor_get(v_a_2576_, 1);
lean_inc(v_snd_2578_);
lean_dec(v_a_2576_);
v___x_2579_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2577_, v_snd_2578_, v_a_2573_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2596_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2596_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2596_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_snd_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2594_; 
v_snd_2584_ = lean_ctor_get(v_a_2580_, 1);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_a_2580_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v_a_2580_, 0);
lean_dec(v_unused_2595_);
v___x_2586_ = v_a_2580_;
v_isShared_2587_ = v_isSharedCheck_2594_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_snd_2584_);
lean_dec(v_a_2580_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2594_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v_fst_2577_);
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_fst_2577_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_snd_2584_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2591_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2589_);
v___x_2591_ = v___x_2582_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v_fst_2577_);
v_a_2597_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2579_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2579_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
return v___x_2575_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_2569_ = stack[0].m_obj;
lean_object* v_dep_2570_ = stack[1].m_obj;
lean_object* v_ws_2571_ = stack[2].m_obj;
lean_object* v_a_2572_ = stack[3].m_obj;
lean_object* v_a_2573_ = stack[4].m_obj;
lean_object* v_res_2605_;
v_res_2605_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2569_, v_dep_2570_, v_ws_2571_, v_a_2572_, v_a_2573_);
stack->m_obj
 = v_res_2605_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2606_, lean_object* v_dep_2607_, lean_object* v_ws_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2606_, v_dep_2607_, v_ws_2608_, v_a_2609_, v_a_2610_);
lean_dec_ref(v_a_2610_);
return v_res_2612_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2613_, lean_object* v_ws_2614_, lean_object* v_pkg_2615_, lean_object* v_dep_2616_, lean_object* v_a_2617_){
_start:
{
uint8_t v___y_2620_; lean_object* v___y_2621_; lean_object* v_name_2651_; lean_object* v___x_2652_; 
v_name_2651_ = lean_ctor_get(v_dep_2616_, 0);
v___x_2652_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2617_, v_name_2651_);
if (lean_obj_tag(v___x_2652_) == 1)
{
lean_object* v_val_2653_; lean_object* v_lakeEnv_2654_; lean_object* v_packages_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v_config_2658_; lean_object* v_dir_2659_; lean_object* v_toWorkspaceConfig_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_dec_ref(v_dep_2616_);
lean_dec_ref(v_pkg_2615_);
v_val_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_val_2653_);
lean_dec_ref_known(v___x_2652_, 1);
v_lakeEnv_2654_ = lean_ctor_get(v_ws_2614_, 0);
lean_inc_ref(v_lakeEnv_2654_);
v_packages_2655_ = lean_ctor_get(v_ws_2614_, 4);
lean_inc_ref(v_packages_2655_);
lean_dec_ref(v_ws_2614_);
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = lean_array_fget(v_packages_2655_, v___x_2656_);
lean_dec_ref(v_packages_2655_);
v_config_2658_ = lean_ctor_get(v___x_2657_, 6);
lean_inc_ref(v_config_2658_);
v_dir_2659_ = lean_ctor_get(v___x_2657_, 4);
lean_inc_ref(v_dir_2659_);
lean_dec(v___x_2657_);
v_toWorkspaceConfig_2660_ = lean_ctor_get(v_config_2658_, 0);
lean_inc_ref(v_toWorkspaceConfig_2660_);
lean_dec_ref(v_config_2658_);
v___x_2661_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2660_);
v___x_2662_ = l_Lake_PackageEntry_materialize(v_val_2653_, v_lakeEnv_2654_, v_dir_2659_, v___x_2661_, v___y_2613_);
lean_dec_ref(v_lakeEnv_2654_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2671_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2667_, 0, v_a_2663_);
lean_ctor_set(v___x_2667_, 1, v_a_2617_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2667_);
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec(v_a_2617_);
v_a_2672_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2662_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2662_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
else
{
lean_object* v_wsIdx_2680_; lean_object* v_relDir_2681_; uint8_t v___y_2683_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
lean_dec(v___x_2652_);
v_wsIdx_2680_ = lean_ctor_get(v_pkg_2615_, 0);
lean_inc(v_wsIdx_2680_);
v_relDir_2681_ = lean_ctor_get(v_pkg_2615_, 5);
lean_inc_ref(v_relDir_2681_);
lean_dec_ref(v_pkg_2615_);
v___x_2687_ = lean_unsigned_to_nat(0u);
v___x_2688_ = lean_nat_dec_eq(v_wsIdx_2680_, v___x_2687_);
lean_dec(v_wsIdx_2680_);
if (v___x_2688_ == 0)
{
uint8_t v___x_2689_; 
v___x_2689_ = 1;
v___y_2683_ = v___x_2689_;
goto v___jp_2682_;
}
else
{
uint8_t v___x_2690_; 
v___x_2690_ = 0;
v___y_2683_ = v___x_2690_;
goto v___jp_2682_;
}
v___jp_2682_:
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2685_ = lean_string_dec_eq(v_relDir_2681_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lake_joinRelative(v_relDir_2681_, v___x_2684_);
v___y_2620_ = v___y_2683_;
v___y_2621_ = v___x_2686_;
goto v___jp_2619_;
}
else
{
v___y_2620_ = v___y_2683_;
v___y_2621_ = v_relDir_2681_;
goto v___jp_2619_;
}
}
}
v___jp_2619_:
{
lean_object* v_lakeEnv_2622_; lean_object* v_packages_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v_config_2626_; lean_object* v_dir_2627_; lean_object* v_toWorkspaceConfig_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_lakeEnv_2622_ = lean_ctor_get(v_ws_2614_, 0);
lean_inc_ref(v_lakeEnv_2622_);
v_packages_2623_ = lean_ctor_get(v_ws_2614_, 4);
lean_inc_ref(v_packages_2623_);
lean_dec_ref(v_ws_2614_);
v___x_2624_ = lean_unsigned_to_nat(0u);
v___x_2625_ = lean_array_fget(v_packages_2623_, v___x_2624_);
lean_dec_ref(v_packages_2623_);
v_config_2626_ = lean_ctor_get(v___x_2625_, 6);
lean_inc_ref(v_config_2626_);
v_dir_2627_ = lean_ctor_get(v___x_2625_, 4);
lean_inc_ref(v_dir_2627_);
lean_dec(v___x_2625_);
v_toWorkspaceConfig_2628_ = lean_ctor_get(v_config_2626_, 0);
lean_inc_ref(v_toWorkspaceConfig_2628_);
lean_dec_ref(v_config_2626_);
v___x_2629_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2628_);
v___x_2630_ = l_Lake_Dependency_materialize(v_dep_2616_, v___y_2620_, v_lakeEnv_2622_, v_dir_2627_, v___x_2629_, v___y_2621_, v___y_2613_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2642_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2642_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2642_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v_manifestEntry_2635_; lean_object* v_name_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
v_manifestEntry_2635_ = lean_ctor_get(v_a_2631_, 4);
v_name_2636_ = lean_ctor_get(v_manifestEntry_2635_, 0);
lean_inc_ref(v_manifestEntry_2635_);
lean_inc(v_name_2636_);
v___x_2637_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2636_, v_manifestEntry_2635_, v_a_2617_);
v___x_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2638_, 0, v_a_2631_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2638_);
v___x_2640_ = v___x_2633_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_a_2617_);
v_a_2643_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2630_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2630_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2613_ = stack[0].m_obj;
lean_object* v_ws_2614_ = stack[1].m_obj;
lean_object* v_pkg_2615_ = stack[2].m_obj;
lean_object* v_dep_2616_ = stack[3].m_obj;
lean_object* v_a_2617_ = stack[4].m_obj;
lean_object* v_res_2691_;
v_res_2691_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2613_, v_ws_2614_, v_pkg_2615_, v_dep_2616_, v_a_2617_);
stack->m_obj
 = v_res_2691_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2692_, lean_object* v_ws_2693_, lean_object* v_pkg_2694_, lean_object* v_dep_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2692_, v_ws_2693_, v_pkg_2694_, v_dep_2695_, v_a_2696_);
lean_dec_ref(v___y_2692_);
return v_res_2698_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2699_, lean_object* v_dep_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_manifestEntry_2703_; lean_object* v_pkgDir_2704_; lean_object* v_name_2705_; lean_object* v_manifestFile_x3f_2706_; lean_object* v___y_2708_; lean_object* v_fst_2709_; lean_object* v_snd_2710_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v_val_2762_; lean_object* v___y_2778_; 
v_manifestEntry_2703_ = lean_ctor_get(v_dep_2700_, 4);
v_pkgDir_2704_ = lean_ctor_get(v_dep_2700_, 0);
v_name_2705_ = lean_ctor_get(v_manifestEntry_2703_, 0);
v_manifestFile_x3f_2706_ = lean_ctor_get(v_manifestEntry_2703_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2706_) == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2704_);
v___x_2799_ = l_Lake_joinRelative(v_pkgDir_2704_, v___x_2798_);
v___y_2778_ = v___x_2799_;
goto v___jp_2777_;
}
else
{
lean_object* v_val_2800_; lean_object* v___x_2801_; 
v_val_2800_ = lean_ctor_get(v_manifestFile_x3f_2706_, 0);
lean_inc(v_val_2800_);
lean_inc_ref(v_pkgDir_2704_);
v___x_2801_ = l_Lake_joinRelative(v_pkgDir_2704_, v_val_2800_);
v___y_2778_ = v___x_2801_;
goto v___jp_2777_;
}
v___jp_2707_:
{
if (lean_obj_tag(v_fst_2709_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2740_; 
lean_inc(v_name_2705_);
lean_dec_ref(v_dep_2700_);
v_a_2711_ = lean_ctor_get(v_fst_2709_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_fst_2709_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2713_ = v_fst_2709_;
v_isShared_2714_ = v_isSharedCheck_2740_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v_fst_2709_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2740_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
if (lean_obj_tag(v_a_2711_) == 11)
{
uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
lean_dec_ref_known(v_a_2711_, 2);
v___x_2715_ = 0;
v___x_2716_ = l_Lean_Name_toString(v_name_2705_, v___x_2715_);
v___x_2717_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2718_ = lean_string_append(v___x_2716_, v___x_2717_);
v___x_2719_ = lean_string_append(v___x_2718_, v___y_2708_);
lean_dec_ref(v___y_2708_);
v___x_2720_ = 2;
v___x_2721_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*1, v___x_2720_);
v___x_2722_ = lean_apply_2(v___y_2699_, v___x_2721_, lean_box(0));
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v_snd_2710_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2723_);
v___x_2725_ = v___x_2713_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
else
{
uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_dec_ref(v___y_2708_);
v___x_2727_ = 0;
v___x_2728_ = l_Lean_Name_toString(v_name_2705_, v___x_2727_);
v___x_2729_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2730_ = lean_string_append(v___x_2728_, v___x_2729_);
v___x_2731_ = lean_io_error_to_string(v_a_2711_);
v___x_2732_ = lean_string_append(v___x_2730_, v___x_2731_);
lean_dec_ref(v___x_2731_);
v___x_2733_ = 2;
v___x_2734_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*1, v___x_2733_);
v___x_2735_ = lean_apply_2(v___y_2699_, v___x_2734_, lean_box(0));
v___x_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
lean_ctor_set(v___x_2736_, 1, v_snd_2710_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2736_);
v___x_2738_ = v___x_2713_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2757_; 
lean_dec_ref(v___y_2708_);
lean_dec_ref(v___y_2699_);
v_a_2741_ = lean_ctor_get(v_fst_2709_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_fst_2709_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2743_ = v_fst_2709_;
v_isShared_2744_ = v_isSharedCheck_2757_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v_fst_2709_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2757_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v_packages_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v_packages_2745_ = lean_ctor_get(v_a_2741_, 3);
lean_inc_ref(v_packages_2745_);
lean_dec(v_a_2741_);
v___x_2746_ = lean_unsigned_to_nat(0u);
v___x_2747_ = lean_array_get_size(v_packages_2745_);
v___x_2748_ = lean_box(0);
v___x_2749_ = lean_nat_dec_lt(v___x_2746_, v___x_2747_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
lean_dec_ref(v_packages_2745_);
lean_dec_ref(v_dep_2700_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v_snd_2710_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set_tag(v___x_2743_, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2750_);
v___x_2752_ = v___x_2743_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
else
{
size_t v___x_2754_; size_t v___x_2755_; lean_object* v___x_2756_; 
lean_del_object(v___x_2743_);
v___x_2754_ = ((size_t)0ULL);
v___x_2755_ = lean_usize_of_nat(v___x_2747_);
v___x_2756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2700_, v_packages_2745_, v___x_2754_, v___x_2755_, v___x_2748_, v_snd_2710_);
lean_dec_ref(v_packages_2745_);
return v___x_2756_;
}
}
}
}
v___jp_2758_:
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = lean_array_get_size(v___y_2759_);
v___x_2764_ = lean_nat_dec_lt(v___y_2760_, v___x_2763_);
if (v___x_2764_ == 0)
{
v___y_2708_ = v___y_2761_;
v_fst_2709_ = v_val_2762_;
v_snd_2710_ = v_a_2701_;
goto v___jp_2707_;
}
else
{
lean_object* v___x_2765_; size_t v___x_2766_; size_t v___x_2767_; lean_object* v___x_2768_; 
v___x_2765_ = lean_box(0);
v___x_2766_ = ((size_t)0ULL);
v___x_2767_ = lean_usize_of_nat(v___x_2763_);
v___x_2768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2759_, v___x_2766_, v___x_2767_, v___x_2765_, v___y_2699_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_dec_ref_known(v___x_2768_, 1);
v___y_2708_ = v___y_2761_;
v_fst_2709_ = v_val_2762_;
v_snd_2710_ = v_a_2701_;
goto v___jp_2707_;
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref(v_val_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v_a_2701_);
lean_dec_ref(v_dep_2700_);
lean_dec_ref(v___y_2699_);
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
v___jp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2779_ = lean_unsigned_to_nat(0u);
v___x_2780_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2778_);
v___x_2781_ = l_Lake_Manifest_load(v___y_2778_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set_tag(v___x_2784_, 1);
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
v___y_2759_ = v___x_2780_;
v___y_2760_ = v___x_2779_;
v___y_2761_ = v___y_2778_;
v_val_2762_ = v___x_2787_;
goto v___jp_2758_;
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
v_a_2790_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2781_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2781_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set_tag(v___x_2792_, 0);
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
v___y_2759_ = v___x_2780_;
v___y_2760_ = v___x_2779_;
v___y_2761_ = v___y_2778_;
v_val_2762_ = v___x_2795_;
goto v___jp_2758_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2699_ = stack[0].m_obj;
lean_object* v_dep_2700_ = stack[1].m_obj;
lean_object* v_a_2701_ = stack[2].m_obj;
lean_object* v_res_2802_;
v_res_2802_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2699_, v_dep_2700_, v_a_2701_);
stack->m_obj
 = v_res_2802_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2803_, lean_object* v_dep_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2803_, v_dep_2804_, v_a_2805_);
return v_res_2807_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2812_, v___y_2810_, v___y_2808_, v___y_2809_, v___y_2811_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v_fst_2816_; lean_object* v_snd_2817_; lean_object* v___x_2818_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v_fst_2816_ = lean_ctor_get(v_a_2815_, 0);
lean_inc_n(v_fst_2816_, 2);
v_snd_2817_ = lean_ctor_get(v_a_2815_, 1);
lean_inc(v_snd_2817_);
lean_dec(v_a_2815_);
v___x_2818_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2812_, v_fst_2816_, v_snd_2817_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2835_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2835_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2835_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_snd_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2833_; 
v_snd_2823_ = lean_ctor_get(v_a_2819_, 1);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; 
v_unused_2834_ = lean_ctor_get(v_a_2819_, 0);
lean_dec(v_unused_2834_);
v___x_2825_ = v_a_2819_;
v_isShared_2826_ = v_isSharedCheck_2833_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_snd_2823_);
lean_dec(v_a_2819_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2833_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_fst_2816_);
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_fst_2816_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_snd_2823_);
v___x_2828_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2828_);
v___x_2830_ = v___x_2821_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v_fst_2816_);
v_a_2836_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2818_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2818_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
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
else
{
lean_dec_ref(v___y_2812_);
return v___x_2814_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2808_ = stack[0].m_obj;
lean_object* v___y_2809_ = stack[1].m_obj;
lean_object* v___y_2810_ = stack[2].m_obj;
lean_object* v___y_2811_ = stack[3].m_obj;
lean_object* v___y_2812_ = stack[4].m_obj;
lean_object* v_res_2844_;
v_res_2844_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
stack->m_obj
 = v_res_2844_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
return v_res_2851_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(lean_object* v_toUpdate_2852_, lean_object* v___x_2853_, lean_object* v___x_2854_, lean_object* v_entries_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___y_2860_; 
if (lean_obj_tag(v_toUpdate_2852_) == 0)
{
lean_object* v_depConfigs_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v_depConfigs_2902_ = lean_ctor_get(v___x_2853_, 12);
v___x_2903_ = l_Lean_NameSet_empty;
v___x_2904_ = lean_array_get_size(v_depConfigs_2902_);
v___x_2905_ = lean_nat_dec_lt(v___x_2854_, v___x_2904_);
if (v___x_2905_ == 0)
{
v___y_2860_ = v___x_2903_;
goto v___jp_2859_;
}
else
{
size_t v___x_2906_; size_t v___x_2907_; lean_object* v___x_2908_; 
v___x_2906_ = ((size_t)0ULL);
v___x_2907_ = lean_usize_of_nat(v___x_2904_);
v___x_2908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_2902_, v___x_2906_, v___x_2907_, v___x_2903_);
v___y_2860_ = v___x_2908_;
goto v___jp_2859_;
}
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_box(0);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___y_2856_);
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
return v___x_2911_;
}
v___jp_2859_:
{
size_t v_sz_2861_; size_t v___x_2862_; lean_object* v___x_2863_; 
v_sz_2861_ = lean_array_size(v_entries_2855_);
v___x_2862_ = ((size_t)0ULL);
v___x_2863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_entries_2855_, v_sz_2861_, v___x_2862_, v___y_2860_, v___y_2856_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v_fst_2865_; lean_object* v_snd_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v_fst_2865_ = lean_ctor_get(v_a_2864_, 0);
lean_inc(v_fst_2865_);
v_snd_2866_ = lean_ctor_get(v_a_2864_, 1);
lean_inc(v_snd_2866_);
lean_dec(v_a_2864_);
v___x_2867_ = lean_box(0);
v___x_2868_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_2865_, v___x_2867_, v_toUpdate_2852_, v_snd_2866_, v___y_2857_);
lean_dec(v_fst_2865_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2885_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2885_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2885_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v_snd_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2883_; 
v_snd_2873_ = lean_ctor_get(v_a_2869_, 1);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_a_2869_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; 
v_unused_2884_ = lean_ctor_get(v_a_2869_, 0);
lean_dec(v_unused_2884_);
v___x_2875_ = v_a_2869_;
v_isShared_2876_ = v_isSharedCheck_2883_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_snd_2873_);
lean_dec(v_a_2869_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2883_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2867_);
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_snd_2873_);
v___x_2878_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2880_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2878_);
v___x_2880_ = v___x_2871_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_a_2886_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2868_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2868_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v_toUpdate_2852_);
v_a_2894_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2863_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2863_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toUpdate_2852_ = stack[0].m_obj;
lean_object* v___x_2853_ = stack[1].m_obj;
lean_object* v___x_2854_ = stack[2].m_obj;
lean_object* v_entries_2855_ = stack[3].m_obj;
lean_object* v___y_2856_ = stack[4].m_obj;
lean_object* v___y_2857_ = stack[5].m_obj;
lean_object* v_res_2912_;
v_res_2912_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2852_, v___x_2853_, v___x_2854_, v_entries_2855_, v___y_2856_, v___y_2857_);
stack->m_obj
 = v_res_2912_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0___boxed(lean_object* v_toUpdate_2913_, lean_object* v___x_2914_, lean_object* v___x_2915_, lean_object* v_entries_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2913_, v___x_2914_, v___x_2915_, v_entries_2916_, v___y_2917_, v___y_2918_);
lean_dec_ref(v___y_2918_);
lean_dec_ref(v_entries_2916_);
lean_dec(v___x_2915_);
lean_dec_ref(v___x_2914_);
return v_res_2920_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2921_, lean_object* v_ws_2922_, lean_object* v_toUpdate_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v___y_2927_; lean_object* v___y_2932_; lean_object* v_fst_2933_; lean_object* v_snd_2934_; lean_object* v_packages_2953_; lean_object* v___x_2954_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v_val_2959_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___x_2995_; lean_object* v_baseName_2996_; lean_object* v_dir_2997_; lean_object* v_config_2998_; lean_object* v_relManifestFile_2999_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; uint8_t v_fst_3004_; lean_object* v_snd_3005_; lean_object* v_packagesDir_x3f_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; uint8_t v___x_3049_; lean_object* v_rootName_3050_; lean_object* v_fst_3052_; lean_object* v_snd_3053_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v_val_3120_; lean_object* v___x_3134_; 
v_packages_2953_ = lean_ctor_get(v_ws_2922_, 4);
v___x_2954_ = lean_unsigned_to_nat(0u);
v___x_2995_ = lean_array_fget_borrowed(v_packages_2953_, v___x_2954_);
v_baseName_2996_ = lean_ctor_get(v___x_2995_, 1);
v_dir_2997_ = lean_ctor_get(v___x_2995_, 4);
v_config_2998_ = lean_ctor_get(v___x_2995_, 6);
v_relManifestFile_2999_ = lean_ctor_get(v___x_2995_, 9);
v___x_3049_ = 0;
lean_inc(v_baseName_2996_);
v_rootName_3050_ = l_Lean_Name_toString(v_baseName_2996_, v___x_3049_);
lean_inc_ref(v_relManifestFile_2999_);
lean_inc_ref(v_dir_2997_);
v___x_3117_ = l_Lake_joinRelative(v_dir_2997_, v_relManifestFile_2999_);
v___x_3118_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_3134_ = l_Lake_Manifest_load(v___x_3117_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3134_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3134_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set_tag(v___x_3137_, 1);
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
v_val_3120_ = v___x_3140_;
goto v___jp_3119_;
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
v_a_3143_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3134_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3134_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set_tag(v___x_3145_, 0);
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
v_val_3120_ = v___x_3148_;
goto v___jp_3119_;
}
}
}
v___jp_2926_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
lean_ctor_set(v___x_2929_, 1, v___y_2927_);
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
v___jp_2931_:
{
if (lean_obj_tag(v_fst_2933_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v_snd_2934_);
v_a_2935_ = lean_ctor_get(v_fst_2933_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_fst_2933_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2937_ = v_fst_2933_;
v_isShared_2938_ = v_isSharedCheck_2949_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v_fst_2933_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2949_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2939_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2940_ = lean_io_error_to_string(v_a_2935_);
v___x_2941_ = lean_string_append(v___x_2939_, v___x_2940_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = 3;
v___x_2943_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set_uint8(v___x_2943_, sizeof(void*)*1, v___x_2942_);
lean_inc_ref(v___y_2932_);
v___x_2944_ = lean_apply_2(v___y_2932_, v___x_2943_, lean_box(0));
v___x_2945_ = lean_box(0);
if (v_isShared_2938_ == 0)
{
lean_ctor_set_tag(v___x_2937_, 1);
lean_ctor_set(v___x_2937_, 0, v___x_2945_);
v___x_2947_ = v___x_2937_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
lean_dec_ref(v_fst_2933_);
v___x_2950_ = lean_box(0);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v_snd_2934_);
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
return v___x_2952_;
}
}
v___jp_2955_:
{
lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2960_ = lean_array_get_size(v___y_2956_);
v___x_2961_ = lean_nat_dec_lt(v___x_2954_, v___x_2960_);
if (v___x_2961_ == 0)
{
v___y_2932_ = v___y_2957_;
v_fst_2933_ = v_val_2959_;
v_snd_2934_ = v___y_2958_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_2962_; size_t v___x_2963_; size_t v___x_2964_; lean_object* v___x_2965_; 
v___x_2962_ = lean_box(0);
v___x_2963_ = ((size_t)0ULL);
v___x_2964_ = lean_usize_of_nat(v___x_2960_);
v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2956_, v___x_2963_, v___x_2964_, v___x_2962_, v___y_2957_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_dec_ref_known(v___x_2965_, 1);
v___y_2932_ = v___y_2957_;
v_fst_2933_ = v_val_2959_;
v_snd_2934_ = v___y_2958_;
goto v___jp_2931_;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec_ref(v_val_2959_);
lean_dec(v___y_2958_);
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
}
v___jp_2974_:
{
if (lean_obj_tag(v___y_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
v_a_2979_ = lean_ctor_get(v___y_2978_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___y_2978_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___y_2978_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___y_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set_tag(v___x_2981_, 1);
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
v___y_2956_ = v___y_2975_;
v___y_2957_ = v___y_2976_;
v___y_2958_ = v___y_2977_;
v_val_2959_ = v___x_2984_;
goto v___jp_2955_;
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
v_a_2987_ = lean_ctor_get(v___y_2978_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___y_2978_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___y_2978_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___y_2978_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
lean_ctor_set_tag(v___x_2989_, 0);
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
v___y_2956_ = v___y_2975_;
v___y_2957_ = v___y_2976_;
v___y_2958_ = v___y_2977_;
v_val_2959_ = v___x_2992_;
goto v___jp_2955_;
}
}
}
}
v___jp_3000_:
{
lean_object* v_toWorkspaceConfig_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v_toWorkspaceConfig_3006_ = lean_ctor_get(v_config_2998_, 0);
v___x_3007_ = l_System_FilePath_normalize(v___y_3003_);
lean_inc_ref(v_toWorkspaceConfig_3006_);
v___x_3008_ = l_System_FilePath_normalize(v_toWorkspaceConfig_3006_);
lean_inc_ref(v___x_3008_);
v___x_3009_ = l_System_FilePath_normalize(v___x_3008_);
v___x_3010_ = lean_string_dec_eq(v___x_3007_, v___x_3009_);
lean_dec_ref(v___x_3009_);
lean_dec_ref(v___x_3007_);
if (v___x_3010_ == 0)
{
if (v_fst_3004_ == 0)
{
lean_dec_ref(v___x_3008_);
lean_dec_ref(v___y_3001_);
v___y_2927_ = v_snd_3005_;
goto v___jp_2926_;
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3011_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_3012_ = lean_string_append(v___x_3011_, v___y_3001_);
v___x_3013_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_3014_ = lean_string_append(v___x_3012_, v___x_3013_);
lean_inc_ref(v_dir_2997_);
v___x_3015_ = l_Lake_joinRelative(v_dir_2997_, v___x_3008_);
v___x_3016_ = lean_string_append(v___x_3014_, v___x_3015_);
v___x_3017_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_3018_ = lean_string_append(v___x_3016_, v___x_3017_);
v___x_3019_ = 1;
v___x_3020_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3020_, 0, v___x_3018_);
lean_ctor_set_uint8(v___x_3020_, sizeof(void*)*1, v___x_3019_);
lean_inc_ref(v___y_3002_);
v___x_3021_ = lean_apply_2(v___y_3002_, v___x_3020_, lean_box(0));
v___x_3022_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_3015_);
v___x_3023_ = l_Lake_createParentDirs(v___x_3015_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v___x_3024_; 
lean_dec_ref_known(v___x_3023_, 1);
v___x_3024_ = lean_io_rename(v___y_3001_, v___x_3015_);
lean_dec_ref(v___x_3015_);
lean_dec_ref(v___y_3001_);
v___y_2975_ = v___x_3022_;
v___y_2976_ = v___y_3002_;
v___y_2977_ = v_snd_3005_;
v___y_2978_ = v___x_3024_;
goto v___jp_2974_;
}
else
{
lean_dec_ref(v___x_3015_);
lean_dec_ref(v___y_3001_);
v___y_2975_ = v___x_3022_;
v___y_2976_ = v___y_3002_;
v___y_2977_ = v_snd_3005_;
v___y_2978_ = v___x_3023_;
goto v___jp_2974_;
}
}
}
else
{
lean_dec_ref(v___x_3008_);
lean_dec_ref(v___y_3001_);
v___y_2927_ = v_snd_3005_;
goto v___jp_2926_;
}
}
v___jp_3025_:
{
if (lean_obj_tag(v_packagesDir_x3f_3026_) == 1)
{
lean_object* v_val_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; uint8_t v___x_3033_; 
v_val_3029_ = lean_ctor_get(v_packagesDir_x3f_3026_, 0);
lean_inc_n(v_val_3029_, 2);
lean_dec_ref_known(v_packagesDir_x3f_3026_, 1);
lean_inc_ref(v_dir_2997_);
v___x_3030_ = l_Lake_joinRelative(v_dir_2997_, v_val_3029_);
v___x_3031_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_3032_ = l_System_FilePath_pathExists(v___x_3030_);
v___x_3033_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_3033_ == 0)
{
v___y_3001_ = v___x_3030_;
v___y_3002_ = v___y_3028_;
v___y_3003_ = v_val_3029_;
v_fst_3004_ = v___x_3032_;
v_snd_3005_ = v___y_3027_;
goto v___jp_3000_;
}
else
{
lean_object* v___x_3034_; size_t v___x_3035_; size_t v___x_3036_; lean_object* v___x_3037_; 
v___x_3034_ = lean_box(0);
v___x_3035_ = ((size_t)0ULL);
v___x_3036_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_3031_, v___x_3035_, v___x_3036_, v___x_3034_, v___y_3028_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_dec_ref_known(v___x_3037_, 1);
v___y_3001_ = v___x_3030_;
v___y_3002_ = v___y_3028_;
v___y_3003_ = v_val_3029_;
v_fst_3004_ = v___x_3032_;
v_snd_3005_ = v___y_3027_;
goto v___jp_3000_;
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v___x_3030_);
lean_dec(v_val_3029_);
lean_dec(v___y_3027_);
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
else
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec(v_packagesDir_x3f_3026_);
v___x_3046_ = lean_box(0);
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v___y_3027_);
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
}
v___jp_3051_:
{
if (lean_obj_tag(v_fst_3052_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3101_; 
v_a_3054_ = lean_ctor_get(v_fst_3052_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_fst_3052_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3056_ = v_fst_3052_;
v_isShared_3057_ = v_isSharedCheck_3101_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v_fst_3052_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3101_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
if (lean_obj_tag(v_a_3054_) == 11)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
lean_dec_ref_known(v_a_3054_, 2);
lean_del_object(v___x_3056_);
v___x_3058_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_3059_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2923_, v___x_2995_, v___x_2954_, v___x_3058_, v_snd_3053_, v_a_2921_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3081_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3062_ = v___x_3059_;
v_isShared_3063_ = v_isSharedCheck_3081_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3081_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v_snd_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3079_; 
v_snd_3064_ = lean_ctor_get(v_a_3060_, 1);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_a_3060_);
if (v_isSharedCheck_3079_ == 0)
{
lean_object* v_unused_3080_; 
v_unused_3080_ = lean_ctor_get(v_a_3060_, 0);
lean_dec(v_unused_3080_);
v___x_3066_ = v_a_3060_;
v_isShared_3067_ = v_isSharedCheck_3079_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_snd_3064_);
lean_dec(v_a_3060_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3079_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3074_; 
v___x_3068_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8));
v___x_3069_ = lean_string_append(v_rootName_3050_, v___x_3068_);
v___x_3070_ = 1;
v___x_3071_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*1, v___x_3070_);
lean_inc_ref(v_a_2921_);
v___x_3072_ = lean_apply_2(v_a_2921_, v___x_3071_, lean_box(0));
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v___x_3072_);
v___x_3074_ = v___x_3066_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_snd_3064_);
v___x_3074_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3076_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v___x_3074_);
v___x_3076_ = v___x_3062_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_3050_);
return v___x_3059_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2923_) == 0)
{
lean_object* v___x_3082_; uint8_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3088_; 
lean_dec_ref_known(v_toUpdate_2923_, 5);
lean_dec(v_snd_3053_);
lean_dec_ref(v_rootName_3050_);
v___x_3082_ = lean_io_error_to_string(v_a_3054_);
v___x_3083_ = 3;
v___x_3084_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set_uint8(v___x_3084_, sizeof(void*)*1, v___x_3083_);
lean_inc_ref(v_a_2921_);
v___x_3085_ = lean_apply_2(v_a_2921_, v___x_3084_, lean_box(0));
v___x_3086_ = lean_box(0);
if (v_isShared_3057_ == 0)
{
lean_ctor_set_tag(v___x_3056_, 1);
lean_ctor_set(v___x_3056_, 0, v___x_3086_);
v___x_3088_ = v___x_3056_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3090_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_3091_ = lean_string_append(v_rootName_3050_, v___x_3090_);
v___x_3092_ = lean_io_error_to_string(v_a_3054_);
v___x_3093_ = lean_string_append(v___x_3091_, v___x_3092_);
lean_dec_ref(v___x_3092_);
v___x_3094_ = 2;
v___x_3095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3095_, 0, v___x_3093_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*1, v___x_3094_);
lean_inc_ref(v_a_2921_);
v___x_3096_ = lean_apply_2(v_a_2921_, v___x_3095_, lean_box(0));
v___x_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
lean_ctor_set(v___x_3097_, 1, v_snd_3053_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3097_);
v___x_3099_ = v___x_3056_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v_packagesDir_x3f_3103_; lean_object* v_packages_3104_; lean_object* v___x_3105_; 
lean_dec_ref(v_rootName_3050_);
v_a_3102_ = lean_ctor_get(v_fst_3052_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v_fst_3052_, 1);
v_packagesDir_x3f_3103_ = lean_ctor_get(v_a_3102_, 2);
lean_inc(v_packagesDir_x3f_3103_);
v_packages_3104_ = lean_ctor_get(v_a_3102_, 3);
lean_inc_ref(v_packages_3104_);
lean_dec(v_a_3102_);
lean_inc(v_toUpdate_2923_);
v___x_3105_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___lam__0(v_toUpdate_2923_, v___x_2995_, v___x_2954_, v_packages_3104_, v_snd_3053_, v_a_2921_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
if (lean_obj_tag(v_toUpdate_2923_) == 0)
{
lean_object* v_snd_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v_snd_3107_ = lean_ctor_get(v_a_3106_, 1);
lean_inc(v_snd_3107_);
lean_dec(v_a_3106_);
v___x_3108_ = lean_array_get_size(v_packages_3104_);
v___x_3109_ = lean_nat_dec_lt(v___x_2954_, v___x_3108_);
if (v___x_3109_ == 0)
{
lean_dec_ref_known(v_toUpdate_2923_, 5);
lean_dec_ref(v_packages_3104_);
v_packagesDir_x3f_3026_ = v_packagesDir_x3f_3103_;
v___y_3027_ = v_snd_3107_;
v___y_3028_ = v_a_2921_;
goto v___jp_3025_;
}
else
{
lean_object* v___x_3110_; size_t v___x_3111_; size_t v___x_3112_; lean_object* v___x_3113_; 
v___x_3110_ = lean_box(0);
v___x_3111_ = ((size_t)0ULL);
v___x_3112_ = lean_usize_of_nat(v___x_3108_);
v___x_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_2923_, v_packages_3104_, v___x_3111_, v___x_3112_, v___x_3110_, v_snd_3107_);
lean_dec_ref(v_packages_3104_);
lean_dec_ref_known(v_toUpdate_2923_, 5);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v_snd_3115_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v_snd_3115_ = lean_ctor_get(v_a_3114_, 1);
lean_inc(v_snd_3115_);
lean_dec(v_a_3114_);
v_packagesDir_x3f_3026_ = v_packagesDir_x3f_3103_;
v___y_3027_ = v_snd_3115_;
v___y_3028_ = v_a_2921_;
goto v___jp_3025_;
}
else
{
lean_dec(v_packagesDir_x3f_3103_);
return v___x_3113_;
}
}
}
else
{
lean_object* v_snd_3116_; 
lean_dec_ref(v_packages_3104_);
v_snd_3116_ = lean_ctor_get(v_a_3106_, 1);
lean_inc(v_snd_3116_);
lean_dec(v_a_3106_);
v_packagesDir_x3f_3026_ = v_packagesDir_x3f_3103_;
v___y_3027_ = v_snd_3116_;
v___y_3028_ = v_a_2921_;
goto v___jp_3025_;
}
}
else
{
lean_dec_ref(v_packages_3104_);
lean_dec(v_packagesDir_x3f_3103_);
lean_dec(v_toUpdate_2923_);
return v___x_3105_;
}
}
}
v___jp_3119_:
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_3121_ == 0)
{
v_fst_3052_ = v_val_3120_;
v_snd_3053_ = v_a_2924_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3122_; size_t v___x_3123_; size_t v___x_3124_; lean_object* v___x_3125_; 
v___x_3122_ = lean_box(0);
v___x_3123_ = ((size_t)0ULL);
v___x_3124_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_3118_, v___x_3123_, v___x_3124_, v___x_3122_, v_a_2921_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_dec_ref_known(v___x_3125_, 1);
v_fst_3052_ = v_val_3120_;
v_snd_3053_ = v_a_2924_;
goto v___jp_3051_;
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v_val_3120_);
lean_dec_ref(v_rootName_3050_);
lean_dec(v_a_2924_);
lean_dec(v_toUpdate_2923_);
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
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2921_ = stack[0].m_obj;
lean_object* v_ws_2922_ = stack[1].m_obj;
lean_object* v_toUpdate_2923_ = stack[2].m_obj;
lean_object* v_a_2924_ = stack[3].m_obj;
lean_object* v_res_3151_;
v_res_3151_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_2921_, v_ws_2922_, v_toUpdate_2923_, v_a_2924_);
stack->m_obj
 = v_res_3151_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_3152_, lean_object* v_ws_3153_, lean_object* v_toUpdate_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_3152_, v_ws_3153_, v_toUpdate_3154_, v_a_3155_);
lean_dec_ref(v_ws_3153_);
lean_dec_ref(v_a_3152_);
return v_res_3157_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_a_3158_, lean_object* v_ws_3159_, lean_object* v_rootDeps_3160_){
_start:
{
lean_object* v___y_3163_; lean_object* v___y_3169_; uint8_t v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3177_; lean_object* v___y_3178_; uint8_t v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3191_; lean_object* v___y_3192_; uint8_t v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v_lakeEnv_3199_; lean_object* v_lakeArgs_x3f_3200_; lean_object* v_packages_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v_baseName_3204_; lean_object* v_dir_3205_; lean_object* v_config_3206_; lean_object* v___x_3207_; lean_object* v_rootToolchainFile_3208_; uint8_t v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3356_; uint8_t v___y_3357_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_lakeEnv_3199_ = lean_ctor_get(v_ws_3159_, 0);
lean_inc_ref(v_lakeEnv_3199_);
v_lakeArgs_x3f_3200_ = lean_ctor_get(v_ws_3159_, 3);
lean_inc(v_lakeArgs_x3f_3200_);
v_packages_3201_ = lean_ctor_get(v_ws_3159_, 4);
lean_inc_ref(v_packages_3201_);
lean_dec_ref(v_ws_3159_);
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = lean_array_fget(v_packages_3201_, v___x_3202_);
lean_dec_ref(v_packages_3201_);
v_baseName_3204_ = lean_ctor_get(v___x_3203_, 1);
lean_inc(v_baseName_3204_);
v_dir_3205_ = lean_ctor_get(v___x_3203_, 4);
lean_inc_ref_n(v_dir_3205_, 3);
v_config_3206_ = lean_ctor_get(v___x_3203_, 6);
lean_inc_ref(v_config_3206_);
lean_dec(v___x_3203_);
v___x_3207_ = l_Lake_toolchainFileName;
v_rootToolchainFile_3208_ = l_Lake_joinRelative(v_dir_3205_, v___x_3207_);
v___x_3361_ = l_System_FilePath_join(v_dir_3205_, v___x_3207_);
v___x_3362_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3361_);
lean_dec_ref(v___x_3361_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3415_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3365_ = v___x_3362_;
v_isShared_3366_ = v_isSharedCheck_3415_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3415_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v_src_3368_; lean_object* v_tc_x3f_3369_; lean_object* v_clashes_3370_; uint8_t v_fixed_3371_; uint8_t v_fixedToolchain_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_fixedToolchain_3394_ = lean_ctor_get_uint8(v_config_3206_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_3206_);
v___x_3395_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___x_3396_ = lean_array_get_size(v_rootDeps_3160_);
v___x_3397_ = lean_nat_dec_lt(v___x_3202_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_dec_ref(v_dir_3205_);
lean_inc(v_a_3363_);
v_src_3368_ = v_baseName_3204_;
v_tc_x3f_3369_ = v_a_3363_;
v_clashes_3370_ = v___x_3395_;
v_fixed_3371_ = v_fixedToolchain_3394_;
goto v___jp_3367_;
}
else
{
lean_object* v___x_3398_; size_t v___x_3399_; size_t v___x_3400_; lean_object* v___x_3401_; 
lean_inc(v_a_3363_);
v___x_3398_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3398_, 0, v_baseName_3204_);
lean_ctor_set(v___x_3398_, 1, v_a_3363_);
lean_ctor_set(v___x_3398_, 2, v___x_3395_);
lean_ctor_set_uint8(v___x_3398_, sizeof(void*)*3, v_fixedToolchain_3394_);
v___x_3399_ = ((size_t)0ULL);
v___x_3400_ = lean_usize_of_nat(v___x_3396_);
v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3205_, v_rootDeps_3160_, v___x_3399_, v___x_3400_, v___x_3398_, v_a_3158_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v_src_3403_; lean_object* v_tc_x3f_3404_; lean_object* v_clashes_3405_; uint8_t v_fixed_3406_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3401_, 1);
v_src_3403_ = lean_ctor_get(v_a_3402_, 0);
lean_inc(v_src_3403_);
v_tc_x3f_3404_ = lean_ctor_get(v_a_3402_, 1);
lean_inc(v_tc_x3f_3404_);
v_clashes_3405_ = lean_ctor_get(v_a_3402_, 2);
lean_inc_ref(v_clashes_3405_);
v_fixed_3406_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*3);
lean_dec(v_a_3402_);
v_src_3368_ = v_src_3403_;
v_tc_x3f_3369_ = v_tc_x3f_3404_;
v_clashes_3370_ = v_clashes_3405_;
v_fixed_3371_ = v_fixed_3406_;
goto v___jp_3367_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_del_object(v___x_3365_);
lean_dec(v_a_3363_);
lean_dec_ref(v_rootToolchainFile_3208_);
lean_dec(v_lakeArgs_x3f_3200_);
lean_dec_ref(v_lakeEnv_3199_);
v_a_3407_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3401_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3401_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
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
v___jp_3367_:
{
lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = lean_array_get_size(v_clashes_3370_);
v___x_3373_ = lean_nat_dec_lt(v___x_3202_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_dec_ref(v_clashes_3370_);
lean_dec(v_src_3368_);
if (lean_obj_tag(v_tc_x3f_3369_) == 1)
{
if (lean_obj_tag(v_a_3363_) == 0)
{
lean_object* v_val_3374_; 
lean_del_object(v___x_3365_);
v_val_3374_ = lean_ctor_get(v_tc_x3f_3369_, 0);
lean_inc(v_val_3374_);
lean_dec_ref_known(v_tc_x3f_3369_, 1);
v___y_3356_ = v_val_3374_;
v___y_3357_ = v___x_3373_;
goto v___jp_3355_;
}
else
{
lean_object* v_val_3375_; lean_object* v_val_3376_; uint8_t v___x_3377_; 
v_val_3375_ = lean_ctor_get(v_tc_x3f_3369_, 0);
lean_inc_n(v_val_3375_, 2);
lean_dec_ref_known(v_tc_x3f_3369_, 1);
v_val_3376_ = lean_ctor_get(v_a_3363_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v_a_3363_, 1);
v___x_3377_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3376_, v_val_3375_);
if (v___x_3377_ == 0)
{
lean_del_object(v___x_3365_);
v___y_3356_ = v_val_3375_;
v___y_3357_ = v___x_3377_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
lean_dec(v_val_3375_);
lean_dec_ref(v_rootToolchainFile_3208_);
lean_dec(v_lakeArgs_x3f_3200_);
lean_dec_ref(v_lakeEnv_3199_);
v___x_3378_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15));
lean_inc_ref(v_a_3158_);
v___x_3379_ = lean_apply_2(v_a_3158_, v___x_3378_, lean_box(0));
v___x_3380_ = lean_box(0);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3380_);
v___x_3382_ = v___x_3365_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
lean_dec(v_tc_x3f_3369_);
lean_dec(v_a_3363_);
lean_dec_ref(v_rootToolchainFile_3208_);
lean_dec(v_lakeArgs_x3f_3200_);
lean_dec_ref(v_lakeEnv_3199_);
v___x_3384_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17));
lean_inc_ref(v_a_3158_);
v___x_3385_ = lean_apply_2(v_a_3158_, v___x_3384_, lean_box(0));
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3385_);
v___x_3387_ = v___x_3365_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_del_object(v___x_3365_);
lean_dec(v_a_3363_);
lean_dec_ref(v_rootToolchainFile_3208_);
lean_dec(v_lakeArgs_x3f_3200_);
lean_dec_ref(v_lakeEnv_3199_);
if (lean_obj_tag(v_tc_x3f_3369_) == 1)
{
if (v_fixed_3371_ == 0)
{
lean_object* v_val_3389_; lean_object* v___x_3390_; 
v_val_3389_ = lean_ctor_get(v_tc_x3f_3369_, 0);
lean_inc(v_val_3389_);
lean_dec_ref_known(v_tc_x3f_3369_, 1);
v___x_3390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3191_ = v_val_3389_;
v___y_3192_ = v___x_3372_;
v___y_3193_ = v___x_3373_;
v___y_3194_ = v_clashes_3370_;
v___y_3195_ = v_src_3368_;
v___y_3196_ = v___x_3390_;
goto v___jp_3190_;
}
else
{
lean_object* v_val_3391_; lean_object* v___x_3392_; 
v_val_3391_ = lean_ctor_get(v_tc_x3f_3369_, 0);
lean_inc(v_val_3391_);
lean_dec_ref_known(v_tc_x3f_3369_, 1);
v___x_3392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3191_ = v_val_3391_;
v___y_3192_ = v___x_3372_;
v___y_3193_ = v___x_3373_;
v___y_3194_ = v_clashes_3370_;
v___y_3195_ = v_src_3368_;
v___y_3196_ = v___x_3392_;
goto v___jp_3190_;
}
}
else
{
lean_object* v___x_3393_; 
lean_dec(v_tc_x3f_3369_);
lean_dec(v_src_3368_);
v___x_3393_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
v___y_3169_ = v___x_3372_;
v___y_3170_ = v___x_3373_;
v___y_3171_ = v_clashes_3370_;
v___y_3172_ = v___x_3393_;
goto v___jp_3168_;
}
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3428_; 
lean_dec_ref(v_rootToolchainFile_3208_);
lean_dec_ref(v_config_3206_);
lean_dec_ref(v_dir_3205_);
lean_dec(v_baseName_3204_);
lean_dec(v_lakeArgs_x3f_3200_);
lean_dec_ref(v_lakeEnv_3199_);
v_a_3416_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3418_ = v___x_3362_;
v_isShared_3419_ = v_isSharedCheck_3428_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3362_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3428_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; uint8_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
v___x_3420_ = lean_io_error_to_string(v_a_3416_);
v___x_3421_ = 3;
v___x_3422_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set_uint8(v___x_3422_, sizeof(void*)*1, v___x_3421_);
lean_inc_ref(v_a_3158_);
v___x_3423_ = lean_apply_2(v_a_3158_, v___x_3422_, lean_box(0));
v___x_3424_ = lean_box(0);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3424_);
v___x_3426_ = v___x_3418_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
v___jp_3162_:
{
uint8_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3164_ = 2;
v___x_3165_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3165_, 0, v___y_3163_);
lean_ctor_set_uint8(v___x_3165_, sizeof(void*)*1, v___x_3164_);
lean_inc_ref(v_a_3158_);
v___x_3166_ = lean_apply_2(v_a_3158_, v___x_3165_, lean_box(0));
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
v___jp_3168_:
{
if (v___y_3170_ == 0)
{
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3169_);
v___y_3163_ = v___y_3172_;
goto v___jp_3162_;
}
else
{
size_t v___x_3173_; size_t v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = ((size_t)0ULL);
v___x_3174_ = lean_usize_of_nat(v___y_3169_);
v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3169_, v___y_3171_, v___x_3173_, v___x_3174_, v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3169_);
v___y_3163_ = v___x_3175_;
goto v___jp_3162_;
}
}
v___jp_3176_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
lean_inc_ref(v___y_3177_);
v___x_3184_ = lean_string_append(v___y_3177_, v___y_3183_);
lean_dec_ref(v___y_3183_);
v___x_3185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3186_ = lean_string_append(v___x_3184_, v___x_3185_);
v___x_3187_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3182_, v___y_3179_);
v___x_3188_ = lean_string_append(v___x_3186_, v___x_3187_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = lean_string_append(v___x_3188_, v___y_3180_);
v___y_3169_ = v___y_3178_;
v___y_3170_ = v___y_3179_;
v___y_3171_ = v___y_3181_;
v___y_3172_ = v___x_3189_;
goto v___jp_3168_;
}
v___jp_3190_:
{
lean_object* v___x_3197_; lean_object* v_toString_3198_; 
v___x_3197_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_3198_ = lean_ctor_get(v___y_3191_, 0);
lean_inc_ref(v_toString_3198_);
lean_dec_ref(v___y_3191_);
v___y_3177_ = v___x_3197_;
v___y_3178_ = v___y_3192_;
v___y_3179_ = v___y_3193_;
v___y_3180_ = v___y_3196_;
v___y_3181_ = v___y_3194_;
v___y_3182_ = v___y_3195_;
v___y_3183_ = v_toString_3198_;
goto v___jp_3176_;
}
v___jp_3209_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_inc_ref(v___y_3211_);
v___x_3214_ = lean_string_append(v___y_3211_, v___y_3213_);
v___x_3215_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_3216_ = lean_string_append(v___x_3214_, v___x_3215_);
v___x_3217_ = 1;
v___x_3218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*1, v___x_3217_);
lean_inc_ref(v_a_3158_);
v___x_3219_ = lean_apply_2(v_a_3158_, v___x_3218_, lean_box(0));
v___x_3220_ = l_IO_FS_writeFile(v_rootToolchainFile_3208_, v___y_3213_);
lean_dec_ref(v_rootToolchainFile_3208_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_dec_ref_known(v___x_3220_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_3200_) == 1)
{
lean_object* v_elan_x3f_3221_; 
v_elan_x3f_3221_ = lean_ctor_get(v_lakeEnv_3199_, 2);
if (lean_obj_tag(v_elan_x3f_3221_) == 1)
{
lean_object* v_val_3222_; lean_object* v_val_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v_elan_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v_val_3222_ = lean_ctor_get(v_lakeArgs_x3f_3200_, 0);
lean_inc(v_val_3222_);
lean_dec_ref_known(v_lakeArgs_x3f_3200_, 1);
v_val_3223_ = lean_ctor_get(v_elan_x3f_3221_, 0);
v___x_3224_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_3158_);
v___x_3225_ = lean_apply_2(v_a_3158_, v___x_3224_, lean_box(0));
v___x_3226_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_3227_ = lean_ctor_get(v_val_3223_, 1);
lean_inc_ref(v_elan_3227_);
v___x_3228_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_3229_ = lean_unsigned_to_nat(4u);
v___x_3230_ = lean_mk_empty_array_with_capacity(v___x_3229_);
lean_dec_ref(v___x_3230_);
v___x_3231_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_3232_ = lean_array_push(v___x_3231_, v___y_3213_);
v___x_3233_ = lean_array_push(v___x_3232_, v___x_3228_);
v___x_3234_ = l_Array_append___redArg(v___x_3233_, v_val_3222_);
lean_dec(v_val_3222_);
v___x_3235_ = lean_box(0);
v___x_3236_ = l_Lake_Env_noToolchainVars(v_lakeEnv_3199_);
v___x_3237_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3237_, 0, v___x_3226_);
lean_ctor_set(v___x_3237_, 1, v_elan_3227_);
lean_ctor_set(v___x_3237_, 2, v___x_3234_);
lean_ctor_set(v___x_3237_, 3, v___x_3235_);
lean_ctor_set(v___x_3237_, 4, v___x_3236_);
lean_ctor_set_uint8(v___x_3237_, sizeof(void*)*5, v___y_3210_);
lean_ctor_set_uint8(v___x_3237_, sizeof(void*)*5 + 1, v___y_3212_);
v___x_3238_ = lean_io_process_spawn(v___x_3237_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3240_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v___x_3240_ = lean_io_process_child_wait(v___x_3226_, v_a_3239_);
lean_dec(v_a_3239_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; uint32_t v___x_3242_; uint8_t v___x_3243_; lean_object* v___x_3244_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref_known(v___x_3240_, 1);
v___x_3242_ = lean_unbox_uint32(v_a_3241_);
lean_dec(v_a_3241_);
v___x_3243_ = lean_uint32_to_uint8(v___x_3242_);
v___x_3244_ = lean_io_exit(v___x_3243_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3265_; 
v_a_3253_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3255_ = v___x_3244_;
v_isShared_3256_ = v_isSharedCheck_3265_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3244_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3265_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3257_; uint8_t v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3263_; 
v___x_3257_ = lean_io_error_to_string(v_a_3253_);
v___x_3258_ = 3;
v___x_3259_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set_uint8(v___x_3259_, sizeof(void*)*1, v___x_3258_);
lean_inc_ref(v_a_3158_);
v___x_3260_ = lean_apply_2(v_a_3158_, v___x_3259_, lean_box(0));
v___x_3261_ = lean_box(0);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3261_);
v___x_3263_ = v___x_3255_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3278_; 
v_a_3266_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3268_ = v___x_3240_;
v_isShared_3269_ = v_isSharedCheck_3278_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3240_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3278_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; uint8_t v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3270_ = lean_io_error_to_string(v_a_3266_);
v___x_3271_ = 3;
v___x_3272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3272_, 0, v___x_3270_);
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*1, v___x_3271_);
lean_inc_ref(v_a_3158_);
v___x_3273_ = lean_apply_2(v_a_3158_, v___x_3272_, lean_box(0));
v___x_3274_ = lean_box(0);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3274_);
v___x_3276_ = v___x_3268_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3291_; 
v_a_3279_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3281_ = v___x_3238_;
v_isShared_3282_ = v_isSharedCheck_3291_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3238_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3291_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3283_; uint8_t v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3283_ = lean_io_error_to_string(v_a_3279_);
v___x_3284_ = 3;
v___x_3285_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set_uint8(v___x_3285_, sizeof(void*)*1, v___x_3284_);
lean_inc_ref(v_a_3158_);
v___x_3286_ = lean_apply_2(v_a_3158_, v___x_3285_, lean_box(0));
v___x_3287_ = lean_box(0);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v___x_3287_);
v___x_3289_ = v___x_3281_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; 
lean_dec_ref_known(v_lakeArgs_x3f_3200_, 1);
lean_dec_ref(v___y_3213_);
lean_dec_ref(v_lakeEnv_3199_);
v___x_3292_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_3158_);
v___x_3293_ = lean_apply_2(v_a_3158_, v___x_3292_, lean_box(0));
v___x_3294_ = 4;
v___x_3295_ = lean_io_exit(v___x_3294_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3295_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3316_; 
v_a_3304_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3306_ = v___x_3295_;
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3295_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; uint8_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3314_; 
v___x_3308_ = lean_io_error_to_string(v_a_3304_);
v___x_3309_ = 3;
v___x_3310_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*1, v___x_3309_);
lean_inc_ref(v_a_3158_);
v___x_3311_ = lean_apply_2(v_a_3158_, v___x_3310_, lean_box(0));
v___x_3312_ = lean_box(0);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v___x_3312_);
v___x_3314_ = v___x_3306_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3312_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; uint8_t v___x_3319_; lean_object* v___x_3320_; 
lean_dec_ref(v___y_3213_);
lean_dec(v_lakeArgs_x3f_3200_);
lean_dec_ref(v_lakeEnv_3199_);
v___x_3317_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_3158_);
v___x_3318_ = lean_apply_2(v_a_3158_, v___x_3317_, lean_box(0));
v___x_3319_ = 4;
v___x_3320_ = lean_io_exit(v___x_3319_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3320_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3320_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3341_; 
v_a_3329_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3331_ = v___x_3320_;
v_isShared_3332_ = v_isSharedCheck_3341_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3320_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3341_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; uint8_t v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3333_ = lean_io_error_to_string(v_a_3329_);
v___x_3334_ = 3;
v___x_3335_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*1, v___x_3334_);
lean_inc_ref(v_a_3158_);
v___x_3336_ = lean_apply_2(v_a_3158_, v___x_3335_, lean_box(0));
v___x_3337_ = lean_box(0);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3337_);
v___x_3339_ = v___x_3331_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref(v___y_3213_);
lean_dec(v_lakeArgs_x3f_3200_);
lean_dec_ref(v_lakeEnv_3199_);
v_a_3342_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3344_ = v___x_3220_;
v_isShared_3345_ = v_isSharedCheck_3354_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3220_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3354_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3352_; 
v___x_3346_ = lean_io_error_to_string(v_a_3342_);
v___x_3347_ = 3;
v___x_3348_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set_uint8(v___x_3348_, sizeof(void*)*1, v___x_3347_);
lean_inc_ref(v_a_3158_);
v___x_3349_ = lean_apply_2(v_a_3158_, v___x_3348_, lean_box(0));
v___x_3350_ = lean_box(0);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3350_);
v___x_3352_ = v___x_3344_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3350_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
v___jp_3355_:
{
uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v_toString_3360_; 
v___x_3358_ = 1;
v___x_3359_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_3360_ = lean_ctor_get(v___y_3356_, 0);
lean_inc_ref(v_toString_3360_);
lean_dec_ref(v___y_3356_);
v___y_3210_ = v___x_3358_;
v___y_3211_ = v___x_3359_;
v___y_3212_ = v___y_3357_;
v___y_3213_ = v_toString_3360_;
goto v___jp_3209_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3158_ = stack[0].m_obj;
lean_object* v_ws_3159_ = stack[1].m_obj;
lean_object* v_rootDeps_3160_ = stack[2].m_obj;
lean_object* v_res_3429_;
v_res_3429_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3158_, v_ws_3159_, v_rootDeps_3160_);
stack->m_obj
 = v_res_3429_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_a_3430_, lean_object* v_ws_3431_, lean_object* v_rootDeps_3432_, lean_object* v_a_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3430_, v_ws_3431_, v_rootDeps_3432_);
lean_dec_ref(v_rootDeps_3432_);
lean_dec_ref(v_a_3430_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(lean_object* v_msg_3435_){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_box(1);
v___x_3437_ = lean_panic_fn_borrowed(v___x_3436_, v_msg_3435_);
return v___x_3437_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3441_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3442_ = lean_unsigned_to_nat(35u);
v___x_3443_ = lean_unsigned_to_nat(182u);
v___x_3444_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3445_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3446_ = l_mkPanicMessageWithDecl(v___x_3445_, v___x_3444_, v___x_3443_, v___x_3442_, v___x_3441_);
return v___x_3446_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3447_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3448_ = lean_unsigned_to_nat(21u);
v___x_3449_ = lean_unsigned_to_nat(183u);
v___x_3450_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3451_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3452_ = l_mkPanicMessageWithDecl(v___x_3451_, v___x_3450_, v___x_3449_, v___x_3448_, v___x_3447_);
return v___x_3452_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3455_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3456_ = lean_unsigned_to_nat(35u);
v___x_3457_ = lean_unsigned_to_nat(276u);
v___x_3458_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3459_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3460_ = l_mkPanicMessageWithDecl(v___x_3459_, v___x_3458_, v___x_3457_, v___x_3456_, v___x_3455_);
return v___x_3460_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3461_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3462_ = lean_unsigned_to_nat(21u);
v___x_3463_ = lean_unsigned_to_nat(277u);
v___x_3464_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3465_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3466_ = l_mkPanicMessageWithDecl(v___x_3465_, v___x_3464_, v___x_3463_, v___x_3462_, v___x_3461_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(lean_object* v_k_3467_, lean_object* v_v_3468_, lean_object* v_t_3469_){
_start:
{
if (lean_obj_tag(v_t_3469_) == 0)
{
lean_object* v_size_3470_; lean_object* v_k_3471_; lean_object* v_v_3472_; lean_object* v_l_3473_; lean_object* v_r_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3830_; 
v_size_3470_ = lean_ctor_get(v_t_3469_, 0);
v_k_3471_ = lean_ctor_get(v_t_3469_, 1);
v_v_3472_ = lean_ctor_get(v_t_3469_, 2);
v_l_3473_ = lean_ctor_get(v_t_3469_, 3);
v_r_3474_ = lean_ctor_get(v_t_3469_, 4);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_t_3469_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3476_ = v_t_3469_;
v_isShared_3477_ = v_isSharedCheck_3830_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_r_3474_);
lean_inc(v_l_3473_);
lean_inc(v_v_3472_);
lean_inc(v_k_3471_);
lean_inc(v_size_3470_);
lean_dec(v_t_3469_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3830_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_string_compare(v_k_3467_, v_k_3471_);
switch(v___x_3478_)
{
case 0:
{
lean_object* v___x_3479_; 
lean_dec(v_size_3470_);
v___x_3479_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3467_, v_v_3468_, v_l_3473_);
if (lean_obj_tag(v_r_3474_) == 0)
{
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_size_3480_; lean_object* v_size_3481_; lean_object* v_k_3482_; lean_object* v_v_3483_; lean_object* v_l_3484_; lean_object* v_r_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v_size_3480_ = lean_ctor_get(v_r_3474_, 0);
v_size_3481_ = lean_ctor_get(v___x_3479_, 0);
v_k_3482_ = lean_ctor_get(v___x_3479_, 1);
v_v_3483_ = lean_ctor_get(v___x_3479_, 2);
v_l_3484_ = lean_ctor_get(v___x_3479_, 3);
v_r_3485_ = lean_ctor_get(v___x_3479_, 4);
lean_inc(v_r_3485_);
v___x_3486_ = lean_unsigned_to_nat(3u);
v___x_3487_ = lean_nat_mul(v___x_3486_, v_size_3480_);
v___x_3488_ = lean_nat_dec_lt(v___x_3487_, v_size_3481_);
lean_dec(v___x_3487_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3493_; 
lean_dec(v_r_3485_);
v___x_3489_ = lean_unsigned_to_nat(1u);
v___x_3490_ = lean_nat_add(v___x_3489_, v_size_3481_);
v___x_3491_ = lean_nat_add(v___x_3490_, v_size_3480_);
lean_dec(v___x_3490_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 3, v___x_3479_);
lean_ctor_set(v___x_3476_, 0, v___x_3491_);
v___x_3493_ = v___x_3476_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3494_, 3, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3494_, 4, v_r_3474_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
else
{
lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3566_; 
lean_inc(v_l_3484_);
lean_inc(v_v_3483_);
lean_inc(v_k_3482_);
lean_inc(v_size_3481_);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; lean_object* v_unused_3568_; lean_object* v_unused_3569_; lean_object* v_unused_3570_; lean_object* v_unused_3571_; 
v_unused_3567_ = lean_ctor_get(v___x_3479_, 4);
lean_dec(v_unused_3567_);
v_unused_3568_ = lean_ctor_get(v___x_3479_, 3);
lean_dec(v_unused_3568_);
v_unused_3569_ = lean_ctor_get(v___x_3479_, 2);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v___x_3479_, 1);
lean_dec(v_unused_3570_);
v_unused_3571_ = lean_ctor_get(v___x_3479_, 0);
lean_dec(v_unused_3571_);
v___x_3496_ = v___x_3479_;
v_isShared_3497_ = v_isSharedCheck_3566_;
goto v_resetjp_3495_;
}
else
{
lean_dec(v___x_3479_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3566_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
if (lean_obj_tag(v_l_3484_) == 0)
{
if (lean_obj_tag(v_r_3485_) == 0)
{
lean_object* v_size_3498_; lean_object* v_size_3499_; lean_object* v_k_3500_; lean_object* v_v_3501_; lean_object* v_l_3502_; lean_object* v_r_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v_size_3498_ = lean_ctor_get(v_l_3484_, 0);
v_size_3499_ = lean_ctor_get(v_r_3485_, 0);
v_k_3500_ = lean_ctor_get(v_r_3485_, 1);
v_v_3501_ = lean_ctor_get(v_r_3485_, 2);
v_l_3502_ = lean_ctor_get(v_r_3485_, 3);
v_r_3503_ = lean_ctor_get(v_r_3485_, 4);
v___x_3504_ = lean_unsigned_to_nat(2u);
v___x_3505_ = lean_nat_mul(v___x_3504_, v_size_3498_);
v___x_3506_ = lean_nat_dec_lt(v_size_3499_, v___x_3505_);
lean_dec(v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3536_; 
lean_inc(v_r_3503_);
lean_inc(v_l_3502_);
lean_inc(v_v_3501_);
lean_inc(v_k_3500_);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_r_3485_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; lean_object* v_unused_3538_; lean_object* v_unused_3539_; lean_object* v_unused_3540_; lean_object* v_unused_3541_; 
v_unused_3537_ = lean_ctor_get(v_r_3485_, 4);
lean_dec(v_unused_3537_);
v_unused_3538_ = lean_ctor_get(v_r_3485_, 3);
lean_dec(v_unused_3538_);
v_unused_3539_ = lean_ctor_get(v_r_3485_, 2);
lean_dec(v_unused_3539_);
v_unused_3540_ = lean_ctor_get(v_r_3485_, 1);
lean_dec(v_unused_3540_);
v_unused_3541_ = lean_ctor_get(v_r_3485_, 0);
lean_dec(v_unused_3541_);
v___x_3508_ = v_r_3485_;
v_isShared_3509_ = v_isSharedCheck_3536_;
goto v_resetjp_3507_;
}
else
{
lean_dec(v_r_3485_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3536_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___x_3524_; lean_object* v___y_3526_; 
v___x_3510_ = lean_unsigned_to_nat(1u);
v___x_3511_ = lean_nat_add(v___x_3510_, v_size_3481_);
lean_dec(v_size_3481_);
v___x_3512_ = lean_nat_add(v___x_3511_, v_size_3480_);
lean_dec(v___x_3511_);
v___x_3524_ = lean_nat_add(v___x_3510_, v_size_3498_);
if (lean_obj_tag(v_l_3502_) == 0)
{
lean_object* v_size_3534_; 
v_size_3534_ = lean_ctor_get(v_l_3502_, 0);
lean_inc(v_size_3534_);
v___y_3526_ = v_size_3534_;
goto v___jp_3525_;
}
else
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_unsigned_to_nat(0u);
v___y_3526_ = v___x_3535_;
goto v___jp_3525_;
}
v___jp_3513_:
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
v___x_3517_ = lean_nat_add(v___y_3514_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec(v___y_3514_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 4, v_r_3474_);
lean_ctor_set(v___x_3508_, 3, v_r_3503_);
lean_ctor_set(v___x_3508_, 2, v_v_3472_);
lean_ctor_set(v___x_3508_, 1, v_k_3471_);
lean_ctor_set(v___x_3508_, 0, v___x_3517_);
v___x_3519_ = v___x_3508_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3523_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3523_, 3, v_r_3503_);
lean_ctor_set(v_reuseFailAlloc_3523_, 4, v_r_3474_);
v___x_3519_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 4, v___x_3519_);
lean_ctor_set(v___x_3496_, 3, v___y_3515_);
lean_ctor_set(v___x_3496_, 2, v_v_3501_);
lean_ctor_set(v___x_3496_, 1, v_k_3500_);
lean_ctor_set(v___x_3496_, 0, v___x_3512_);
v___x_3521_ = v___x_3496_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_k_3500_);
lean_ctor_set(v_reuseFailAlloc_3522_, 2, v_v_3501_);
lean_ctor_set(v_reuseFailAlloc_3522_, 3, v___y_3515_);
lean_ctor_set(v_reuseFailAlloc_3522_, 4, v___x_3519_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
v___jp_3525_:
{
lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3527_ = lean_nat_add(v___x_3524_, v___y_3526_);
lean_dec(v___y_3526_);
lean_dec(v___x_3524_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v_l_3502_);
lean_ctor_set(v___x_3476_, 3, v_l_3484_);
lean_ctor_set(v___x_3476_, 2, v_v_3483_);
lean_ctor_set(v___x_3476_, 1, v_k_3482_);
lean_ctor_set(v___x_3476_, 0, v___x_3527_);
v___x_3529_ = v___x_3476_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3527_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_k_3482_);
lean_ctor_set(v_reuseFailAlloc_3533_, 2, v_v_3483_);
lean_ctor_set(v_reuseFailAlloc_3533_, 3, v_l_3484_);
lean_ctor_set(v_reuseFailAlloc_3533_, 4, v_l_3502_);
v___x_3529_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_nat_add(v___x_3510_, v_size_3480_);
if (lean_obj_tag(v_r_3503_) == 0)
{
lean_object* v_size_3531_; 
v_size_3531_ = lean_ctor_get(v_r_3503_, 0);
lean_inc(v_size_3531_);
v___y_3514_ = v___x_3530_;
v___y_3515_ = v___x_3529_;
v___y_3516_ = v_size_3531_;
goto v___jp_3513_;
}
else
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_unsigned_to_nat(0u);
v___y_3514_ = v___x_3530_;
v___y_3515_ = v___x_3529_;
v___y_3516_ = v___x_3532_;
goto v___jp_3513_;
}
}
}
}
}
else
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3548_; 
lean_del_object(v___x_3476_);
v___x_3542_ = lean_unsigned_to_nat(1u);
v___x_3543_ = lean_nat_add(v___x_3542_, v_size_3481_);
lean_dec(v_size_3481_);
v___x_3544_ = lean_nat_add(v___x_3543_, v_size_3480_);
lean_dec(v___x_3543_);
v___x_3545_ = lean_nat_add(v___x_3542_, v_size_3480_);
v___x_3546_ = lean_nat_add(v___x_3545_, v_size_3499_);
lean_dec(v___x_3545_);
lean_inc_ref(v_r_3474_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 4, v_r_3474_);
lean_ctor_set(v___x_3496_, 3, v_r_3485_);
lean_ctor_set(v___x_3496_, 2, v_v_3472_);
lean_ctor_set(v___x_3496_, 1, v_k_3471_);
lean_ctor_set(v___x_3496_, 0, v___x_3546_);
v___x_3548_ = v___x_3496_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3561_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3561_, 3, v_r_3485_);
lean_ctor_set(v_reuseFailAlloc_3561_, 4, v_r_3474_);
v___x_3548_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_isSharedCheck_3555_ = !lean_is_exclusive(v_r_3474_);
if (v_isSharedCheck_3555_ == 0)
{
lean_object* v_unused_3556_; lean_object* v_unused_3557_; lean_object* v_unused_3558_; lean_object* v_unused_3559_; lean_object* v_unused_3560_; 
v_unused_3556_ = lean_ctor_get(v_r_3474_, 4);
lean_dec(v_unused_3556_);
v_unused_3557_ = lean_ctor_get(v_r_3474_, 3);
lean_dec(v_unused_3557_);
v_unused_3558_ = lean_ctor_get(v_r_3474_, 2);
lean_dec(v_unused_3558_);
v_unused_3559_ = lean_ctor_get(v_r_3474_, 1);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_r_3474_, 0);
lean_dec(v_unused_3560_);
v___x_3550_ = v_r_3474_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_dec(v_r_3474_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 4, v___x_3548_);
lean_ctor_set(v___x_3550_, 3, v_l_3484_);
lean_ctor_set(v___x_3550_, 2, v_v_3483_);
lean_ctor_set(v___x_3550_, 1, v_k_3482_);
lean_ctor_set(v___x_3550_, 0, v___x_3544_);
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_k_3482_);
lean_ctor_set(v_reuseFailAlloc_3554_, 2, v_v_3483_);
lean_ctor_set(v_reuseFailAlloc_3554_, 3, v_l_3484_);
lean_ctor_set(v_reuseFailAlloc_3554_, 4, v___x_3548_);
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
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec_ref_known(v_l_3484_, 5);
lean_del_object(v___x_3496_);
lean_dec(v_v_3483_);
lean_dec(v_k_3482_);
lean_dec(v_size_3481_);
lean_dec_ref_known(v_r_3474_, 5);
lean_del_object(v___x_3476_);
lean_dec(v_v_3472_);
lean_dec(v_k_3471_);
v___x_3562_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3);
v___x_3563_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3562_);
return v___x_3563_;
}
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_del_object(v___x_3496_);
lean_dec(v_r_3485_);
lean_dec(v_v_3483_);
lean_dec(v_k_3482_);
lean_dec(v_size_3481_);
lean_dec_ref_known(v_r_3474_, 5);
lean_del_object(v___x_3476_);
lean_dec(v_v_3472_);
lean_dec(v_k_3471_);
v___x_3564_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4);
v___x_3565_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3564_);
return v___x_3565_;
}
}
}
}
else
{
lean_object* v_size_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3576_; 
v_size_3572_ = lean_ctor_get(v_r_3474_, 0);
v___x_3573_ = lean_unsigned_to_nat(1u);
v___x_3574_ = lean_nat_add(v___x_3573_, v_size_3572_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 3, v___x_3479_);
lean_ctor_set(v___x_3476_, 0, v___x_3574_);
v___x_3576_ = v___x_3476_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3574_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3577_, 3, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3577_, 4, v_r_3474_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
else
{
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_l_3578_; 
v_l_3578_ = lean_ctor_get(v___x_3479_, 3);
if (lean_obj_tag(v_l_3578_) == 0)
{
lean_object* v_r_3579_; 
lean_inc_ref(v_l_3578_);
v_r_3579_ = lean_ctor_get(v___x_3479_, 4);
lean_inc(v_r_3579_);
if (lean_obj_tag(v_r_3579_) == 0)
{
lean_object* v_size_3580_; lean_object* v_k_3581_; lean_object* v_v_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3596_; 
v_size_3580_ = lean_ctor_get(v___x_3479_, 0);
v_k_3581_ = lean_ctor_get(v___x_3479_, 1);
v_v_3582_ = lean_ctor_get(v___x_3479_, 2);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3596_ == 0)
{
lean_object* v_unused_3597_; lean_object* v_unused_3598_; 
v_unused_3597_ = lean_ctor_get(v___x_3479_, 4);
lean_dec(v_unused_3597_);
v_unused_3598_ = lean_ctor_get(v___x_3479_, 3);
lean_dec(v_unused_3598_);
v___x_3584_ = v___x_3479_;
v_isShared_3585_ = v_isSharedCheck_3596_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_v_3582_);
lean_inc(v_k_3581_);
lean_inc(v_size_3580_);
lean_dec(v___x_3479_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3596_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v_size_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3591_; 
v_size_3586_ = lean_ctor_get(v_r_3579_, 0);
v___x_3587_ = lean_unsigned_to_nat(1u);
v___x_3588_ = lean_nat_add(v___x_3587_, v_size_3580_);
lean_dec(v_size_3580_);
v___x_3589_ = lean_nat_add(v___x_3587_, v_size_3586_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 4, v_r_3474_);
lean_ctor_set(v___x_3584_, 3, v_r_3579_);
lean_ctor_set(v___x_3584_, 2, v_v_3472_);
lean_ctor_set(v___x_3584_, 1, v_k_3471_);
lean_ctor_set(v___x_3584_, 0, v___x_3589_);
v___x_3591_ = v___x_3584_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3589_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3595_, 3, v_r_3579_);
lean_ctor_set(v_reuseFailAlloc_3595_, 4, v_r_3474_);
v___x_3591_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3593_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v___x_3591_);
lean_ctor_set(v___x_3476_, 3, v_l_3578_);
lean_ctor_set(v___x_3476_, 2, v_v_3582_);
lean_ctor_set(v___x_3476_, 1, v_k_3581_);
lean_ctor_set(v___x_3476_, 0, v___x_3588_);
v___x_3593_ = v___x_3476_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_k_3581_);
lean_ctor_set(v_reuseFailAlloc_3594_, 2, v_v_3582_);
lean_ctor_set(v_reuseFailAlloc_3594_, 3, v_l_3578_);
lean_ctor_set(v_reuseFailAlloc_3594_, 4, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
else
{
lean_object* v_k_3599_; lean_object* v_v_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3612_; 
v_k_3599_ = lean_ctor_get(v___x_3479_, 1);
v_v_3600_ = lean_ctor_get(v___x_3479_, 2);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; lean_object* v_unused_3614_; lean_object* v_unused_3615_; 
v_unused_3613_ = lean_ctor_get(v___x_3479_, 4);
lean_dec(v_unused_3613_);
v_unused_3614_ = lean_ctor_get(v___x_3479_, 3);
lean_dec(v_unused_3614_);
v_unused_3615_ = lean_ctor_get(v___x_3479_, 0);
lean_dec(v_unused_3615_);
v___x_3602_ = v___x_3479_;
v_isShared_3603_ = v_isSharedCheck_3612_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_v_3600_);
lean_inc(v_k_3599_);
lean_dec(v___x_3479_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3612_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3604_ = lean_unsigned_to_nat(3u);
v___x_3605_ = lean_unsigned_to_nat(1u);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 3, v_r_3579_);
lean_ctor_set(v___x_3602_, 2, v_v_3472_);
lean_ctor_set(v___x_3602_, 1, v_k_3471_);
lean_ctor_set(v___x_3602_, 0, v___x_3605_);
v___x_3607_ = v___x_3602_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3611_, 3, v_r_3579_);
lean_ctor_set(v_reuseFailAlloc_3611_, 4, v_r_3579_);
v___x_3607_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v___x_3607_);
lean_ctor_set(v___x_3476_, 3, v_l_3578_);
lean_ctor_set(v___x_3476_, 2, v_v_3600_);
lean_ctor_set(v___x_3476_, 1, v_k_3599_);
lean_ctor_set(v___x_3476_, 0, v___x_3604_);
v___x_3609_ = v___x_3476_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3604_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_k_3599_);
lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_v_3600_);
lean_ctor_set(v_reuseFailAlloc_3610_, 3, v_l_3578_);
lean_ctor_set(v_reuseFailAlloc_3610_, 4, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
else
{
lean_object* v_r_3616_; 
v_r_3616_ = lean_ctor_get(v___x_3479_, 4);
lean_inc(v_r_3616_);
if (lean_obj_tag(v_r_3616_) == 0)
{
lean_object* v_k_3617_; lean_object* v_v_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3642_; 
lean_inc(v_l_3578_);
v_k_3617_ = lean_ctor_get(v___x_3479_, 1);
v_v_3618_ = lean_ctor_get(v___x_3479_, 2);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; lean_object* v_unused_3644_; lean_object* v_unused_3645_; 
v_unused_3643_ = lean_ctor_get(v___x_3479_, 4);
lean_dec(v_unused_3643_);
v_unused_3644_ = lean_ctor_get(v___x_3479_, 3);
lean_dec(v_unused_3644_);
v_unused_3645_ = lean_ctor_get(v___x_3479_, 0);
lean_dec(v_unused_3645_);
v___x_3620_ = v___x_3479_;
v_isShared_3621_ = v_isSharedCheck_3642_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_v_3618_);
lean_inc(v_k_3617_);
lean_dec(v___x_3479_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3642_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v_k_3622_; lean_object* v_v_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3638_; 
v_k_3622_ = lean_ctor_get(v_r_3616_, 1);
v_v_3623_ = lean_ctor_get(v_r_3616_, 2);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_r_3616_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; lean_object* v_unused_3640_; lean_object* v_unused_3641_; 
v_unused_3639_ = lean_ctor_get(v_r_3616_, 4);
lean_dec(v_unused_3639_);
v_unused_3640_ = lean_ctor_get(v_r_3616_, 3);
lean_dec(v_unused_3640_);
v_unused_3641_ = lean_ctor_get(v_r_3616_, 0);
lean_dec(v_unused_3641_);
v___x_3625_ = v_r_3616_;
v_isShared_3626_ = v_isSharedCheck_3638_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_v_3623_);
lean_inc(v_k_3622_);
lean_dec(v_r_3616_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3638_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3627_ = lean_unsigned_to_nat(3u);
v___x_3628_ = lean_unsigned_to_nat(1u);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 4, v_l_3578_);
lean_ctor_set(v___x_3625_, 3, v_l_3578_);
lean_ctor_set(v___x_3625_, 2, v_v_3618_);
lean_ctor_set(v___x_3625_, 1, v_k_3617_);
lean_ctor_set(v___x_3625_, 0, v___x_3628_);
v___x_3630_ = v___x_3625_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_k_3617_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_v_3618_);
lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_l_3578_);
lean_ctor_set(v_reuseFailAlloc_3637_, 4, v_l_3578_);
v___x_3630_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v___x_3632_; 
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 4, v_l_3578_);
lean_ctor_set(v___x_3620_, 2, v_v_3472_);
lean_ctor_set(v___x_3620_, 1, v_k_3471_);
lean_ctor_set(v___x_3620_, 0, v___x_3628_);
v___x_3632_ = v___x_3620_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3636_, 3, v_l_3578_);
lean_ctor_set(v_reuseFailAlloc_3636_, 4, v_l_3578_);
v___x_3632_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3634_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v___x_3632_);
lean_ctor_set(v___x_3476_, 3, v___x_3630_);
lean_ctor_set(v___x_3476_, 2, v_v_3623_);
lean_ctor_set(v___x_3476_, 1, v_k_3622_);
lean_ctor_set(v___x_3476_, 0, v___x_3627_);
v___x_3634_ = v___x_3476_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3627_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_k_3622_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_v_3623_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
}
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3646_ = lean_unsigned_to_nat(2u);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v_r_3616_);
lean_ctor_set(v___x_3476_, 3, v___x_3479_);
lean_ctor_set(v___x_3476_, 0, v___x_3646_);
v___x_3648_ = v___x_3476_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3649_, 3, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3649_, 4, v_r_3616_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
else
{
lean_object* v___x_3650_; lean_object* v___x_3652_; 
v___x_3650_ = lean_unsigned_to_nat(1u);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v___x_3479_);
lean_ctor_set(v___x_3476_, 3, v___x_3479_);
lean_ctor_set(v___x_3476_, 0, v___x_3650_);
v___x_3652_ = v___x_3476_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3653_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3653_, 3, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3653_, 4, v___x_3479_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
case 1:
{
lean_object* v___x_3655_; 
lean_dec(v_v_3472_);
lean_dec(v_k_3471_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 2, v_v_3468_);
lean_ctor_set(v___x_3476_, 1, v_k_3467_);
v___x_3655_ = v___x_3476_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_size_3470_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_k_3467_);
lean_ctor_set(v_reuseFailAlloc_3656_, 2, v_v_3468_);
lean_ctor_set(v_reuseFailAlloc_3656_, 3, v_l_3473_);
lean_ctor_set(v_reuseFailAlloc_3656_, 4, v_r_3474_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
default: 
{
lean_object* v___x_3657_; 
lean_dec(v_size_3470_);
v___x_3657_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3467_, v_v_3468_, v_r_3474_);
if (lean_obj_tag(v_l_3473_) == 0)
{
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_size_3658_; lean_object* v_size_3659_; lean_object* v_k_3660_; lean_object* v_v_3661_; lean_object* v_l_3662_; lean_object* v_r_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; uint8_t v___x_3666_; 
v_size_3658_ = lean_ctor_get(v_l_3473_, 0);
v_size_3659_ = lean_ctor_get(v___x_3657_, 0);
v_k_3660_ = lean_ctor_get(v___x_3657_, 1);
v_v_3661_ = lean_ctor_get(v___x_3657_, 2);
v_l_3662_ = lean_ctor_get(v___x_3657_, 3);
lean_inc(v_l_3662_);
v_r_3663_ = lean_ctor_get(v___x_3657_, 4);
v___x_3664_ = lean_unsigned_to_nat(3u);
v___x_3665_ = lean_nat_mul(v___x_3664_, v_size_3658_);
v___x_3666_ = lean_nat_dec_lt(v___x_3665_, v_size_3659_);
lean_dec(v___x_3665_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
lean_dec(v_l_3662_);
v___x_3667_ = lean_unsigned_to_nat(1u);
v___x_3668_ = lean_nat_add(v___x_3667_, v_size_3658_);
v___x_3669_ = lean_nat_add(v___x_3668_, v_size_3659_);
lean_dec(v___x_3668_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v___x_3657_);
lean_ctor_set(v___x_3476_, 0, v___x_3669_);
v___x_3671_ = v___x_3476_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3672_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3672_, 3, v_l_3473_);
lean_ctor_set(v_reuseFailAlloc_3672_, 4, v___x_3657_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
else
{
lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3742_; 
lean_inc(v_r_3663_);
lean_inc(v_v_3661_);
lean_inc(v_k_3660_);
lean_inc(v_size_3659_);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; lean_object* v_unused_3746_; lean_object* v_unused_3747_; 
v_unused_3743_ = lean_ctor_get(v___x_3657_, 4);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v___x_3657_, 3);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v___x_3657_, 2);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v___x_3657_, 1);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v___x_3657_, 0);
lean_dec(v_unused_3747_);
v___x_3674_ = v___x_3657_;
v_isShared_3675_ = v_isSharedCheck_3742_;
goto v_resetjp_3673_;
}
else
{
lean_dec(v___x_3657_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3742_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
if (lean_obj_tag(v_l_3662_) == 0)
{
if (lean_obj_tag(v_r_3663_) == 0)
{
lean_object* v_size_3676_; lean_object* v_k_3677_; lean_object* v_v_3678_; lean_object* v_l_3679_; lean_object* v_r_3680_; lean_object* v_size_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v_size_3676_ = lean_ctor_get(v_l_3662_, 0);
v_k_3677_ = lean_ctor_get(v_l_3662_, 1);
v_v_3678_ = lean_ctor_get(v_l_3662_, 2);
v_l_3679_ = lean_ctor_get(v_l_3662_, 3);
v_r_3680_ = lean_ctor_get(v_l_3662_, 4);
v_size_3681_ = lean_ctor_get(v_r_3663_, 0);
v___x_3682_ = lean_unsigned_to_nat(2u);
v___x_3683_ = lean_nat_mul(v___x_3682_, v_size_3681_);
v___x_3684_ = lean_nat_dec_lt(v_size_3676_, v___x_3683_);
lean_dec(v___x_3683_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3713_; 
lean_inc(v_r_3680_);
lean_inc(v_l_3679_);
lean_inc(v_v_3678_);
lean_inc(v_k_3677_);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_l_3662_);
if (v_isSharedCheck_3713_ == 0)
{
lean_object* v_unused_3714_; lean_object* v_unused_3715_; lean_object* v_unused_3716_; lean_object* v_unused_3717_; lean_object* v_unused_3718_; 
v_unused_3714_ = lean_ctor_get(v_l_3662_, 4);
lean_dec(v_unused_3714_);
v_unused_3715_ = lean_ctor_get(v_l_3662_, 3);
lean_dec(v_unused_3715_);
v_unused_3716_ = lean_ctor_get(v_l_3662_, 2);
lean_dec(v_unused_3716_);
v_unused_3717_ = lean_ctor_get(v_l_3662_, 1);
lean_dec(v_unused_3717_);
v_unused_3718_ = lean_ctor_get(v_l_3662_, 0);
lean_dec(v_unused_3718_);
v___x_3686_ = v_l_3662_;
v_isShared_3687_ = v_isSharedCheck_3713_;
goto v_resetjp_3685_;
}
else
{
lean_dec(v_l_3662_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3713_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3703_; 
v___x_3688_ = lean_unsigned_to_nat(1u);
v___x_3689_ = lean_nat_add(v___x_3688_, v_size_3658_);
v___x_3690_ = lean_nat_add(v___x_3689_, v_size_3659_);
lean_dec(v_size_3659_);
if (lean_obj_tag(v_l_3679_) == 0)
{
lean_object* v_size_3711_; 
v_size_3711_ = lean_ctor_get(v_l_3679_, 0);
lean_inc(v_size_3711_);
v___y_3703_ = v_size_3711_;
goto v___jp_3702_;
}
else
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_unsigned_to_nat(0u);
v___y_3703_ = v___x_3712_;
goto v___jp_3702_;
}
v___jp_3691_:
{
lean_object* v___x_3695_; lean_object* v___x_3697_; 
v___x_3695_ = lean_nat_add(v___y_3692_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec(v___y_3692_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v_r_3663_);
lean_ctor_set(v___x_3686_, 3, v_r_3680_);
lean_ctor_set(v___x_3686_, 2, v_v_3661_);
lean_ctor_set(v___x_3686_, 1, v_k_3660_);
lean_ctor_set(v___x_3686_, 0, v___x_3695_);
v___x_3697_ = v___x_3686_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_k_3660_);
lean_ctor_set(v_reuseFailAlloc_3701_, 2, v_v_3661_);
lean_ctor_set(v_reuseFailAlloc_3701_, 3, v_r_3680_);
lean_ctor_set(v_reuseFailAlloc_3701_, 4, v_r_3663_);
v___x_3697_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3699_; 
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v___x_3697_);
lean_ctor_set(v___x_3674_, 3, v___y_3693_);
lean_ctor_set(v___x_3674_, 2, v_v_3678_);
lean_ctor_set(v___x_3674_, 1, v_k_3677_);
lean_ctor_set(v___x_3674_, 0, v___x_3690_);
v___x_3699_ = v___x_3674_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_k_3677_);
lean_ctor_set(v_reuseFailAlloc_3700_, 2, v_v_3678_);
lean_ctor_set(v_reuseFailAlloc_3700_, 3, v___y_3693_);
lean_ctor_set(v_reuseFailAlloc_3700_, 4, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
v___jp_3702_:
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = lean_nat_add(v___x_3689_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec(v___x_3689_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v_l_3679_);
lean_ctor_set(v___x_3476_, 0, v___x_3704_);
v___x_3706_ = v___x_3476_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_l_3473_);
lean_ctor_set(v_reuseFailAlloc_3710_, 4, v_l_3679_);
v___x_3706_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; 
v___x_3707_ = lean_nat_add(v___x_3688_, v_size_3681_);
if (lean_obj_tag(v_r_3680_) == 0)
{
lean_object* v_size_3708_; 
v_size_3708_ = lean_ctor_get(v_r_3680_, 0);
lean_inc(v_size_3708_);
v___y_3692_ = v___x_3707_;
v___y_3693_ = v___x_3706_;
v___y_3694_ = v_size_3708_;
goto v___jp_3691_;
}
else
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_unsigned_to_nat(0u);
v___y_3692_ = v___x_3707_;
v___y_3693_ = v___x_3706_;
v___y_3694_ = v___x_3709_;
goto v___jp_3691_;
}
}
}
}
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
lean_del_object(v___x_3476_);
v___x_3719_ = lean_unsigned_to_nat(1u);
v___x_3720_ = lean_nat_add(v___x_3719_, v_size_3658_);
v___x_3721_ = lean_nat_add(v___x_3720_, v_size_3659_);
lean_dec(v_size_3659_);
v___x_3722_ = lean_nat_add(v___x_3720_, v_size_3676_);
lean_dec(v___x_3720_);
lean_inc_ref(v_l_3473_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v_l_3662_);
lean_ctor_set(v___x_3674_, 3, v_l_3473_);
lean_ctor_set(v___x_3674_, 2, v_v_3472_);
lean_ctor_set(v___x_3674_, 1, v_k_3471_);
lean_ctor_set(v___x_3674_, 0, v___x_3722_);
v___x_3724_ = v___x_3674_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3737_, 3, v_l_3473_);
lean_ctor_set(v_reuseFailAlloc_3737_, 4, v_l_3662_);
v___x_3724_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
v_isSharedCheck_3731_ = !lean_is_exclusive(v_l_3473_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; lean_object* v_unused_3736_; 
v_unused_3732_ = lean_ctor_get(v_l_3473_, 4);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_l_3473_, 3);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_l_3473_, 2);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_l_3473_, 1);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_l_3473_, 0);
lean_dec(v_unused_3736_);
v___x_3726_ = v_l_3473_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_dec(v_l_3473_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 4, v_r_3663_);
lean_ctor_set(v___x_3726_, 3, v___x_3724_);
lean_ctor_set(v___x_3726_, 2, v_v_3661_);
lean_ctor_set(v___x_3726_, 1, v_k_3660_);
lean_ctor_set(v___x_3726_, 0, v___x_3721_);
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_k_3660_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_v_3661_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v_r_3663_);
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
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_dec_ref_known(v_l_3662_, 5);
lean_del_object(v___x_3674_);
lean_dec(v_v_3661_);
lean_dec(v_k_3660_);
lean_dec(v_size_3659_);
lean_dec_ref_known(v_l_3473_, 5);
lean_del_object(v___x_3476_);
lean_dec(v_v_3472_);
lean_dec(v_k_3471_);
v___x_3738_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7);
v___x_3739_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3738_);
return v___x_3739_;
}
}
else
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_del_object(v___x_3674_);
lean_dec(v_r_3663_);
lean_dec(v_v_3661_);
lean_dec(v_k_3660_);
lean_dec(v_size_3659_);
lean_dec_ref_known(v_l_3473_, 5);
lean_del_object(v___x_3476_);
lean_dec(v_v_3472_);
lean_dec(v_k_3471_);
v___x_3740_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8);
v___x_3741_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3740_);
return v___x_3741_;
}
}
}
}
else
{
lean_object* v_size_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
v_size_3748_ = lean_ctor_get(v_l_3473_, 0);
v___x_3749_ = lean_unsigned_to_nat(1u);
v___x_3750_ = lean_nat_add(v___x_3749_, v_size_3748_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v___x_3657_);
lean_ctor_set(v___x_3476_, 0, v___x_3750_);
v___x_3752_ = v___x_3476_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3753_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3753_, 3, v_l_3473_);
lean_ctor_set(v_reuseFailAlloc_3753_, 4, v___x_3657_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
else
{
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_l_3754_; 
v_l_3754_ = lean_ctor_get(v___x_3657_, 3);
lean_inc(v_l_3754_);
if (lean_obj_tag(v_l_3754_) == 0)
{
lean_object* v_r_3755_; 
v_r_3755_ = lean_ctor_get(v___x_3657_, 4);
lean_inc(v_r_3755_);
if (lean_obj_tag(v_r_3755_) == 0)
{
lean_object* v_size_3756_; lean_object* v_k_3757_; lean_object* v_v_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3772_; 
v_size_3756_ = lean_ctor_get(v___x_3657_, 0);
v_k_3757_ = lean_ctor_get(v___x_3657_, 1);
v_v_3758_ = lean_ctor_get(v___x_3657_, 2);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3772_ == 0)
{
lean_object* v_unused_3773_; lean_object* v_unused_3774_; 
v_unused_3773_ = lean_ctor_get(v___x_3657_, 4);
lean_dec(v_unused_3773_);
v_unused_3774_ = lean_ctor_get(v___x_3657_, 3);
lean_dec(v_unused_3774_);
v___x_3760_ = v___x_3657_;
v_isShared_3761_ = v_isSharedCheck_3772_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_v_3758_);
lean_inc(v_k_3757_);
lean_inc(v_size_3756_);
lean_dec(v___x_3657_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3772_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v_size_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3767_; 
v_size_3762_ = lean_ctor_get(v_l_3754_, 0);
v___x_3763_ = lean_unsigned_to_nat(1u);
v___x_3764_ = lean_nat_add(v___x_3763_, v_size_3756_);
lean_dec(v_size_3756_);
v___x_3765_ = lean_nat_add(v___x_3763_, v_size_3762_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 4, v_l_3754_);
lean_ctor_set(v___x_3760_, 3, v_l_3473_);
lean_ctor_set(v___x_3760_, 2, v_v_3472_);
lean_ctor_set(v___x_3760_, 1, v_k_3471_);
lean_ctor_set(v___x_3760_, 0, v___x_3765_);
v___x_3767_ = v___x_3760_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3771_, 3, v_l_3473_);
lean_ctor_set(v_reuseFailAlloc_3771_, 4, v_l_3754_);
v___x_3767_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3769_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v_r_3755_);
lean_ctor_set(v___x_3476_, 3, v___x_3767_);
lean_ctor_set(v___x_3476_, 2, v_v_3758_);
lean_ctor_set(v___x_3476_, 1, v_k_3757_);
lean_ctor_set(v___x_3476_, 0, v___x_3764_);
v___x_3769_ = v___x_3476_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3764_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v_k_3757_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v_v_3758_);
lean_ctor_set(v_reuseFailAlloc_3770_, 3, v___x_3767_);
lean_ctor_set(v_reuseFailAlloc_3770_, 4, v_r_3755_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
else
{
lean_object* v_k_3775_; lean_object* v_v_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3800_; 
v_k_3775_ = lean_ctor_get(v___x_3657_, 1);
v_v_3776_ = lean_ctor_get(v___x_3657_, 2);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; lean_object* v_unused_3802_; lean_object* v_unused_3803_; 
v_unused_3801_ = lean_ctor_get(v___x_3657_, 4);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v___x_3657_, 3);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v___x_3657_, 0);
lean_dec(v_unused_3803_);
v___x_3778_ = v___x_3657_;
v_isShared_3779_ = v_isSharedCheck_3800_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_v_3776_);
lean_inc(v_k_3775_);
lean_dec(v___x_3657_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3800_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v_k_3780_; lean_object* v_v_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3796_; 
v_k_3780_ = lean_ctor_get(v_l_3754_, 1);
v_v_3781_ = lean_ctor_get(v_l_3754_, 2);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_l_3754_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; lean_object* v_unused_3798_; lean_object* v_unused_3799_; 
v_unused_3797_ = lean_ctor_get(v_l_3754_, 4);
lean_dec(v_unused_3797_);
v_unused_3798_ = lean_ctor_get(v_l_3754_, 3);
lean_dec(v_unused_3798_);
v_unused_3799_ = lean_ctor_get(v_l_3754_, 0);
lean_dec(v_unused_3799_);
v___x_3783_ = v_l_3754_;
v_isShared_3784_ = v_isSharedCheck_3796_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_v_3781_);
lean_inc(v_k_3780_);
lean_dec(v_l_3754_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3796_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3788_; 
v___x_3785_ = lean_unsigned_to_nat(3u);
v___x_3786_ = lean_unsigned_to_nat(1u);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 4, v_r_3755_);
lean_ctor_set(v___x_3783_, 3, v_r_3755_);
lean_ctor_set(v___x_3783_, 2, v_v_3472_);
lean_ctor_set(v___x_3783_, 1, v_k_3471_);
lean_ctor_set(v___x_3783_, 0, v___x_3786_);
v___x_3788_ = v___x_3783_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3795_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3795_, 3, v_r_3755_);
lean_ctor_set(v_reuseFailAlloc_3795_, 4, v_r_3755_);
v___x_3788_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3790_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 3, v_r_3755_);
lean_ctor_set(v___x_3778_, 0, v___x_3786_);
v___x_3790_ = v___x_3778_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_k_3775_);
lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_v_3776_);
lean_ctor_set(v_reuseFailAlloc_3794_, 3, v_r_3755_);
lean_ctor_set(v_reuseFailAlloc_3794_, 4, v_r_3755_);
v___x_3790_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3792_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v___x_3790_);
lean_ctor_set(v___x_3476_, 3, v___x_3788_);
lean_ctor_set(v___x_3476_, 2, v_v_3781_);
lean_ctor_set(v___x_3476_, 1, v_k_3780_);
lean_ctor_set(v___x_3476_, 0, v___x_3785_);
v___x_3792_ = v___x_3476_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3785_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_k_3780_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_v_3781_);
lean_ctor_set(v_reuseFailAlloc_3793_, 3, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3793_, 4, v___x_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3804_; 
v_r_3804_ = lean_ctor_get(v___x_3657_, 4);
lean_inc(v_r_3804_);
if (lean_obj_tag(v_r_3804_) == 0)
{
lean_object* v_k_3805_; lean_object* v_v_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3818_; 
v_k_3805_ = lean_ctor_get(v___x_3657_, 1);
v_v_3806_ = lean_ctor_get(v___x_3657_, 2);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; lean_object* v_unused_3820_; lean_object* v_unused_3821_; 
v_unused_3819_ = lean_ctor_get(v___x_3657_, 4);
lean_dec(v_unused_3819_);
v_unused_3820_ = lean_ctor_get(v___x_3657_, 3);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v___x_3657_, 0);
lean_dec(v_unused_3821_);
v___x_3808_ = v___x_3657_;
v_isShared_3809_ = v_isSharedCheck_3818_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_v_3806_);
lean_inc(v_k_3805_);
lean_dec(v___x_3657_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3818_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3810_ = lean_unsigned_to_nat(3u);
v___x_3811_ = lean_unsigned_to_nat(1u);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 4, v_l_3754_);
lean_ctor_set(v___x_3808_, 2, v_v_3472_);
lean_ctor_set(v___x_3808_, 1, v_k_3471_);
lean_ctor_set(v___x_3808_, 0, v___x_3811_);
v___x_3813_ = v___x_3808_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3817_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3817_, 3, v_l_3754_);
lean_ctor_set(v_reuseFailAlloc_3817_, 4, v_l_3754_);
v___x_3813_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3815_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v_r_3804_);
lean_ctor_set(v___x_3476_, 3, v___x_3813_);
lean_ctor_set(v___x_3476_, 2, v_v_3806_);
lean_ctor_set(v___x_3476_, 1, v_k_3805_);
lean_ctor_set(v___x_3476_, 0, v___x_3810_);
v___x_3815_ = v___x_3476_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3810_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_3816_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_3816_, 3, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3816_, 4, v_r_3804_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3824_; 
v___x_3822_ = lean_unsigned_to_nat(2u);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v___x_3657_);
lean_ctor_set(v___x_3476_, 3, v_r_3804_);
lean_ctor_set(v___x_3476_, 0, v___x_3822_);
v___x_3824_ = v___x_3476_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3825_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3825_, 3, v_r_3804_);
lean_ctor_set(v_reuseFailAlloc_3825_, 4, v___x_3657_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
else
{
lean_object* v___x_3826_; lean_object* v___x_3828_; 
v___x_3826_ = lean_unsigned_to_nat(1u);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v___x_3657_);
lean_ctor_set(v___x_3476_, 3, v___x_3657_);
lean_ctor_set(v___x_3476_, 0, v___x_3826_);
v___x_3828_ = v___x_3476_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_k_3471_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v_v_3472_);
lean_ctor_set(v_reuseFailAlloc_3829_, 3, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3829_, 4, v___x_3657_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_unsigned_to_nat(1u);
v___x_3832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
lean_ctor_set(v___x_3832_, 1, v_k_3467_);
lean_ctor_set(v___x_3832_, 2, v_v_3468_);
lean_ctor_set(v___x_3832_, 3, v_t_3469_);
lean_ctor_set(v___x_3832_, 4, v_t_3469_);
return v___x_3832_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(lean_object* v_init_3833_, lean_object* v_x_3834_){
_start:
{
if (lean_obj_tag(v_x_3834_) == 0)
{
lean_object* v_k_3835_; lean_object* v_v_3836_; lean_object* v_l_3837_; lean_object* v_r_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v_k_3835_ = lean_ctor_get(v_x_3834_, 1);
lean_inc(v_k_3835_);
v_v_3836_ = lean_ctor_get(v_x_3834_, 2);
lean_inc(v_v_3836_);
v_l_3837_ = lean_ctor_get(v_x_3834_, 3);
lean_inc(v_l_3837_);
v_r_3838_ = lean_ctor_get(v_x_3834_, 4);
lean_inc(v_r_3838_);
lean_dec_ref_known(v_x_3834_, 5);
v___x_3839_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_3833_, v_l_3837_);
v___x_3840_ = 1;
v___x_3841_ = l_Lean_Name_toString(v_k_3835_, v___x_3840_);
v___x_3842_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3842_, 0, v_v_3836_);
v___x_3843_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v___x_3841_, v___x_3842_, v___x_3839_);
v_init_3833_ = v___x_3843_;
v_x_3834_ = v_r_3838_;
goto _start;
}
else
{
return v_init_3833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_m_3845_){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = lean_box(1);
v___x_3847_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v___x_3846_, v_m_3845_);
v___x_3848_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
return v___x_3848_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v___x_3851_, uint8_t v_updateToolchain_3852_, lean_object* v_ws_3853_, lean_object* v_dep_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v_baseName_3858_; lean_object* v_name_3859_; lean_object* v_opts_3860_; uint8_t v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_baseName_3858_ = lean_ctor_get(v___x_3851_, 1);
v_name_3859_ = lean_ctor_get(v_dep_3854_, 0);
v_opts_3860_ = lean_ctor_get(v_dep_3854_, 4);
v___x_3861_ = 0;
lean_inc(v_baseName_3858_);
v___x_3862_ = l_Lean_Name_toString(v_baseName_3858_, v___x_3861_);
v___x_3863_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3864_ = lean_string_append(v___x_3862_, v___x_3863_);
lean_inc(v_name_3859_);
v___x_3865_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3859_, v_updateToolchain_3852_);
v___x_3866_ = lean_string_append(v___x_3864_, v___x_3865_);
lean_dec_ref(v___x_3865_);
v___x_3867_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3868_ = lean_string_append(v___x_3866_, v___x_3867_);
lean_inc(v_opts_3860_);
v___x_3869_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_opts_3860_);
v___x_3870_ = lean_unsigned_to_nat(80u);
v___x_3871_ = l_Lean_Json_pretty(v___x_3869_, v___x_3870_);
v___x_3872_ = lean_string_append(v___x_3868_, v___x_3871_);
lean_dec_ref(v___x_3871_);
v___x_3873_ = 0;
v___x_3874_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3874_, 0, v___x_3872_);
lean_ctor_set_uint8(v___x_3874_, sizeof(void*)*1, v___x_3873_);
lean_inc_ref(v___y_3856_);
v___x_3875_ = lean_apply_2(v___y_3856_, v___x_3874_, lean_box(0));
v___x_3876_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3853_, v___x_3851_, v_dep_3854_, v___y_3855_, v___y_3856_);
return v___x_3876_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3851_ = stack[0].m_obj;
uint8_t v_updateToolchain_3852_ = stack[1].m_num;
lean_object* v_ws_3853_ = stack[2].m_obj;
lean_object* v_dep_3854_ = stack[3].m_obj;
lean_object* v___y_3855_ = stack[4].m_obj;
lean_object* v___y_3856_ = stack[5].m_obj;
lean_object* v_res_3877_;
v_res_3877_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v___x_3851_, v_updateToolchain_3852_, v_ws_3853_, v_dep_3854_, v___y_3855_, v___y_3856_);
stack->m_obj
 = v_res_3877_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v___x_3878_, lean_object* v_updateToolchain_3879_, lean_object* v_ws_3880_, lean_object* v_dep_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
uint8_t v_updateToolchain_boxed_3885_; lean_object* v_res_3886_; 
v_updateToolchain_boxed_3885_ = lean_unbox(v_updateToolchain_3879_);
v_res_3886_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v___x_3878_, v_updateToolchain_boxed_3885_, v_ws_3880_, v_dep_3881_, v___y_3882_, v___y_3883_);
lean_dec_ref(v___y_3883_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_a_3887_, lean_object* v_b_3888_){
_start:
{
lean_object* v_next_3889_; 
v_next_3889_ = lean_ctor_get(v_a_3887_, 0);
lean_inc(v_next_3889_);
if (lean_obj_tag(v_next_3889_) == 0)
{
lean_dec_ref(v_a_3887_);
return v_b_3888_;
}
else
{
lean_object* v_upperBound_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3910_; 
v_upperBound_3890_ = lean_ctor_get(v_a_3887_, 1);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_a_3887_);
if (v_isSharedCheck_3910_ == 0)
{
lean_object* v_unused_3911_; 
v_unused_3911_ = lean_ctor_get(v_a_3887_, 0);
lean_dec(v_unused_3911_);
v___x_3892_ = v_a_3887_;
v_isShared_3893_ = v_isSharedCheck_3910_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_upperBound_3890_);
lean_dec(v_a_3887_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3910_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v_val_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3909_; 
v_val_3894_ = lean_ctor_get(v_next_3889_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_next_3889_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3896_ = v_next_3889_;
v_isShared_3897_ = v_isSharedCheck_3909_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_val_3894_);
lean_dec(v_next_3889_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3909_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
uint8_t v___x_3898_; 
v___x_3898_ = lean_nat_dec_lt(v_val_3894_, v_upperBound_3890_);
if (v___x_3898_ == 0)
{
lean_del_object(v___x_3896_);
lean_dec(v_val_3894_);
lean_del_object(v___x_3892_);
lean_dec(v_upperBound_3890_);
return v_b_3888_;
}
else
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3902_; 
v___x_3899_ = lean_unsigned_to_nat(1u);
v___x_3900_ = lean_nat_add(v_val_3894_, v___x_3899_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v___x_3900_);
v___x_3902_ = v___x_3896_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3904_; 
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 0, v___x_3902_);
v___x_3904_ = v___x_3892_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_upperBound_3890_);
v___x_3904_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3905_; 
v___x_3905_ = lean_array_push(v_b_3888_, v_val_3894_);
v_a_3887_ = v___x_3904_;
v_b_3888_ = v___x_3905_;
goto _start;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_n_3912_, lean_object* v_f_3913_, lean_object* v_xs_3914_, lean_object* v_k_3915_, lean_object* v_acc_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
uint8_t v___x_3920_; 
v___x_3920_ = lean_nat_dec_lt(v_k_3915_, v_n_3912_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_dec(v_k_3915_);
lean_dec_ref(v_f_3913_);
v___x_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3921_, 0, v_acc_3916_);
lean_ctor_set(v___x_3921_, 1, v___y_3917_);
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
return v___x_3922_;
}
else
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_array_fget_borrowed(v_xs_3914_, v_k_3915_);
lean_inc_ref(v_f_3913_);
lean_inc_ref(v___y_3918_);
lean_inc(v___x_3923_);
v___x_3924_ = lean_apply_4(v_f_3913_, v___x_3923_, v___y_3917_, v___y_3918_, lean_box(0));
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v_fst_3926_; lean_object* v_snd_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v_fst_3926_ = lean_ctor_get(v_a_3925_, 0);
lean_inc(v_fst_3926_);
v_snd_3927_ = lean_ctor_get(v_a_3925_, 1);
lean_inc(v_snd_3927_);
lean_dec(v_a_3925_);
v___x_3928_ = lean_unsigned_to_nat(1u);
v___x_3929_ = lean_nat_add(v_k_3915_, v___x_3928_);
lean_dec(v_k_3915_);
v___x_3930_ = lean_array_push(v_acc_3916_, v_fst_3926_);
v_k_3915_ = v___x_3929_;
v_acc_3916_ = v___x_3930_;
v___y_3917_ = v_snd_3927_;
goto _start;
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v_acc_3916_);
lean_dec(v_k_3915_);
lean_dec_ref(v_f_3913_);
v_a_3932_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3924_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3924_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3912_ = stack[0].m_obj;
lean_object* v_f_3913_ = stack[1].m_obj;
lean_object* v_xs_3914_ = stack[2].m_obj;
lean_object* v_k_3915_ = stack[3].m_obj;
lean_object* v_acc_3916_ = stack[4].m_obj;
lean_object* v___y_3917_ = stack[5].m_obj;
lean_object* v___y_3918_ = stack[6].m_obj;
lean_object* v_res_3940_;
v_res_3940_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_3912_, v_f_3913_, v_xs_3914_, v_k_3915_, v_acc_3916_, v___y_3917_, v___y_3918_);
stack->m_obj
 = v_res_3940_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object* v_n_3941_, lean_object* v_f_3942_, lean_object* v_xs_3943_, lean_object* v_k_3944_, lean_object* v_acc_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_3941_, v_f_3942_, v_xs_3943_, v_k_3944_, v_acc_3945_, v___y_3946_, v___y_3947_);
lean_dec_ref(v___y_3947_);
lean_dec_ref(v_xs_3943_);
lean_dec(v_n_3941_);
return v_res_3949_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object* v_upperBound_3950_, lean_object* v_fst_3951_, lean_object* v___x_3952_, lean_object* v_leanOpts_3953_, lean_object* v_a_3954_, lean_object* v_b_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_fst_3960_; lean_object* v_snd_3961_; uint8_t v___x_3965_; 
v___x_3965_ = lean_nat_dec_lt(v_a_3954_, v_upperBound_3950_);
if (v___x_3965_ == 0)
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
lean_dec(v_a_3954_);
lean_dec_ref(v_leanOpts_3953_);
v___x_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3966_, 0, v_b_3955_);
lean_ctor_set(v___x_3966_, 1, v___y_3956_);
v___x_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
return v___x_3967_;
}
else
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3968_ = lean_array_fget_borrowed(v_fst_3951_, v_a_3954_);
lean_inc(v___x_3968_);
v___x_3969_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_3968_, v___y_3956_, v___y_3957_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_4023_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_3972_ = v___x_3969_;
v_isShared_3973_ = v_isSharedCheck_4023_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_4023_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v_snd_3974_; lean_object* v___x_3975_; lean_object* v_opts_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_snd_3974_ = lean_ctor_get(v_a_3970_, 1);
lean_inc(v_snd_3974_);
lean_dec(v_a_3970_);
v___x_3975_ = lean_array_fget_borrowed(v___x_3952_, v_a_3954_);
v_opts_3976_ = lean_ctor_get(v___x_3975_, 4);
v___x_3977_ = lean_unsigned_to_nat(0u);
v___x_3978_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3953_);
lean_inc(v_opts_3976_);
lean_inc(v___x_3968_);
v___x_3979_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_3955_, v___x_3968_, v_opts_3976_, v_leanOpts_3953_, v___x_3965_, v___x_3978_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v_a_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
lean_del_object(v___x_3972_);
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
v_a_3981_ = lean_ctor_get(v___x_3979_, 1);
lean_inc(v_a_3981_);
lean_dec_ref_known(v___x_3979_, 2);
v___x_3982_ = lean_array_get_size(v_a_3981_);
v___x_3983_ = lean_nat_dec_lt(v___x_3977_, v___x_3982_);
if (v___x_3983_ == 0)
{
lean_dec(v_a_3981_);
v_fst_3960_ = v_a_3980_;
v_snd_3961_ = v_snd_3974_;
goto v___jp_3959_;
}
else
{
lean_object* v___x_3984_; size_t v___x_3985_; size_t v___x_3986_; lean_object* v___x_3987_; 
v___x_3984_ = lean_box(0);
v___x_3985_ = ((size_t)0ULL);
v___x_3986_ = lean_usize_of_nat(v___x_3982_);
v___x_3987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3981_, v___x_3985_, v___x_3986_, v___x_3984_, v___y_3957_);
lean_dec(v_a_3981_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_dec_ref_known(v___x_3987_, 1);
v_fst_3960_ = v_a_3980_;
v_snd_3961_ = v_snd_3974_;
goto v___jp_3959_;
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec(v_a_3980_);
lean_dec(v_snd_3974_);
lean_dec(v_a_3954_);
lean_dec_ref(v_leanOpts_3953_);
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3987_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3987_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; 
lean_dec(v_snd_3974_);
lean_dec(v_a_3954_);
lean_dec_ref(v_leanOpts_3953_);
v_a_3996_ = lean_ctor_get(v___x_3979_, 1);
lean_inc(v_a_3996_);
lean_dec_ref_known(v___x_3979_, 2);
v___x_3997_ = lean_array_get_size(v_a_3996_);
v___x_3998_ = lean_nat_dec_lt(v___x_3977_, v___x_3997_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; lean_object* v___x_4001_; 
lean_dec(v_a_3996_);
v___x_3999_ = lean_box(0);
if (v_isShared_3973_ == 0)
{
lean_ctor_set_tag(v___x_3972_, 1);
lean_ctor_set(v___x_3972_, 0, v___x_3999_);
v___x_4001_ = v___x_3972_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
else
{
lean_object* v___x_4003_; size_t v___x_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
lean_del_object(v___x_3972_);
v___x_4003_ = lean_box(0);
v___x_4004_ = ((size_t)0ULL);
v___x_4005_ = lean_usize_of_nat(v___x_3997_);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3996_, v___x_4004_, v___x_4005_, v___x_4003_, v___y_3957_);
lean_dec(v_a_3996_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; 
v_unused_4014_ = lean_ctor_get(v___x_4006_, 0);
lean_dec(v_unused_4014_);
v___x_4008_ = v___x_4006_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_dec(v___x_4006_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
lean_ctor_set_tag(v___x_4008_, 1);
lean_ctor_set(v___x_4008_, 0, v___x_4003_);
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4003_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
v_a_4015_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_4006_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4006_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
lean_dec_ref(v_b_3955_);
lean_dec(v_a_3954_);
lean_dec_ref(v_leanOpts_3953_);
v_a_4024_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_3969_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_3969_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
v___jp_3959_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_unsigned_to_nat(1u);
v___x_3963_ = lean_nat_add(v_a_3954_, v___x_3962_);
lean_dec(v_a_3954_);
v_a_3954_ = v___x_3963_;
v_b_3955_ = v_fst_3960_;
v___y_3956_ = v_snd_3961_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3950_ = stack[0].m_obj;
lean_object* v_fst_3951_ = stack[1].m_obj;
lean_object* v___x_3952_ = stack[2].m_obj;
lean_object* v_leanOpts_3953_ = stack[3].m_obj;
lean_object* v_a_3954_ = stack[4].m_obj;
lean_object* v_b_3955_ = stack[5].m_obj;
lean_object* v___y_3956_ = stack[6].m_obj;
lean_object* v___y_3957_ = stack[7].m_obj;
lean_object* v_res_4032_;
v_res_4032_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_3950_, v_fst_3951_, v___x_3952_, v_leanOpts_3953_, v_a_3954_, v_b_3955_, v___y_3956_, v___y_3957_);
stack->m_obj
 = v_res_4032_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object* v_upperBound_4033_, lean_object* v_fst_4034_, lean_object* v___x_4035_, lean_object* v_leanOpts_4036_, lean_object* v_a_4037_, lean_object* v_b_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4033_, v_fst_4034_, v___x_4035_, v_leanOpts_4036_, v_a_4037_, v_b_4038_, v___y_4039_, v___y_4040_);
lean_dec_ref(v___y_4040_);
lean_dec_ref(v___x_4035_);
lean_dec_ref(v_fst_4034_);
lean_dec(v_upperBound_4033_);
return v_res_4042_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(lean_object* v___x_4043_, lean_object* v_x_4044_){
_start:
{
lean_object* v_baseName_4045_; lean_object* v_name_4046_; uint8_t v___x_4047_; 
v_baseName_4045_ = lean_ctor_get(v_x_4044_, 1);
v_name_4046_ = lean_ctor_get(v___x_4043_, 0);
v___x_4047_ = lean_name_eq(v_baseName_4045_, v_name_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4043_ = stack[0].m_obj;
lean_object* v_x_4044_ = stack[1].m_obj;
uint8_t v_res_4048_;
v_res_4048_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(v___x_4043_, v_x_4044_);
stack->m_num = v_res_4048_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___x_4049_, lean_object* v_x_4050_){
_start:
{
uint8_t v_res_4051_; lean_object* v_r_4052_; 
v_res_4051_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(v___x_4049_, v_x_4050_);
lean_dec_ref(v_x_4050_);
lean_dec_ref(v___x_4049_);
v_r_4052_ = lean_box(v_res_4051_);
return v_r_4052_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object* v_pkg_4053_, lean_object* v_leanOpts_4054_, uint8_t v_reconfigure_4055_, lean_object* v_as_4056_, size_t v_i_4057_, size_t v_stop_4058_, lean_object* v_b_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
uint8_t v___x_4063_; 
v___x_4063_ = lean_usize_dec_eq(v_i_4057_, v_stop_4058_);
if (v___x_4063_ == 0)
{
lean_object* v_ws_4064_; lean_object* v_depIdxs_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4162_; 
v_ws_4064_ = lean_ctor_get(v_b_4059_, 0);
v_depIdxs_4065_ = lean_ctor_get(v_b_4059_, 1);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_b_4059_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4067_ = v_b_4059_;
v_isShared_4068_ = v_isSharedCheck_4162_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_depIdxs_4065_);
lean_inc(v_ws_4064_);
lean_dec(v_b_4059_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4162_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v_packages_4069_; size_t v___x_4070_; size_t v___x_4071_; lean_object* v___x_4072_; lean_object* v___f_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v_packages_4069_ = lean_ctor_get(v_ws_4064_, 4);
v___x_4070_ = ((size_t)1ULL);
v___x_4071_ = lean_usize_sub(v_i_4057_, v___x_4070_);
v___x_4072_ = lean_array_uget_borrowed(v_as_4056_, v___x_4071_);
lean_inc(v___x_4072_);
v___f_4073_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4073_, 0, v___x_4072_);
v___x_4074_ = lean_unsigned_to_nat(0u);
v___x_4075_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_4073_, v_packages_4069_, v___x_4074_);
if (lean_obj_tag(v___x_4075_) == 1)
{
lean_object* v_val_4076_; lean_object* v___x_4077_; lean_object* v___x_4079_; 
v_val_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_val_4076_);
lean_dec_ref_known(v___x_4075_, 1);
v___x_4077_ = lean_array_push(v_depIdxs_4065_, v_val_4076_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 1, v___x_4077_);
v___x_4079_ = v___x_4067_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_ws_4064_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
v_i_4057_ = v___x_4071_;
v_b_4059_ = v___x_4079_;
goto _start;
}
}
else
{
lean_object* v_baseName_4082_; lean_object* v_name_4083_; lean_object* v_opts_4084_; uint8_t v___x_4085_; 
lean_dec(v___x_4075_);
v_baseName_4082_ = lean_ctor_get(v_pkg_4053_, 1);
v_name_4083_ = lean_ctor_get(v___x_4072_, 0);
v_opts_4084_ = lean_ctor_get(v___x_4072_, 4);
v___x_4085_ = lean_name_eq(v_baseName_4082_, v_name_4083_);
if (v___x_4085_ == 0)
{
lean_object* v___x_4086_; 
lean_inc_ref(v___y_4061_);
lean_inc_ref(v_ws_4064_);
lean_inc(v___x_4072_);
lean_inc_ref(v_pkg_4053_);
v___x_4086_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_4053_, v___x_4072_, v_ws_4064_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4145_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4089_ = v___x_4086_;
v_isShared_4090_ = v_isSharedCheck_4145_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4086_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4145_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v_fst_4091_; lean_object* v_snd_4092_; lean_object* v___x_4093_; lean_object* v_wsIdx_4094_; lean_object* v___x_4095_; 
v_fst_4091_ = lean_ctor_get(v_a_4087_, 0);
lean_inc(v_fst_4091_);
v_snd_4092_ = lean_ctor_get(v_a_4087_, 1);
lean_inc(v_snd_4092_);
lean_dec(v_a_4087_);
v___x_4093_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_4094_ = lean_array_get_size(v_packages_4069_);
lean_inc_ref(v_leanOpts_4054_);
lean_inc(v_opts_4084_);
v___x_4095_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_4064_, v_fst_4091_, v_opts_4084_, v_leanOpts_4054_, v_reconfigure_4055_, v___x_4093_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v_a_4097_; lean_object* v___x_4098_; lean_object* v___x_4100_; 
lean_del_object(v___x_4089_);
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_a_4096_);
v_a_4097_ = lean_ctor_get(v___x_4095_, 1);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4095_, 2);
v___x_4098_ = lean_array_push(v_depIdxs_4065_, v_wsIdx_4094_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 1, v___x_4098_);
lean_ctor_set(v___x_4067_, 0, v_a_4096_);
v___x_4100_ = v___x_4067_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4096_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v___x_4098_);
v___x_4100_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
lean_object* v___x_4101_; uint8_t v___x_4102_; 
v___x_4101_ = lean_array_get_size(v_a_4097_);
v___x_4102_ = lean_nat_dec_lt(v___x_4074_, v___x_4101_);
if (v___x_4102_ == 0)
{
lean_dec(v_a_4097_);
v_i_4057_ = v___x_4071_;
v_b_4059_ = v___x_4100_;
v___y_4060_ = v_snd_4092_;
goto _start;
}
else
{
lean_object* v___x_4104_; size_t v___x_4105_; size_t v___x_4106_; lean_object* v___x_4107_; 
v___x_4104_ = lean_box(0);
v___x_4105_ = ((size_t)0ULL);
v___x_4106_ = lean_usize_of_nat(v___x_4101_);
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4097_, v___x_4105_, v___x_4106_, v___x_4104_, v___y_4061_);
lean_dec(v_a_4097_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_dec_ref_known(v___x_4107_, 1);
v_i_4057_ = v___x_4071_;
v_b_4059_ = v___x_4100_;
v___y_4060_ = v_snd_4092_;
goto _start;
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
lean_dec_ref(v___x_4100_);
lean_dec(v_snd_4092_);
lean_dec_ref(v_leanOpts_4054_);
lean_dec_ref(v_pkg_4053_);
v_a_4109_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4107_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4107_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4119_; uint8_t v___x_4120_; 
lean_dec(v_snd_4092_);
lean_del_object(v___x_4067_);
lean_dec_ref(v_depIdxs_4065_);
lean_dec_ref(v_leanOpts_4054_);
lean_dec_ref(v_pkg_4053_);
v_a_4118_ = lean_ctor_get(v___x_4095_, 1);
lean_inc(v_a_4118_);
lean_dec_ref_known(v___x_4095_, 2);
v___x_4119_ = lean_array_get_size(v_a_4118_);
v___x_4120_ = lean_nat_dec_lt(v___x_4074_, v___x_4119_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4121_; lean_object* v___x_4123_; 
lean_dec(v_a_4118_);
v___x_4121_ = lean_box(0);
if (v_isShared_4090_ == 0)
{
lean_ctor_set_tag(v___x_4089_, 1);
lean_ctor_set(v___x_4089_, 0, v___x_4121_);
v___x_4123_ = v___x_4089_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4121_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
else
{
lean_object* v___x_4125_; size_t v___x_4126_; size_t v___x_4127_; lean_object* v___x_4128_; 
lean_del_object(v___x_4089_);
v___x_4125_ = lean_box(0);
v___x_4126_ = ((size_t)0ULL);
v___x_4127_ = lean_usize_of_nat(v___x_4119_);
v___x_4128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4118_, v___x_4126_, v___x_4127_, v___x_4125_, v___y_4061_);
lean_dec(v_a_4118_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4135_ == 0)
{
lean_object* v_unused_4136_; 
v_unused_4136_ = lean_ctor_get(v___x_4128_, 0);
lean_dec(v_unused_4136_);
v___x_4130_ = v___x_4128_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_dec(v___x_4128_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 1);
lean_ctor_set(v___x_4130_, 0, v___x_4125_);
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4125_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
v_a_4137_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4128_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4128_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_del_object(v___x_4067_);
lean_dec_ref(v_depIdxs_4065_);
lean_dec_ref(v_ws_4064_);
lean_dec_ref(v_leanOpts_4054_);
lean_dec_ref(v_pkg_4053_);
v_a_4146_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4086_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4086_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_inc(v_baseName_4082_);
lean_del_object(v___x_4067_);
lean_dec_ref(v_depIdxs_4065_);
lean_dec_ref(v_ws_4064_);
lean_dec(v___y_4060_);
lean_dec_ref(v_leanOpts_4054_);
lean_dec_ref(v_pkg_4053_);
v___x_4154_ = l_Lean_Name_toString(v_baseName_4082_, v___x_4063_);
v___x_4155_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_4156_ = lean_string_append(v___x_4154_, v___x_4155_);
v___x_4157_ = 3;
v___x_4158_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set_uint8(v___x_4158_, sizeof(void*)*1, v___x_4157_);
lean_inc_ref(v___y_4061_);
v___x_4159_ = lean_apply_2(v___y_4061_, v___x_4158_, lean_box(0));
v___x_4160_ = lean_box(0);
v___x_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
return v___x_4161_;
}
}
}
}
else
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
lean_dec_ref(v_leanOpts_4054_);
lean_dec_ref(v_pkg_4053_);
v___x_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4163_, 0, v_b_4059_);
lean_ctor_set(v___x_4163_, 1, v___y_4060_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_4053_ = stack[0].m_obj;
lean_object* v_leanOpts_4054_ = stack[1].m_obj;
uint8_t v_reconfigure_4055_ = stack[2].m_num;
lean_object* v_as_4056_ = stack[3].m_obj;
size_t v_i_4057_ = stack[4].m_num;
size_t v_stop_4058_ = stack[5].m_num;
lean_object* v_b_4059_ = stack[6].m_obj;
lean_object* v___y_4060_ = stack[7].m_obj;
lean_object* v___y_4061_ = stack[8].m_obj;
lean_object* v_res_4165_;
v_res_4165_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4053_, v_leanOpts_4054_, v_reconfigure_4055_, v_as_4056_, v_i_4057_, v_stop_4058_, v_b_4059_, v___y_4060_, v___y_4061_);
stack->m_obj
 = v_res_4165_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___boxed(lean_object* v_pkg_4166_, lean_object* v_leanOpts_4167_, lean_object* v_reconfigure_4168_, lean_object* v_as_4169_, lean_object* v_i_4170_, lean_object* v_stop_4171_, lean_object* v_b_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
uint8_t v_reconfigure_boxed_4176_; size_t v_i_boxed_4177_; size_t v_stop_boxed_4178_; lean_object* v_res_4179_; 
v_reconfigure_boxed_4176_ = lean_unbox(v_reconfigure_4168_);
v_i_boxed_4177_ = lean_unbox_usize(v_i_4170_);
lean_dec(v_i_4170_);
v_stop_boxed_4178_ = lean_unbox_usize(v_stop_4171_);
lean_dec(v_stop_4171_);
v_res_4179_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4166_, v_leanOpts_4167_, v_reconfigure_boxed_4176_, v_as_4169_, v_i_boxed_4177_, v_stop_boxed_4178_, v_b_4172_, v___y_4173_, v___y_4174_);
lean_dec_ref(v___y_4174_);
lean_dec_ref(v_as_4169_);
return v_res_4179_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object* v_leanOpts_4180_, uint8_t v_reconfigure_4181_, lean_object* v_ws_4182_, lean_object* v_i_4183_, lean_object* v_next_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v_packages_4188_; lean_object* v_pkg_4189_; lean_object* v_ws_4191_; lean_object* v_depIdxs_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v_____x_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v_depConfigs_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v_s_4213_; lean_object* v___x_4214_; uint8_t v___x_4215_; 
v_packages_4188_ = lean_ctor_get(v_ws_4182_, 4);
v_pkg_4189_ = lean_array_fget(v_packages_4188_, v_i_4183_);
lean_dec(v_i_4183_);
v_depConfigs_4210_ = lean_ctor_get(v_pkg_4189_, 12);
v___x_4211_ = lean_array_get_size(v_depConfigs_4210_);
v___x_4212_ = lean_mk_empty_array_with_capacity(v___x_4211_);
lean_inc_ref(v___x_4212_);
lean_inc_ref(v_ws_4182_);
v_s_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_4213_, 0, v_ws_4182_);
lean_ctor_set(v_s_4213_, 1, v___x_4212_);
v___x_4214_ = lean_unsigned_to_nat(0u);
v___x_4215_ = lean_nat_dec_le(v___x_4211_, v___x_4211_);
if (v___x_4215_ == 0)
{
uint8_t v___x_4216_; 
v___x_4216_ = lean_nat_dec_lt(v___x_4214_, v___x_4211_);
if (v___x_4216_ == 0)
{
lean_object* v_ws_4217_; lean_object* v_packages_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
lean_dec_ref_known(v_s_4213_, 2);
v_ws_4217_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4182_, v_pkg_4189_, v___x_4212_);
v_packages_4218_ = lean_ctor_get(v_ws_4217_, 4);
v___x_4219_ = lean_array_get_size(v_packages_4218_);
v___x_4220_ = lean_nat_dec_lt(v_next_4184_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
lean_dec(v_next_4184_);
lean_dec_ref(v_leanOpts_4180_);
v___x_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4221_, 0, v_ws_4217_);
lean_ctor_set(v___x_4221_, 1, v___y_4185_);
v___x_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4221_);
return v___x_4222_;
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = lean_unsigned_to_nat(1u);
v___x_4224_ = lean_nat_add(v_next_4184_, v___x_4223_);
v_ws_4182_ = v_ws_4217_;
v_i_4183_ = v_next_4184_;
v_next_4184_ = v___x_4224_;
goto _start;
}
}
else
{
size_t v___x_4226_; size_t v___x_4227_; lean_object* v___x_4228_; 
lean_dec_ref(v___x_4212_);
lean_dec_ref(v_ws_4182_);
v___x_4226_ = lean_usize_of_nat(v___x_4211_);
v___x_4227_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4180_);
lean_inc(v_pkg_4189_);
v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4189_, v_leanOpts_4180_, v_reconfigure_4181_, v_depConfigs_4210_, v___x_4226_, v___x_4227_, v_s_4213_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; lean_object* v_fst_4230_; lean_object* v_snd_4231_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v___x_4228_, 1);
v_fst_4230_ = lean_ctor_get(v_a_4229_, 0);
lean_inc(v_fst_4230_);
v_snd_4231_ = lean_ctor_get(v_a_4229_, 1);
lean_inc(v_snd_4231_);
lean_dec(v_a_4229_);
v_____x_4205_ = v_fst_4230_;
v___y_4206_ = v_snd_4231_;
v___y_4207_ = v___y_4186_;
goto v___jp_4204_;
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
lean_dec(v_pkg_4189_);
lean_dec(v_next_4184_);
lean_dec_ref(v_leanOpts_4180_);
v_a_4232_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4228_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4228_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
}
else
{
uint8_t v___x_4240_; 
v___x_4240_ = lean_nat_dec_lt(v___x_4214_, v___x_4211_);
if (v___x_4240_ == 0)
{
lean_dec_ref_known(v_s_4213_, 2);
v_ws_4191_ = v_ws_4182_;
v_depIdxs_4192_ = v___x_4212_;
v___y_4193_ = v___y_4185_;
v___y_4194_ = v___y_4186_;
goto v___jp_4190_;
}
else
{
size_t v___x_4241_; size_t v___x_4242_; lean_object* v___x_4243_; 
lean_dec_ref(v___x_4212_);
lean_dec_ref(v_ws_4182_);
v___x_4241_ = lean_usize_of_nat(v___x_4211_);
v___x_4242_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4180_);
lean_inc(v_pkg_4189_);
v___x_4243_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4189_, v_leanOpts_4180_, v_reconfigure_4181_, v_depConfigs_4210_, v___x_4241_, v___x_4242_, v_s_4213_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v_fst_4245_; lean_object* v_snd_4246_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v___x_4243_, 1);
v_fst_4245_ = lean_ctor_get(v_a_4244_, 0);
lean_inc(v_fst_4245_);
v_snd_4246_ = lean_ctor_get(v_a_4244_, 1);
lean_inc(v_snd_4246_);
lean_dec(v_a_4244_);
v_____x_4205_ = v_fst_4245_;
v___y_4206_ = v_snd_4246_;
v___y_4207_ = v___y_4186_;
goto v___jp_4204_;
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_dec(v_pkg_4189_);
lean_dec(v_next_4184_);
lean_dec_ref(v_leanOpts_4180_);
v_a_4247_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4243_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4243_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
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
v___jp_4190_:
{
lean_object* v_ws_4195_; lean_object* v_packages_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v_ws_4195_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4191_, v_pkg_4189_, v_depIdxs_4192_);
v_packages_4196_ = lean_ctor_get(v_ws_4195_, 4);
v___x_4197_ = lean_array_get_size(v_packages_4196_);
v___x_4198_ = lean_nat_dec_lt(v_next_4184_, v___x_4197_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
lean_dec(v_next_4184_);
lean_dec_ref(v_leanOpts_4180_);
v___x_4199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4199_, 0, v_ws_4195_);
lean_ctor_set(v___x_4199_, 1, v___y_4193_);
v___x_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
return v___x_4200_;
}
else
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = lean_unsigned_to_nat(1u);
v___x_4202_ = lean_nat_add(v_next_4184_, v___x_4201_);
v_ws_4182_ = v_ws_4195_;
v_i_4183_ = v_next_4184_;
v_next_4184_ = v___x_4202_;
v___y_4185_ = v___y_4193_;
v___y_4186_ = v___y_4194_;
goto _start;
}
}
v___jp_4204_:
{
lean_object* v_ws_4208_; lean_object* v_depIdxs_4209_; 
v_ws_4208_ = lean_ctor_get(v_____x_4205_, 0);
lean_inc_ref(v_ws_4208_);
v_depIdxs_4209_ = lean_ctor_get(v_____x_4205_, 1);
lean_inc_ref(v_depIdxs_4209_);
lean_dec_ref(v_____x_4205_);
v_ws_4191_ = v_ws_4208_;
v_depIdxs_4192_ = v_depIdxs_4209_;
v___y_4193_ = v___y_4206_;
v___y_4194_ = v___y_4207_;
goto v___jp_4190_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_leanOpts_4180_ = stack[0].m_obj;
uint8_t v_reconfigure_4181_ = stack[1].m_num;
lean_object* v_ws_4182_ = stack[2].m_obj;
lean_object* v_i_4183_ = stack[3].m_obj;
lean_object* v_next_4184_ = stack[4].m_obj;
lean_object* v___y_4185_ = stack[5].m_obj;
lean_object* v___y_4186_ = stack[6].m_obj;
lean_object* v_res_4255_;
v_res_4255_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4180_, v_reconfigure_4181_, v_ws_4182_, v_i_4183_, v_next_4184_, v___y_4185_, v___y_4186_);
stack->m_obj
 = v_res_4255_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object* v_leanOpts_4256_, lean_object* v_reconfigure_4257_, lean_object* v_ws_4258_, lean_object* v_i_4259_, lean_object* v_next_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
uint8_t v_reconfigure_boxed_4264_; lean_object* v_res_4265_; 
v_reconfigure_boxed_4264_ = lean_unbox(v_reconfigure_4257_);
v_res_4265_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4256_, v_reconfigure_boxed_4264_, v_ws_4258_, v_i_4259_, v_next_4260_, v___y_4261_, v___y_4262_);
lean_dec_ref(v___y_4262_);
return v_res_4265_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4268_, lean_object* v_toUpdate_4269_, lean_object* v_leanOpts_4270_, uint8_t v_updateToolchain_4271_, lean_object* v_a_4272_){
_start:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4274_ = lean_box(1);
v___x_4275_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4272_, v_ws_4268_, v_toUpdate_4269_, v___x_4274_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v_snd_4277_; uint8_t v___x_4278_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v___x_4275_, 1);
v_snd_4277_ = lean_ctor_get(v_a_4276_, 1);
lean_inc(v_snd_4277_);
lean_dec(v_a_4276_);
v___x_4278_ = 1;
if (v_updateToolchain_4271_ == 0)
{
lean_object* v_packages_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v_wsIdx_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v_packages_4279_ = lean_ctor_get(v_ws_4268_, 4);
v___x_4280_ = lean_unsigned_to_nat(0u);
v___x_4281_ = lean_array_fget_borrowed(v_packages_4279_, v___x_4280_);
v_wsIdx_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_wsIdx_4282_);
v___x_4283_ = lean_array_get_size(v_packages_4279_);
v___x_4284_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4270_, v___x_4278_, v_ws_4268_, v_wsIdx_4282_, v___x_4283_, v_snd_4277_, v_a_4272_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4302_; 
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4287_ = v___x_4284_;
v_isShared_4288_ = v_isSharedCheck_4302_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4284_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4302_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v_fst_4289_; lean_object* v_snd_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4301_; 
v_fst_4289_ = lean_ctor_get(v_a_4285_, 0);
v_snd_4290_ = lean_ctor_get(v_a_4285_, 1);
v_isSharedCheck_4301_ = !lean_is_exclusive(v_a_4285_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4292_ = v_a_4285_;
v_isShared_4293_ = v_isSharedCheck_4301_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_snd_4290_);
lean_inc(v_fst_4289_);
lean_dec(v_a_4285_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4301_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4294_; lean_object* v___x_4296_; 
v___x_4294_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4289_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v___x_4294_);
v___x_4296_ = v___x_4292_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4294_);
lean_ctor_set(v_reuseFailAlloc_4300_, 1, v_snd_4290_);
v___x_4296_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
lean_object* v___x_4298_; 
if (v_isShared_4288_ == 0)
{
lean_ctor_set(v___x_4287_, 0, v___x_4296_);
v___x_4298_ = v___x_4287_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4296_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
}
else
{
return v___x_4284_;
}
}
else
{
lean_object* v_packages_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v_depConfigs_4306_; lean_object* v___x_4307_; lean_object* v___f_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v_packages_4303_ = lean_ctor_get(v_ws_4268_, 4);
v___x_4304_ = lean_unsigned_to_nat(0u);
v___x_4305_ = lean_array_fget_borrowed(v_packages_4303_, v___x_4304_);
v_depConfigs_4306_ = lean_ctor_get(v___x_4305_, 12);
v___x_4307_ = lean_box(v_updateToolchain_4271_);
lean_inc_ref(v_ws_4268_);
lean_inc(v___x_4305_);
v___f_4308_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4308_, 0, v___x_4305_);
lean_closure_set(v___f_4308_, 1, v___x_4307_);
lean_closure_set(v___f_4308_, 2, v_ws_4268_);
v___x_4309_ = lean_array_get_size(v_depConfigs_4306_);
lean_inc_ref(v_depConfigs_4306_);
v___x_4310_ = l_Array_reverse___redArg(v_depConfigs_4306_);
v___x_4311_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4312_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4309_, v___f_4308_, v___x_4310_, v___x_4304_, v___x_4311_, v_snd_4277_, v_a_4272_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v_fst_4314_; lean_object* v_snd_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4387_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4312_, 1);
v_fst_4314_ = lean_ctor_get(v_a_4313_, 0);
v_snd_4315_ = lean_ctor_get(v_a_4313_, 1);
v_isSharedCheck_4387_ = !lean_is_exclusive(v_a_4313_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4317_ = v_a_4313_;
v_isShared_4318_ = v_isSharedCheck_4387_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_snd_4315_);
lean_inc(v_fst_4314_);
lean_dec(v_a_4313_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4387_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4319_; 
lean_inc_ref(v_ws_4268_);
v___x_4319_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4272_, v_ws_4268_, v_fst_4314_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v___x_4320_; lean_object* v___x_4321_; 
lean_dec_ref_known(v___x_4319_, 1);
v___x_4320_ = lean_array_get_size(v_packages_4303_);
lean_inc_ref(v_leanOpts_4270_);
v___x_4321_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4309_, v_fst_4314_, v___x_4310_, v_leanOpts_4270_, v___x_4304_, v_ws_4268_, v_snd_4315_, v_a_4272_);
lean_dec_ref(v___x_4310_);
lean_dec(v_fst_4314_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4370_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4324_ = v___x_4321_;
v_isShared_4325_ = v_isSharedCheck_4370_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4321_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4370_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v_fst_4326_; lean_object* v_snd_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4369_; 
v_fst_4326_ = lean_ctor_get(v_a_4322_, 0);
v_snd_4327_ = lean_ctor_get(v_a_4322_, 1);
v_isSharedCheck_4369_ = !lean_is_exclusive(v_a_4322_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4329_ = v_a_4322_;
v_isShared_4330_ = v_isSharedCheck_4369_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_snd_4327_);
lean_inc(v_fst_4326_);
lean_dec(v_a_4322_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4369_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v_packages_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4336_; 
v_packages_4331_ = lean_ctor_get(v_fst_4326_, 4);
v___x_4332_ = lean_array_get_size(v_packages_4331_);
v___x_4333_ = lean_array_fget(v_packages_4331_, v___x_4304_);
v___x_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4320_);
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 1, v___x_4332_);
lean_ctor_set(v___x_4317_, 0, v___x_4334_);
v___x_4336_ = v___x_4317_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v___x_4334_);
lean_ctor_set(v_reuseFailAlloc_4368_, 1, v___x_4332_);
v___x_4336_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4337_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4336_, v___x_4311_);
v___x_4338_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4326_, v___x_4333_, v___x_4337_);
v___x_4339_ = lean_nat_dec_eq(v___x_4320_, v___x_4332_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
lean_del_object(v___x_4329_);
lean_del_object(v___x_4324_);
v___x_4340_ = lean_unsigned_to_nat(1u);
v___x_4341_ = lean_nat_add(v___x_4320_, v___x_4340_);
v___x_4342_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4270_, v___x_4278_, v___x_4338_, v___x_4320_, v___x_4341_, v_snd_4327_, v_a_4272_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4360_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4345_ = v___x_4342_;
v_isShared_4346_ = v_isSharedCheck_4360_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4342_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4360_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v_fst_4347_; lean_object* v_snd_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4359_; 
v_fst_4347_ = lean_ctor_get(v_a_4343_, 0);
v_snd_4348_ = lean_ctor_get(v_a_4343_, 1);
v_isSharedCheck_4359_ = !lean_is_exclusive(v_a_4343_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4350_ = v_a_4343_;
v_isShared_4351_ = v_isSharedCheck_4359_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_snd_4348_);
lean_inc(v_fst_4347_);
lean_dec(v_a_4343_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4359_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4352_; lean_object* v___x_4354_; 
v___x_4352_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4347_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v___x_4352_);
v___x_4354_ = v___x_4350_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4352_);
lean_ctor_set(v_reuseFailAlloc_4358_, 1, v_snd_4348_);
v___x_4354_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
lean_object* v___x_4356_; 
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 0, v___x_4354_);
v___x_4356_ = v___x_4345_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4354_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
}
else
{
return v___x_4342_;
}
}
else
{
lean_object* v___x_4361_; lean_object* v___x_4363_; 
lean_dec_ref(v_leanOpts_4270_);
v___x_4361_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4338_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v___x_4361_);
v___x_4363_ = v___x_4329_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4361_);
lean_ctor_set(v_reuseFailAlloc_4367_, 1, v_snd_4327_);
v___x_4363_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4365_; 
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 0, v___x_4363_);
v___x_4365_ = v___x_4324_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4363_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_del_object(v___x_4317_);
lean_dec_ref(v_leanOpts_4270_);
v_a_4371_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4321_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4321_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_del_object(v___x_4317_);
lean_dec(v_snd_4315_);
lean_dec(v_fst_4314_);
lean_dec_ref(v___x_4310_);
lean_dec_ref(v_leanOpts_4270_);
lean_dec_ref(v_ws_4268_);
v_a_4379_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4319_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4319_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec_ref(v___x_4310_);
lean_dec_ref(v_leanOpts_4270_);
lean_dec_ref(v_ws_4268_);
v_a_4388_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4312_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4312_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec_ref(v_leanOpts_4270_);
lean_dec_ref(v_ws_4268_);
v_a_4396_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4275_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4275_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_4268_ = stack[0].m_obj;
lean_object* v_toUpdate_4269_ = stack[1].m_obj;
lean_object* v_leanOpts_4270_ = stack[2].m_obj;
uint8_t v_updateToolchain_4271_ = stack[3].m_num;
lean_object* v_a_4272_ = stack[4].m_obj;
lean_object* v_res_4404_;
v_res_4404_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4268_, v_toUpdate_4269_, v_leanOpts_4270_, v_updateToolchain_4271_, v_a_4272_);
stack->m_obj
 = v_res_4404_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4405_, lean_object* v_toUpdate_4406_, lean_object* v_leanOpts_4407_, lean_object* v_updateToolchain_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_){
_start:
{
uint8_t v_updateToolchain_boxed_4411_; lean_object* v_res_4412_; 
v_updateToolchain_boxed_4411_ = lean_unbox(v_updateToolchain_4408_);
v_res_4412_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4405_, v_toUpdate_4406_, v_leanOpts_4407_, v_updateToolchain_boxed_4411_, v_a_4409_);
lean_dec_ref(v_a_4409_);
return v_res_4412_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_leanOpts_4413_, uint8_t v_reconfigure_4414_, lean_object* v_ws_4415_, lean_object* v_i_4416_, lean_object* v_i__lt_4417_, lean_object* v_next_4418_, lean_object* v_lt__next_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4413_, v_reconfigure_4414_, v_ws_4415_, v_i_4416_, v_next_4418_, v___y_4420_, v___y_4421_);
return v___x_4423_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_leanOpts_4413_ = stack[0].m_obj;
uint8_t v_reconfigure_4414_ = stack[1].m_num;
lean_object* v_ws_4415_ = stack[2].m_obj;
lean_object* v_i_4416_ = stack[3].m_obj;
lean_object* v_next_4418_ = stack[5].m_obj;
lean_object* v___y_4420_ = stack[7].m_obj;
lean_object* v___y_4421_ = stack[8].m_obj;
lean_object* v_res_4424_;
v_res_4424_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4413_, v_reconfigure_4414_, v_ws_4415_, v_i_4416_, lean_box(0), v_next_4418_, lean_box(0), v___y_4420_, v___y_4421_);
stack->m_obj
 = v_res_4424_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_leanOpts_4425_, lean_object* v_reconfigure_4426_, lean_object* v_ws_4427_, lean_object* v_i_4428_, lean_object* v_i__lt_4429_, lean_object* v_next_4430_, lean_object* v_lt__next_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
uint8_t v_reconfigure_boxed_4435_; lean_object* v_res_4436_; 
v_reconfigure_boxed_4435_ = lean_unbox(v_reconfigure_4426_);
v_res_4436_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4425_, v_reconfigure_boxed_4435_, v_ws_4427_, v_i_4428_, v_i__lt_4429_, v_next_4430_, v_lt__next_4431_, v___y_4432_, v___y_4433_);
lean_dec_ref(v___y_4433_);
return v_res_4436_;
}
}
lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_00_u03b1_4437_, lean_object* v_00_u03b2_4438_, lean_object* v_n_4439_, lean_object* v_f_4440_, lean_object* v_xs_4441_, lean_object* v_k_4442_, lean_object* v_h_4443_, lean_object* v_acc_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4439_, v_f_4440_, v_xs_4441_, v_k_4442_, v_acc_4444_, v___y_4445_, v___y_4446_);
return v___x_4448_;
}
}
LEAN_EXPORT void l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_4439_ = stack[2].m_obj;
lean_object* v_f_4440_ = stack[3].m_obj;
lean_object* v_xs_4441_ = stack[4].m_obj;
lean_object* v_k_4442_ = stack[5].m_obj;
lean_object* v_acc_4444_ = stack[7].m_obj;
lean_object* v___y_4445_ = stack[8].m_obj;
lean_object* v___y_4446_ = stack[9].m_obj;
lean_object* v_res_4449_;
v_res_4449_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_box(0), lean_box(0), v_n_4439_, v_f_4440_, v_xs_4441_, v_k_4442_, lean_box(0), v_acc_4444_, v___y_4445_, v___y_4446_);
stack->m_obj
 = v_res_4449_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_00_u03b1_4450_, lean_object* v_00_u03b2_4451_, lean_object* v_n_4452_, lean_object* v_f_4453_, lean_object* v_xs_4454_, lean_object* v_k_4455_, lean_object* v_h_4456_, lean_object* v_acc_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_00_u03b1_4450_, v_00_u03b2_4451_, v_n_4452_, v_f_4453_, v_xs_4454_, v_k_4455_, v_h_4456_, v_acc_4457_, v___y_4458_, v___y_4459_);
lean_dec_ref(v___y_4459_);
lean_dec_ref(v_xs_4454_);
lean_dec(v_n_4452_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_inst_4462_, lean_object* v_R_4463_, lean_object* v_a_4464_, lean_object* v_b_4465_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_a_4464_, v_b_4465_);
return v___x_4466_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_upperBound_4467_, lean_object* v_fst_4468_, lean_object* v___x_4469_, lean_object* v_leanOpts_4470_, lean_object* v_inst_4471_, lean_object* v_R_4472_, lean_object* v_a_4473_, lean_object* v_b_4474_, lean_object* v_c_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4467_, v_fst_4468_, v___x_4469_, v_leanOpts_4470_, v_a_4473_, v_b_4474_, v___y_4476_, v___y_4477_);
return v___x_4479_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4467_ = stack[0].m_obj;
lean_object* v_fst_4468_ = stack[1].m_obj;
lean_object* v___x_4469_ = stack[2].m_obj;
lean_object* v_leanOpts_4470_ = stack[3].m_obj;
lean_object* v_a_4473_ = stack[6].m_obj;
lean_object* v_b_4474_ = stack[7].m_obj;
lean_object* v___y_4476_ = stack[9].m_obj;
lean_object* v___y_4477_ = stack[10].m_obj;
lean_object* v_res_4480_;
v_res_4480_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4467_, v_fst_4468_, v___x_4469_, v_leanOpts_4470_, lean_box(0), lean_box(0), v_a_4473_, v_b_4474_, lean_box(0), v___y_4476_, v___y_4477_);
stack->m_obj
 = v_res_4480_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_upperBound_4481_, lean_object* v_fst_4482_, lean_object* v___x_4483_, lean_object* v_leanOpts_4484_, lean_object* v_inst_4485_, lean_object* v_R_4486_, lean_object* v_a_4487_, lean_object* v_b_4488_, lean_object* v_c_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4481_, v_fst_4482_, v___x_4483_, v_leanOpts_4484_, v_inst_4485_, v_R_4486_, v_a_4487_, v_b_4488_, v_c_4489_, v___y_4490_, v___y_4491_);
lean_dec_ref(v___y_4491_);
lean_dec_ref(v___x_4483_);
lean_dec_ref(v_fst_4482_);
lean_dec(v_upperBound_4481_);
return v_res_4493_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_start_4494_, lean_object* v_pkg_4495_, lean_object* v_leanOpts_4496_, uint8_t v_reconfigure_4497_, lean_object* v_as_4498_, size_t v_i_4499_, size_t v_stop_4500_, lean_object* v_b_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
lean_object* v___x_4505_; 
v___x_4505_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4495_, v_leanOpts_4496_, v_reconfigure_4497_, v_as_4498_, v_i_4499_, v_stop_4500_, v_b_4501_, v___y_4502_, v___y_4503_);
return v___x_4505_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_4494_ = stack[0].m_obj;
lean_object* v_pkg_4495_ = stack[1].m_obj;
lean_object* v_leanOpts_4496_ = stack[2].m_obj;
uint8_t v_reconfigure_4497_ = stack[3].m_num;
lean_object* v_as_4498_ = stack[4].m_obj;
size_t v_i_4499_ = stack[5].m_num;
size_t v_stop_4500_ = stack[6].m_num;
lean_object* v_b_4501_ = stack[7].m_obj;
lean_object* v___y_4502_ = stack[8].m_obj;
lean_object* v___y_4503_ = stack[9].m_obj;
lean_object* v_res_4506_;
v_res_4506_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_start_4494_, v_pkg_4495_, v_leanOpts_4496_, v_reconfigure_4497_, v_as_4498_, v_i_4499_, v_stop_4500_, v_b_4501_, v___y_4502_, v___y_4503_);
stack->m_obj
 = v_res_4506_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_start_4507_, lean_object* v_pkg_4508_, lean_object* v_leanOpts_4509_, lean_object* v_reconfigure_4510_, lean_object* v_as_4511_, lean_object* v_i_4512_, lean_object* v_stop_4513_, lean_object* v_b_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
uint8_t v_reconfigure_boxed_4518_; size_t v_i_boxed_4519_; size_t v_stop_boxed_4520_; lean_object* v_res_4521_; 
v_reconfigure_boxed_4518_ = lean_unbox(v_reconfigure_4510_);
v_i_boxed_4519_ = lean_unbox_usize(v_i_4512_);
lean_dec(v_i_4512_);
v_stop_boxed_4520_ = lean_unbox_usize(v_stop_4513_);
lean_dec(v_stop_4513_);
v_res_4521_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_start_4507_, v_pkg_4508_, v_leanOpts_4509_, v_reconfigure_boxed_4518_, v_as_4511_, v_i_boxed_4519_, v_stop_boxed_4520_, v_b_4514_, v___y_4515_, v___y_4516_);
lean_dec_ref(v___y_4516_);
lean_dec_ref(v_as_4511_);
lean_dec(v_start_4507_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_4522_, lean_object* v_msg_4523_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v_msg_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object* v_00_u03b2_4525_, lean_object* v_k_4526_, lean_object* v_v_4527_, lean_object* v_t_4528_){
_start:
{
lean_object* v___x_4529_; 
v___x_4529_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_4526_, v_v_4527_, v_t_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object* v_init_4530_, lean_object* v_t_4531_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_4530_, v_t_4531_);
return v___x_4532_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4533_, lean_object* v_as_4534_, size_t v_i_4535_, size_t v_stop_4536_, lean_object* v_b_4537_){
_start:
{
lean_object* v___y_4539_; uint8_t v___x_4543_; 
v___x_4543_ = lean_usize_dec_eq(v_i_4535_, v_stop_4536_);
if (v___x_4543_ == 0)
{
lean_object* v___x_4544_; lean_object* v_baseName_4545_; lean_object* v_relConfigFile_4546_; lean_object* v_relManifestFile_4547_; lean_object* v___x_4548_; 
v___x_4544_ = lean_array_uget_borrowed(v_as_4534_, v_i_4535_);
v_baseName_4545_ = lean_ctor_get(v___x_4544_, 1);
v_relConfigFile_4546_ = lean_ctor_get(v___x_4544_, 8);
v_relManifestFile_4547_ = lean_ctor_get(v___x_4544_, 9);
v___x_4548_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4533_, v_baseName_4545_);
if (lean_obj_tag(v___x_4548_) == 0)
{
v___y_4539_ = v_b_4537_;
goto v___jp_4538_;
}
else
{
lean_object* v_val_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4570_; 
v_val_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4570_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_val_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4570_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v_name_4553_; lean_object* v_scope_4554_; uint8_t v_inherited_4555_; lean_object* v_src_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4567_; 
v_name_4553_ = lean_ctor_get(v_val_4549_, 0);
v_scope_4554_ = lean_ctor_get(v_val_4549_, 1);
v_inherited_4555_ = lean_ctor_get_uint8(v_val_4549_, sizeof(void*)*5);
v_src_4556_ = lean_ctor_get(v_val_4549_, 4);
v_isSharedCheck_4567_ = !lean_is_exclusive(v_val_4549_);
if (v_isSharedCheck_4567_ == 0)
{
lean_object* v_unused_4568_; lean_object* v_unused_4569_; 
v_unused_4568_ = lean_ctor_get(v_val_4549_, 3);
lean_dec(v_unused_4568_);
v_unused_4569_ = lean_ctor_get(v_val_4549_, 2);
lean_dec(v_unused_4569_);
v___x_4558_ = v_val_4549_;
v_isShared_4559_ = v_isSharedCheck_4567_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_src_4556_);
lean_inc(v_scope_4554_);
lean_inc(v_name_4553_);
lean_dec(v_val_4549_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4567_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
lean_inc_ref(v_relManifestFile_4547_);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v_relManifestFile_4547_);
v___x_4561_ = v___x_4551_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_relManifestFile_4547_);
v___x_4561_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
lean_object* v___x_4563_; 
lean_inc_ref(v_relConfigFile_4546_);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 3, v___x_4561_);
lean_ctor_set(v___x_4558_, 2, v_relConfigFile_4546_);
v___x_4563_ = v___x_4558_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_name_4553_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_scope_4554_);
lean_ctor_set(v_reuseFailAlloc_4565_, 2, v_relConfigFile_4546_);
lean_ctor_set(v_reuseFailAlloc_4565_, 3, v___x_4561_);
lean_ctor_set(v_reuseFailAlloc_4565_, 4, v_src_4556_);
lean_ctor_set_uint8(v_reuseFailAlloc_4565_, sizeof(void*)*5, v_inherited_4555_);
v___x_4563_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
lean_object* v___x_4564_; 
v___x_4564_ = lean_array_push(v_b_4537_, v___x_4563_);
v___y_4539_ = v___x_4564_;
goto v___jp_4538_;
}
}
}
}
}
}
else
{
return v_b_4537_;
}
v___jp_4538_:
{
size_t v___x_4540_; size_t v___x_4541_; 
v___x_4540_ = ((size_t)1ULL);
v___x_4541_ = lean_usize_add(v_i_4535_, v___x_4540_);
v_i_4535_ = v___x_4541_;
v_b_4537_ = v___y_4539_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_entries_4533_ = stack[0].m_obj;
lean_object* v_as_4534_ = stack[1].m_obj;
size_t v_i_4535_ = stack[2].m_num;
size_t v_stop_4536_ = stack[3].m_num;
lean_object* v_b_4537_ = stack[4].m_obj;
lean_object* v_res_4571_;
v_res_4571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4533_, v_as_4534_, v_i_4535_, v_stop_4536_, v_b_4537_);
stack->m_obj
 = v_res_4571_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4572_, lean_object* v_as_4573_, lean_object* v_i_4574_, lean_object* v_stop_4575_, lean_object* v_b_4576_){
_start:
{
size_t v_i_boxed_4577_; size_t v_stop_boxed_4578_; lean_object* v_res_4579_; 
v_i_boxed_4577_ = lean_unbox_usize(v_i_4574_);
lean_dec(v_i_4574_);
v_stop_boxed_4578_ = lean_unbox_usize(v_stop_4575_);
lean_dec(v_stop_4575_);
v_res_4579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4572_, v_as_4573_, v_i_boxed_4577_, v_stop_boxed_4578_, v_b_4576_);
lean_dec_ref(v_as_4573_);
lean_dec(v_entries_4572_);
return v_res_4579_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4580_, lean_object* v_entries_4581_){
_start:
{
lean_object* v_packages_4583_; lean_object* v___y_4585_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; uint8_t v___x_4603_; 
v_packages_4583_ = lean_ctor_get(v_ws_4580_, 4);
v___x_4600_ = lean_unsigned_to_nat(0u);
v___x_4601_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4602_ = lean_array_get_size(v_packages_4583_);
v___x_4603_ = lean_nat_dec_lt(v___x_4600_, v___x_4602_);
if (v___x_4603_ == 0)
{
v___y_4585_ = v___x_4601_;
goto v___jp_4584_;
}
else
{
uint8_t v___x_4604_; 
v___x_4604_ = lean_nat_dec_le(v___x_4602_, v___x_4602_);
if (v___x_4604_ == 0)
{
if (v___x_4603_ == 0)
{
v___y_4585_ = v___x_4601_;
goto v___jp_4584_;
}
else
{
size_t v___x_4605_; size_t v___x_4606_; lean_object* v___x_4607_; 
v___x_4605_ = ((size_t)0ULL);
v___x_4606_ = lean_usize_of_nat(v___x_4602_);
v___x_4607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4581_, v_packages_4583_, v___x_4605_, v___x_4606_, v___x_4601_);
v___y_4585_ = v___x_4607_;
goto v___jp_4584_;
}
}
else
{
size_t v___x_4608_; size_t v___x_4609_; lean_object* v___x_4610_; 
v___x_4608_ = ((size_t)0ULL);
v___x_4609_ = lean_usize_of_nat(v___x_4602_);
v___x_4610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4581_, v_packages_4583_, v___x_4608_, v___x_4609_, v___x_4601_);
v___y_4585_ = v___x_4610_;
goto v___jp_4584_;
}
}
v___jp_4584_:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v_config_4588_; lean_object* v_baseName_4589_; lean_object* v_dir_4590_; lean_object* v_relManifestFile_4591_; lean_object* v_toWorkspaceConfig_4592_; uint8_t v_fixedToolchain_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v_manifest_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4586_ = lean_unsigned_to_nat(0u);
v___x_4587_ = lean_array_fget_borrowed(v_packages_4583_, v___x_4586_);
v_config_4588_ = lean_ctor_get(v___x_4587_, 6);
v_baseName_4589_ = lean_ctor_get(v___x_4587_, 1);
v_dir_4590_ = lean_ctor_get(v___x_4587_, 4);
v_relManifestFile_4591_ = lean_ctor_get(v___x_4587_, 9);
v_toWorkspaceConfig_4592_ = lean_ctor_get(v_config_4588_, 0);
v_fixedToolchain_4593_ = lean_ctor_get_uint8(v_config_4588_, sizeof(void*)*28 + 6);
v___x_4594_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4592_);
v___x_4595_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4592_);
v___x_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
lean_inc(v_baseName_4589_);
v_manifest_4597_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4597_, 0, v_baseName_4589_);
lean_ctor_set(v_manifest_4597_, 1, v___x_4594_);
lean_ctor_set(v_manifest_4597_, 2, v___x_4596_);
lean_ctor_set(v_manifest_4597_, 3, v___y_4585_);
lean_ctor_set_uint8(v_manifest_4597_, sizeof(void*)*4, v_fixedToolchain_4593_);
lean_inc_ref(v_relManifestFile_4591_);
lean_inc_ref(v_dir_4590_);
v___x_4598_ = l_Lake_joinRelative(v_dir_4590_, v_relManifestFile_4591_);
v___x_4599_ = l_Lake_Manifest_save(v_manifest_4597_, v___x_4598_);
lean_dec_ref(v___x_4598_);
return v___x_4599_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_4580_ = stack[0].m_obj;
lean_object* v_entries_4581_ = stack[1].m_obj;
lean_object* v_res_4611_;
v_res_4611_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4580_, v_entries_4581_);
stack->m_obj
 = v_res_4611_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4612_, lean_object* v_entries_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4612_, v_entries_4613_);
lean_dec(v_entries_4613_);
lean_dec_ref(v_ws_4612_);
return v_res_4615_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4616_, lean_object* v_as_4617_, size_t v_i_4618_, size_t v_stop_4619_, lean_object* v_b_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v_a_4625_; lean_object* v___y_4630_; uint8_t v___x_4632_; 
v___x_4632_ = lean_usize_dec_eq(v_i_4618_, v_stop_4619_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_6568__overap_4635_; lean_object* v___x_4636_; 
v___x_4633_ = lean_unsigned_to_nat(0u);
v___x_4634_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_6568__overap_4635_ = lean_array_uget_borrowed(v_as_4617_, v_i_4618_);
lean_inc(v___x_6568__overap_4635_);
lean_inc(v___y_4621_);
lean_inc_ref(v_pkg_4616_);
v___x_4636_ = lean_apply_4(v___x_6568__overap_4635_, v_pkg_4616_, v___y_4621_, v___x_4634_, lean_box(0));
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v_a_4638_; lean_object* v___x_4639_; uint8_t v___x_4640_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
v_a_4638_ = lean_ctor_get(v___x_4636_, 1);
lean_inc(v_a_4638_);
lean_dec_ref_known(v___x_4636_, 2);
v___x_4639_ = lean_array_get_size(v_a_4638_);
v___x_4640_ = lean_nat_dec_lt(v___x_4633_, v___x_4639_);
if (v___x_4640_ == 0)
{
lean_dec(v_a_4638_);
v_a_4625_ = v_a_4637_;
goto v___jp_4624_;
}
else
{
lean_object* v___x_4641_; size_t v___x_4642_; size_t v___x_4643_; lean_object* v___x_4644_; 
v___x_4641_ = lean_box(0);
v___x_4642_ = ((size_t)0ULL);
v___x_4643_ = lean_usize_of_nat(v___x_4639_);
v___x_4644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4638_, v___x_4642_, v___x_4643_, v___x_4641_, v___y_4622_);
lean_dec(v_a_4638_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_dec_ref_known(v___x_4644_, 1);
v_a_4625_ = v_a_4637_;
goto v___jp_4624_;
}
else
{
lean_dec(v_a_4637_);
v___y_4630_ = v___x_4644_;
goto v___jp_4629_;
}
}
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4646_; uint8_t v___x_4647_; 
v_a_4645_ = lean_ctor_get(v___x_4636_, 1);
lean_inc(v_a_4645_);
lean_dec_ref_known(v___x_4636_, 2);
v___x_4646_ = lean_array_get_size(v_a_4645_);
v___x_4647_ = lean_nat_dec_lt(v___x_4633_, v___x_4646_);
if (v___x_4647_ == 0)
{
lean_object* v___x_4648_; lean_object* v___x_4649_; 
lean_dec(v_a_4645_);
lean_dec_ref(v_pkg_4616_);
v___x_4648_ = lean_box(0);
v___x_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
return v___x_4649_;
}
else
{
lean_object* v___x_4650_; size_t v___x_4651_; size_t v___x_4652_; lean_object* v___x_4653_; 
v___x_4650_ = lean_box(0);
v___x_4651_ = ((size_t)0ULL);
v___x_4652_ = lean_usize_of_nat(v___x_4646_);
v___x_4653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4645_, v___x_4651_, v___x_4652_, v___x_4650_, v___y_4622_);
lean_dec(v_a_4645_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4660_; 
lean_dec_ref(v_pkg_4616_);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4660_ == 0)
{
lean_object* v_unused_4661_; 
v_unused_4661_ = lean_ctor_get(v___x_4653_, 0);
lean_dec(v_unused_4661_);
v___x_4655_ = v___x_4653_;
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
else
{
lean_dec(v___x_4653_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4656_ == 0)
{
lean_ctor_set_tag(v___x_4655_, 1);
lean_ctor_set(v___x_4655_, 0, v___x_4650_);
v___x_4658_ = v___x_4655_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4650_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
else
{
v___y_4630_ = v___x_4653_;
goto v___jp_4629_;
}
}
}
}
else
{
lean_object* v___x_4662_; 
lean_dec_ref(v_pkg_4616_);
v___x_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4662_, 0, v_b_4620_);
return v___x_4662_;
}
v___jp_4624_:
{
size_t v___x_4626_; size_t v___x_4627_; 
v___x_4626_ = ((size_t)1ULL);
v___x_4627_ = lean_usize_add(v_i_4618_, v___x_4626_);
v_i_4618_ = v___x_4627_;
v_b_4620_ = v_a_4625_;
goto _start;
}
v___jp_4629_:
{
if (lean_obj_tag(v___y_4630_) == 0)
{
lean_object* v_a_4631_; 
v_a_4631_ = lean_ctor_get(v___y_4630_, 0);
lean_inc(v_a_4631_);
lean_dec_ref_known(v___y_4630_, 1);
v_a_4625_ = v_a_4631_;
goto v___jp_4624_;
}
else
{
lean_dec_ref(v_pkg_4616_);
return v___y_4630_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_4616_ = stack[0].m_obj;
lean_object* v_as_4617_ = stack[1].m_obj;
size_t v_i_4618_ = stack[2].m_num;
size_t v_stop_4619_ = stack[3].m_num;
lean_object* v_b_4620_ = stack[4].m_obj;
lean_object* v___y_4621_ = stack[5].m_obj;
lean_object* v___y_4622_ = stack[6].m_obj;
lean_object* v_res_4663_;
v_res_4663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4616_, v_as_4617_, v_i_4618_, v_stop_4619_, v_b_4620_, v___y_4621_, v___y_4622_);
stack->m_obj
 = v_res_4663_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4664_, lean_object* v_as_4665_, lean_object* v_i_4666_, lean_object* v_stop_4667_, lean_object* v_b_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
size_t v_i_boxed_4672_; size_t v_stop_boxed_4673_; lean_object* v_res_4674_; 
v_i_boxed_4672_ = lean_unbox_usize(v_i_4666_);
lean_dec(v_i_4666_);
v_stop_boxed_4673_ = lean_unbox_usize(v_stop_4667_);
lean_dec(v_stop_4667_);
v_res_4674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4664_, v_as_4665_, v_i_boxed_4672_, v_stop_boxed_4673_, v_b_4668_, v___y_4669_, v___y_4670_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v_as_4665_);
return v_res_4674_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
lean_object* v_baseName_4680_; lean_object* v_postUpdateHooks_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; 
v_baseName_4680_ = lean_ctor_get(v_pkg_4676_, 1);
v_postUpdateHooks_4681_ = lean_ctor_get(v_pkg_4676_, 20);
lean_inc_ref(v_postUpdateHooks_4681_);
v___x_4682_ = lean_array_get_size(v_postUpdateHooks_4681_);
v___x_4683_ = lean_unsigned_to_nat(0u);
v___x_4684_ = lean_nat_dec_eq(v___x_4682_, v___x_4683_);
if (v___x_4684_ == 0)
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; 
lean_inc(v_baseName_4680_);
v___x_4685_ = l_Lean_Name_toString(v_baseName_4680_, v___x_4684_);
v___x_4686_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4687_ = lean_string_append(v___x_4685_, v___x_4686_);
v___x_4688_ = 1;
v___x_4689_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4689_, 0, v___x_4687_);
lean_ctor_set_uint8(v___x_4689_, sizeof(void*)*1, v___x_4688_);
lean_inc_ref(v_a_4678_);
v___x_4690_ = lean_apply_2(v_a_4678_, v___x_4689_, lean_box(0));
v___x_4691_ = lean_box(0);
v___x_4692_ = lean_nat_dec_lt(v___x_4683_, v___x_4682_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; 
lean_dec_ref(v_postUpdateHooks_4681_);
lean_dec_ref(v_pkg_4676_);
v___x_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4691_);
return v___x_4693_;
}
else
{
uint8_t v___x_4694_; 
v___x_4694_ = lean_nat_dec_le(v___x_4682_, v___x_4682_);
if (v___x_4694_ == 0)
{
if (v___x_4692_ == 0)
{
lean_object* v___x_4695_; 
lean_dec_ref(v_postUpdateHooks_4681_);
lean_dec_ref(v_pkg_4676_);
v___x_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4691_);
return v___x_4695_;
}
else
{
size_t v___x_4696_; size_t v___x_4697_; lean_object* v___x_4698_; 
v___x_4696_ = ((size_t)0ULL);
v___x_4697_ = lean_usize_of_nat(v___x_4682_);
v___x_4698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4676_, v_postUpdateHooks_4681_, v___x_4696_, v___x_4697_, v___x_4691_, v_a_4677_, v_a_4678_);
lean_dec_ref(v_postUpdateHooks_4681_);
return v___x_4698_;
}
}
else
{
size_t v___x_4699_; size_t v___x_4700_; lean_object* v___x_4701_; 
v___x_4699_ = ((size_t)0ULL);
v___x_4700_ = lean_usize_of_nat(v___x_4682_);
v___x_4701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4676_, v_postUpdateHooks_4681_, v___x_4699_, v___x_4700_, v___x_4691_, v_a_4677_, v_a_4678_);
lean_dec_ref(v_postUpdateHooks_4681_);
return v___x_4701_;
}
}
}
else
{
lean_object* v___x_4702_; lean_object* v___x_4703_; 
lean_dec_ref(v_postUpdateHooks_4681_);
lean_dec_ref(v_pkg_4676_);
v___x_4702_ = lean_box(0);
v___x_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4702_);
return v___x_4703_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_4676_ = stack[0].m_obj;
lean_object* v_a_4677_ = stack[1].m_obj;
lean_object* v_a_4678_ = stack[2].m_obj;
lean_object* v_res_4704_;
v_res_4704_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4676_, v_a_4677_, v_a_4678_);
stack->m_obj
 = v_res_4704_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4705_, v_a_4706_, v_a_4707_);
lean_dec_ref(v_a_4707_);
lean_dec(v_a_4706_);
return v_res_4709_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4710_, lean_object* v_ws_4711_, lean_object* v_toUpdate_4712_, lean_object* v_leanOpts_4713_, uint8_t v_updateToolchain_4714_){
_start:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4716_ = lean_box(1);
v___x_4717_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4710_, v_ws_4711_, v_toUpdate_4712_, v___x_4716_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_object* v_a_4718_; lean_object* v_snd_4719_; uint8_t v___x_4720_; 
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
lean_inc(v_a_4718_);
lean_dec_ref_known(v___x_4717_, 1);
v_snd_4719_ = lean_ctor_get(v_a_4718_, 1);
lean_inc(v_snd_4719_);
lean_dec(v_a_4718_);
v___x_4720_ = 1;
if (v_updateToolchain_4714_ == 0)
{
lean_object* v_packages_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v_wsIdx_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; 
v_packages_4721_ = lean_ctor_get(v_ws_4711_, 4);
v___x_4722_ = lean_unsigned_to_nat(0u);
v___x_4723_ = lean_array_fget_borrowed(v_packages_4721_, v___x_4722_);
v_wsIdx_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_wsIdx_4724_);
v___x_4725_ = lean_array_get_size(v_packages_4721_);
v___x_4726_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4713_, v___x_4720_, v_ws_4711_, v_wsIdx_4724_, v___x_4725_, v_snd_4719_, v_a_4710_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4744_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4729_ = v___x_4726_;
v_isShared_4730_ = v_isSharedCheck_4744_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4726_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4744_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v_fst_4731_; lean_object* v_snd_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4743_; 
v_fst_4731_ = lean_ctor_get(v_a_4727_, 0);
v_snd_4732_ = lean_ctor_get(v_a_4727_, 1);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_a_4727_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4734_ = v_a_4727_;
v_isShared_4735_ = v_isSharedCheck_4743_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_snd_4732_);
lean_inc(v_fst_4731_);
lean_dec(v_a_4727_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4743_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4736_; lean_object* v___x_4738_; 
v___x_4736_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4731_);
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 0, v___x_4736_);
v___x_4738_ = v___x_4734_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4736_);
lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_snd_4732_);
v___x_4738_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
lean_object* v___x_4740_; 
if (v_isShared_4730_ == 0)
{
lean_ctor_set(v___x_4729_, 0, v___x_4738_);
v___x_4740_ = v___x_4729_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4738_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
}
else
{
return v___x_4726_;
}
}
else
{
lean_object* v_packages_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v_depConfigs_4748_; lean_object* v___x_4749_; lean_object* v___f_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v_packages_4745_ = lean_ctor_get(v_ws_4711_, 4);
v___x_4746_ = lean_unsigned_to_nat(0u);
v___x_4747_ = lean_array_fget_borrowed(v_packages_4745_, v___x_4746_);
v_depConfigs_4748_ = lean_ctor_get(v___x_4747_, 12);
v___x_4749_ = lean_box(v_updateToolchain_4714_);
lean_inc_ref(v_ws_4711_);
lean_inc(v___x_4747_);
v___f_4750_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4750_, 0, v___x_4747_);
lean_closure_set(v___f_4750_, 1, v___x_4749_);
lean_closure_set(v___f_4750_, 2, v_ws_4711_);
v___x_4751_ = lean_array_get_size(v_depConfigs_4748_);
lean_inc_ref(v_depConfigs_4748_);
v___x_4752_ = l_Array_reverse___redArg(v_depConfigs_4748_);
v___x_4753_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4754_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4751_, v___f_4750_, v___x_4752_, v___x_4746_, v___x_4753_, v_snd_4719_, v_a_4710_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; lean_object* v_fst_4756_; lean_object* v_snd_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4829_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
lean_inc(v_a_4755_);
lean_dec_ref_known(v___x_4754_, 1);
v_fst_4756_ = lean_ctor_get(v_a_4755_, 0);
v_snd_4757_ = lean_ctor_get(v_a_4755_, 1);
v_isSharedCheck_4829_ = !lean_is_exclusive(v_a_4755_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4759_ = v_a_4755_;
v_isShared_4760_ = v_isSharedCheck_4829_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_snd_4757_);
lean_inc(v_fst_4756_);
lean_dec(v_a_4755_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4829_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4761_; 
lean_inc_ref(v_ws_4711_);
v___x_4761_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4710_, v_ws_4711_, v_fst_4756_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v___x_4762_; lean_object* v___x_4763_; 
lean_dec_ref_known(v___x_4761_, 1);
v___x_4762_ = lean_array_get_size(v_packages_4745_);
lean_inc_ref(v_leanOpts_4713_);
v___x_4763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4751_, v_fst_4756_, v___x_4752_, v_leanOpts_4713_, v___x_4746_, v_ws_4711_, v_snd_4757_, v_a_4710_);
lean_dec_ref(v___x_4752_);
lean_dec(v_fst_4756_);
if (lean_obj_tag(v___x_4763_) == 0)
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4812_; 
v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4766_ = v___x_4763_;
v_isShared_4767_ = v_isSharedCheck_4812_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4763_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4812_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v_fst_4768_; lean_object* v_snd_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4811_; 
v_fst_4768_ = lean_ctor_get(v_a_4764_, 0);
v_snd_4769_ = lean_ctor_get(v_a_4764_, 1);
v_isSharedCheck_4811_ = !lean_is_exclusive(v_a_4764_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4771_ = v_a_4764_;
v_isShared_4772_ = v_isSharedCheck_4811_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_snd_4769_);
lean_inc(v_fst_4768_);
lean_dec(v_a_4764_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4811_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v_packages_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4778_; 
v_packages_4773_ = lean_ctor_get(v_fst_4768_, 4);
v___x_4774_ = lean_array_get_size(v_packages_4773_);
v___x_4775_ = lean_array_fget(v_packages_4773_, v___x_4746_);
v___x_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4762_);
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 1, v___x_4774_);
lean_ctor_set(v___x_4759_, 0, v___x_4776_);
v___x_4778_ = v___x_4759_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4776_);
lean_ctor_set(v_reuseFailAlloc_4810_, 1, v___x_4774_);
v___x_4778_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; uint8_t v___x_4781_; 
v___x_4779_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4778_, v___x_4753_);
v___x_4780_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4768_, v___x_4775_, v___x_4779_);
v___x_4781_ = lean_nat_dec_eq(v___x_4762_, v___x_4774_);
if (v___x_4781_ == 0)
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
lean_del_object(v___x_4771_);
lean_del_object(v___x_4766_);
v___x_4782_ = lean_unsigned_to_nat(1u);
v___x_4783_ = lean_nat_add(v___x_4762_, v___x_4782_);
v___x_4784_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4713_, v___x_4720_, v___x_4780_, v___x_4762_, v___x_4783_, v_snd_4769_, v_a_4710_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4802_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4787_ = v___x_4784_;
v_isShared_4788_ = v_isSharedCheck_4802_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4784_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4802_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v_fst_4789_; lean_object* v_snd_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4801_; 
v_fst_4789_ = lean_ctor_get(v_a_4785_, 0);
v_snd_4790_ = lean_ctor_get(v_a_4785_, 1);
v_isSharedCheck_4801_ = !lean_is_exclusive(v_a_4785_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4792_ = v_a_4785_;
v_isShared_4793_ = v_isSharedCheck_4801_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_snd_4790_);
lean_inc(v_fst_4789_);
lean_dec(v_a_4785_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4801_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4796_; 
v___x_4794_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4789_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 0, v___x_4794_);
v___x_4796_ = v___x_4792_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4794_);
lean_ctor_set(v_reuseFailAlloc_4800_, 1, v_snd_4790_);
v___x_4796_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
lean_object* v___x_4798_; 
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v___x_4796_);
v___x_4798_ = v___x_4787_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4796_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
}
else
{
return v___x_4784_;
}
}
else
{
lean_object* v___x_4803_; lean_object* v___x_4805_; 
lean_dec_ref(v_leanOpts_4713_);
v___x_4803_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4780_);
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 0, v___x_4803_);
v___x_4805_ = v___x_4771_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4803_);
lean_ctor_set(v_reuseFailAlloc_4809_, 1, v_snd_4769_);
v___x_4805_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
lean_object* v___x_4807_; 
if (v_isShared_4767_ == 0)
{
lean_ctor_set(v___x_4766_, 0, v___x_4805_);
v___x_4807_ = v___x_4766_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4805_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
lean_del_object(v___x_4759_);
lean_dec_ref(v_leanOpts_4713_);
v_a_4813_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___x_4763_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4763_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_del_object(v___x_4759_);
lean_dec(v_snd_4757_);
lean_dec(v_fst_4756_);
lean_dec_ref(v___x_4752_);
lean_dec_ref(v_leanOpts_4713_);
lean_dec_ref(v_ws_4711_);
v_a_4821_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4761_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4761_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
lean_dec_ref(v___x_4752_);
lean_dec_ref(v_leanOpts_4713_);
lean_dec_ref(v_ws_4711_);
v_a_4830_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4754_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4754_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4835_; 
if (v_isShared_4833_ == 0)
{
v___x_4835_ = v___x_4832_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
}
else
{
lean_object* v_a_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4845_; 
lean_dec_ref(v_leanOpts_4713_);
lean_dec_ref(v_ws_4711_);
v_a_4838_ = lean_ctor_get(v___x_4717_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4840_ = v___x_4717_;
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_a_4838_);
lean_dec(v___x_4717_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4843_; 
if (v_isShared_4841_ == 0)
{
v___x_4843_ = v___x_4840_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v_a_4838_);
v___x_4843_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
return v___x_4843_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4710_ = stack[0].m_obj;
lean_object* v_ws_4711_ = stack[1].m_obj;
lean_object* v_toUpdate_4712_ = stack[2].m_obj;
lean_object* v_leanOpts_4713_ = stack[3].m_obj;
uint8_t v_updateToolchain_4714_ = stack[4].m_num;
lean_object* v_res_4846_;
v_res_4846_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4710_, v_ws_4711_, v_toUpdate_4712_, v_leanOpts_4713_, v_updateToolchain_4714_);
stack->m_obj
 = v_res_4846_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4847_, lean_object* v_ws_4848_, lean_object* v_toUpdate_4849_, lean_object* v_leanOpts_4850_, lean_object* v_updateToolchain_4851_, lean_object* v_a_4852_){
_start:
{
uint8_t v_updateToolchain_boxed_4853_; lean_object* v_res_4854_; 
v_updateToolchain_boxed_4853_ = lean_unbox(v_updateToolchain_4851_);
v_res_4854_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4847_, v_ws_4848_, v_toUpdate_4849_, v_leanOpts_4850_, v_updateToolchain_boxed_4853_);
lean_dec_ref(v_a_4847_);
return v_res_4854_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4855_, size_t v_i_4856_, size_t v_stop_4857_, lean_object* v_b_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
uint8_t v___x_4862_; 
v___x_4862_ = lean_usize_dec_eq(v_i_4856_, v_stop_4857_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4863_ = lean_array_uget_borrowed(v_as_4855_, v_i_4856_);
lean_inc(v___x_4863_);
v___x_4864_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4863_, v___y_4859_, v___y_4860_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; size_t v___x_4866_; size_t v___x_4867_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc(v_a_4865_);
lean_dec_ref_known(v___x_4864_, 1);
v___x_4866_ = ((size_t)1ULL);
v___x_4867_ = lean_usize_add(v_i_4856_, v___x_4866_);
v_i_4856_ = v___x_4867_;
v_b_4858_ = v_a_4865_;
goto _start;
}
else
{
return v___x_4864_;
}
}
else
{
lean_object* v___x_4869_; 
v___x_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4869_, 0, v_b_4858_);
return v___x_4869_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4855_ = stack[0].m_obj;
size_t v_i_4856_ = stack[1].m_num;
size_t v_stop_4857_ = stack[2].m_num;
lean_object* v_b_4858_ = stack[3].m_obj;
lean_object* v___y_4859_ = stack[4].m_obj;
lean_object* v___y_4860_ = stack[5].m_obj;
lean_object* v_res_4870_;
v_res_4870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4855_, v_i_4856_, v_stop_4857_, v_b_4858_, v___y_4859_, v___y_4860_);
stack->m_obj
 = v_res_4870_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4871_, lean_object* v_i_4872_, lean_object* v_stop_4873_, lean_object* v_b_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
size_t v_i_boxed_4878_; size_t v_stop_boxed_4879_; lean_object* v_res_4880_; 
v_i_boxed_4878_ = lean_unbox_usize(v_i_4872_);
lean_dec(v_i_4872_);
v_stop_boxed_4879_ = lean_unbox_usize(v_stop_4873_);
lean_dec(v_stop_4873_);
v_res_4880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4871_, v_i_boxed_4878_, v_stop_boxed_4879_, v_b_4874_, v___y_4875_, v___y_4876_);
lean_dec_ref(v___y_4876_);
lean_dec(v___y_4875_);
lean_dec_ref(v_as_4871_);
return v_res_4880_;
}
}
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4881_, lean_object* v_toUpdate_4882_, lean_object* v_leanOpts_4883_, uint8_t v_updateToolchain_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4885_, v_ws_4881_, v_toUpdate_4882_, v_leanOpts_4883_, v_updateToolchain_4884_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v_fst_4889_; lean_object* v_snd_4890_; lean_object* v___y_4892_; lean_object* v___x_4909_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref_known(v___x_4887_, 1);
v_fst_4889_ = lean_ctor_get(v_a_4888_, 0);
lean_inc(v_fst_4889_);
v_snd_4890_ = lean_ctor_get(v_a_4888_, 1);
lean_inc(v_snd_4890_);
lean_dec(v_a_4888_);
v___x_4909_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4889_, v_snd_4890_);
lean_dec(v_snd_4890_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4931_; 
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4931_ == 0)
{
lean_object* v_unused_4932_; 
v_unused_4932_ = lean_ctor_get(v___x_4909_, 0);
lean_dec(v_unused_4932_);
v___x_4911_ = v___x_4909_;
v_isShared_4912_ = v_isSharedCheck_4931_;
goto v_resetjp_4910_;
}
else
{
lean_dec(v___x_4909_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4931_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v_packages_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; uint8_t v___x_4916_; 
v_packages_4913_ = lean_ctor_get(v_fst_4889_, 4);
v___x_4914_ = lean_unsigned_to_nat(0u);
v___x_4915_ = lean_array_get_size(v_packages_4913_);
v___x_4916_ = lean_nat_dec_lt(v___x_4914_, v___x_4915_);
if (v___x_4916_ == 0)
{
lean_object* v___x_4918_; 
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 0, v_fst_4889_);
v___x_4918_ = v___x_4911_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_fst_4889_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
else
{
lean_object* v___x_4920_; uint8_t v___x_4921_; 
v___x_4920_ = lean_box(0);
v___x_4921_ = lean_nat_dec_le(v___x_4915_, v___x_4915_);
if (v___x_4921_ == 0)
{
if (v___x_4916_ == 0)
{
lean_object* v___x_4923_; 
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 0, v_fst_4889_);
v___x_4923_ = v___x_4911_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_fst_4889_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
else
{
size_t v___x_4925_; size_t v___x_4926_; lean_object* v___x_4927_; 
lean_del_object(v___x_4911_);
v___x_4925_ = ((size_t)0ULL);
v___x_4926_ = lean_usize_of_nat(v___x_4915_);
v___x_4927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4913_, v___x_4925_, v___x_4926_, v___x_4920_, v_fst_4889_, v_a_4885_);
v___y_4892_ = v___x_4927_;
goto v___jp_4891_;
}
}
else
{
size_t v___x_4928_; size_t v___x_4929_; lean_object* v___x_4930_; 
lean_del_object(v___x_4911_);
v___x_4928_ = ((size_t)0ULL);
v___x_4929_ = lean_usize_of_nat(v___x_4915_);
v___x_4930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4913_, v___x_4928_, v___x_4929_, v___x_4920_, v_fst_4889_, v_a_4885_);
v___y_4892_ = v___x_4930_;
goto v___jp_4891_;
}
}
}
}
else
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4945_; 
lean_dec(v_fst_4889_);
v_a_4933_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4935_ = v___x_4909_;
v_isShared_4936_ = v_isSharedCheck_4945_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___x_4909_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4945_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4937_; uint8_t v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4943_; 
v___x_4937_ = lean_io_error_to_string(v_a_4933_);
v___x_4938_ = 3;
v___x_4939_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4939_, 0, v___x_4937_);
lean_ctor_set_uint8(v___x_4939_, sizeof(void*)*1, v___x_4938_);
lean_inc_ref(v_a_4885_);
v___x_4940_ = lean_apply_2(v_a_4885_, v___x_4939_, lean_box(0));
v___x_4941_ = lean_box(0);
if (v_isShared_4936_ == 0)
{
lean_ctor_set(v___x_4935_, 0, v___x_4941_);
v___x_4943_ = v___x_4935_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4941_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
v___jp_4891_:
{
if (lean_obj_tag(v___y_4892_) == 0)
{
lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
v_isSharedCheck_4899_ = !lean_is_exclusive(v___y_4892_);
if (v_isSharedCheck_4899_ == 0)
{
lean_object* v_unused_4900_; 
v_unused_4900_ = lean_ctor_get(v___y_4892_, 0);
lean_dec(v_unused_4900_);
v___x_4894_ = v___y_4892_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_dec(v___y_4892_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v_fst_4889_);
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_fst_4889_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
else
{
lean_object* v_a_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4908_; 
lean_dec(v_fst_4889_);
v_a_4901_ = lean_ctor_get(v___y_4892_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___y_4892_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4903_ = v___y_4892_;
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_a_4901_);
lean_dec(v___y_4892_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4906_; 
if (v_isShared_4904_ == 0)
{
v___x_4906_ = v___x_4903_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4901_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
}
}
}
else
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4953_; 
v_a_4946_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4948_ = v___x_4887_;
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4887_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4951_; 
if (v_isShared_4949_ == 0)
{
v___x_4951_ = v___x_4948_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4946_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Workspace_updateAndMaterialize_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_4881_ = stack[0].m_obj;
lean_object* v_toUpdate_4882_ = stack[1].m_obj;
lean_object* v_leanOpts_4883_ = stack[2].m_obj;
uint8_t v_updateToolchain_4884_ = stack[3].m_num;
lean_object* v_a_4885_ = stack[4].m_obj;
lean_object* v_res_4954_;
v_res_4954_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4881_, v_toUpdate_4882_, v_leanOpts_4883_, v_updateToolchain_4884_, v_a_4885_);
stack->m_obj
 = v_res_4954_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4955_, lean_object* v_toUpdate_4956_, lean_object* v_leanOpts_4957_, lean_object* v_updateToolchain_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_){
_start:
{
uint8_t v_updateToolchain_boxed_4961_; lean_object* v_res_4962_; 
v_updateToolchain_boxed_4961_ = lean_unbox(v_updateToolchain_4958_);
v_res_4962_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4955_, v_toUpdate_4956_, v_leanOpts_4957_, v_updateToolchain_boxed_4961_, v_a_4959_);
lean_dec_ref(v_a_4959_);
return v_res_4962_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_4967_, lean_object* v_what_4968_, lean_object* v___y_4969_){
_start:
{
lean_object* v_name_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; uint8_t v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; uint8_t v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; 
v_name_4971_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_name_4971_);
lean_dec_ref(v___x_4967_);
v___x_4972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_4973_ = lean_string_append(v___x_4972_, v_what_4968_);
v___x_4974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_4975_ = lean_string_append(v___x_4973_, v___x_4974_);
v___x_4976_ = 1;
v___x_4977_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4971_, v___x_4976_);
v___x_4978_ = lean_string_append(v___x_4975_, v___x_4977_);
v___x_4979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_4980_ = lean_string_append(v___x_4978_, v___x_4979_);
v___x_4981_ = lean_string_append(v___x_4980_, v___x_4977_);
lean_dec_ref(v___x_4977_);
v___x_4982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_4983_ = lean_string_append(v___x_4981_, v___x_4982_);
v___x_4984_ = 2;
v___x_4985_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4985_, 0, v___x_4983_);
lean_ctor_set_uint8(v___x_4985_, sizeof(void*)*1, v___x_4984_);
lean_inc_ref(v___y_4969_);
v___x_4986_ = lean_apply_2(v___y_4969_, v___x_4985_, lean_box(0));
v___x_4987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
return v___x_4987_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4967_ = stack[0].m_obj;
lean_object* v_what_4968_ = stack[1].m_obj;
lean_object* v___y_4969_ = stack[2].m_obj;
lean_object* v_res_4988_;
v_res_4988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4967_, v_what_4968_, v___y_4969_);
stack->m_obj
 = v_res_4988_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_4989_, lean_object* v_what_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4989_, v_what_4990_, v___y_4991_);
lean_dec_ref(v___y_4991_);
lean_dec_ref(v_what_4990_);
return v_res_4993_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_4997_, lean_object* v_as_4998_, size_t v_i_4999_, size_t v_stop_5000_, lean_object* v_b_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v_a_5005_; lean_object* v___y_5010_; uint8_t v___x_5012_; 
v___x_5012_ = lean_usize_dec_eq(v_i_4999_, v_stop_5000_);
if (v___x_5012_ == 0)
{
lean_object* v___x_5013_; lean_object* v_src_x3f_5014_; 
v___x_5013_ = lean_array_uget_borrowed(v_as_4998_, v_i_4999_);
v_src_x3f_5014_ = lean_ctor_get(v___x_5013_, 3);
if (lean_obj_tag(v_src_x3f_5014_) == 1)
{
lean_object* v_name_5015_; lean_object* v_val_5016_; lean_object* v___x_5017_; 
v_name_5015_ = lean_ctor_get(v___x_5013_, 0);
v_val_5016_ = lean_ctor_get(v_src_x3f_5014_, 0);
v___x_5017_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_4997_, v_name_5015_);
if (lean_obj_tag(v___x_5017_) == 1)
{
lean_object* v_val_5018_; lean_object* v___y_5020_; lean_object* v___y_5024_; 
v_val_5018_ = lean_ctor_get(v___x_5017_, 0);
lean_inc(v_val_5018_);
lean_dec_ref_known(v___x_5017_, 1);
if (lean_obj_tag(v_val_5016_) == 0)
{
lean_object* v_src_5027_; 
v_src_5027_ = lean_ctor_get(v_val_5018_, 4);
lean_inc_ref(v_src_5027_);
lean_dec(v_val_5018_);
if (lean_obj_tag(v_src_5027_) == 0)
{
lean_object* v___x_5028_; 
lean_dec_ref_known(v_src_5027_, 1);
v___x_5028_ = lean_box(0);
v_a_5005_ = v___x_5028_;
goto v___jp_5004_;
}
else
{
lean_dec_ref(v_src_5027_);
v___y_5024_ = v___y_5002_;
goto v___jp_5023_;
}
}
else
{
lean_object* v_src_5029_; 
v_src_5029_ = lean_ctor_get(v_val_5018_, 4);
lean_inc_ref(v_src_5029_);
lean_dec(v_val_5018_);
if (lean_obj_tag(v_src_5029_) == 1)
{
lean_object* v_url_5030_; lean_object* v_rev_5031_; lean_object* v_url_5032_; lean_object* v_inputRev_x3f_5033_; lean_object* v___y_5035_; uint8_t v___x_5042_; 
v_url_5030_ = lean_ctor_get(v_val_5016_, 0);
v_rev_5031_ = lean_ctor_get(v_val_5016_, 1);
v_url_5032_ = lean_ctor_get(v_src_5029_, 0);
lean_inc_ref(v_url_5032_);
v_inputRev_x3f_5033_ = lean_ctor_get(v_src_5029_, 2);
lean_inc(v_inputRev_x3f_5033_);
lean_dec_ref_known(v_src_5029_, 4);
v___x_5042_ = lean_string_dec_eq(v_url_5030_, v_url_5032_);
lean_dec_ref(v_url_5032_);
if (v___x_5042_ == 0)
{
goto v___jp_5039_;
}
else
{
if (v___x_5012_ == 0)
{
v___y_5035_ = v___y_5002_;
goto v___jp_5034_;
}
else
{
goto v___jp_5039_;
}
}
v___jp_5034_:
{
lean_object* v___x_5036_; uint8_t v___x_5037_; 
v___x_5036_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_5031_);
v___x_5037_ = l_Option_instDecidableEq___redArg(v___x_5036_, v_rev_5031_, v_inputRev_x3f_5033_);
if (v___x_5037_ == 0)
{
v___y_5020_ = v___y_5035_;
goto v___jp_5019_;
}
else
{
if (v___x_5012_ == 0)
{
lean_object* v___x_5038_; 
v___x_5038_ = lean_box(0);
v_a_5005_ = v___x_5038_;
goto v___jp_5004_;
}
else
{
v___y_5020_ = v___y_5035_;
goto v___jp_5019_;
}
}
}
v___jp_5039_:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_5013_);
v___x_5041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5013_, v___x_5040_, v___y_5002_);
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_dec_ref_known(v___x_5041_, 1);
v___y_5035_ = v___y_5002_;
goto v___jp_5034_;
}
else
{
lean_dec(v_inputRev_x3f_5033_);
return v___x_5041_;
}
}
}
else
{
lean_dec_ref(v_src_5029_);
v___y_5024_ = v___y_5002_;
goto v___jp_5023_;
}
}
v___jp_5019_:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_5013_);
v___x_5022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5013_, v___x_5021_, v___y_5020_);
v___y_5010_ = v___x_5022_;
goto v___jp_5009_;
}
v___jp_5023_:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_5013_);
v___x_5026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5013_, v___x_5025_, v___y_5024_);
v___y_5010_ = v___x_5026_;
goto v___jp_5009_;
}
}
else
{
lean_object* v___x_5043_; 
lean_dec(v___x_5017_);
v___x_5043_ = lean_box(0);
v_a_5005_ = v___x_5043_;
goto v___jp_5004_;
}
}
else
{
lean_object* v___x_5044_; 
v___x_5044_ = lean_box(0);
v_a_5005_ = v___x_5044_;
goto v___jp_5004_;
}
}
else
{
lean_object* v___x_5045_; 
v___x_5045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5045_, 0, v_b_5001_);
return v___x_5045_;
}
v___jp_5004_:
{
size_t v___x_5006_; size_t v___x_5007_; 
v___x_5006_ = ((size_t)1ULL);
v___x_5007_ = lean_usize_add(v_i_4999_, v___x_5006_);
v_i_4999_ = v___x_5007_;
v_b_5001_ = v_a_5005_;
goto _start;
}
v___jp_5009_:
{
if (lean_obj_tag(v___y_5010_) == 0)
{
lean_object* v_a_5011_; 
v_a_5011_ = lean_ctor_get(v___y_5010_, 0);
lean_inc(v_a_5011_);
lean_dec_ref_known(v___y_5010_, 1);
v_a_5005_ = v_a_5011_;
goto v___jp_5004_;
}
else
{
return v___y_5010_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkgEntries_4997_ = stack[0].m_obj;
lean_object* v_as_4998_ = stack[1].m_obj;
size_t v_i_4999_ = stack[2].m_num;
size_t v_stop_5000_ = stack[3].m_num;
lean_object* v_b_5001_ = stack[4].m_obj;
lean_object* v___y_5002_ = stack[5].m_obj;
lean_object* v_res_5046_;
v_res_5046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4997_, v_as_4998_, v_i_4999_, v_stop_5000_, v_b_5001_, v___y_5002_);
stack->m_obj
 = v_res_5046_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_5047_, lean_object* v_as_5048_, lean_object* v_i_5049_, lean_object* v_stop_5050_, lean_object* v_b_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
size_t v_i_boxed_5054_; size_t v_stop_boxed_5055_; lean_object* v_res_5056_; 
v_i_boxed_5054_ = lean_unbox_usize(v_i_5049_);
lean_dec(v_i_5049_);
v_stop_boxed_5055_ = lean_unbox_usize(v_stop_5050_);
lean_dec(v_stop_5050_);
v_res_5056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5047_, v_as_5048_, v_i_boxed_5054_, v_stop_boxed_5055_, v_b_5051_, v___y_5052_);
lean_dec_ref(v___y_5052_);
lean_dec_ref(v_as_5048_);
lean_dec(v_pkgEntries_5047_);
return v_res_5056_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_5057_, lean_object* v_deps_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; uint8_t v___x_5064_; 
v___x_5061_ = lean_unsigned_to_nat(0u);
v___x_5062_ = lean_array_get_size(v_deps_5058_);
v___x_5063_ = lean_box(0);
v___x_5064_ = lean_nat_dec_lt(v___x_5061_, v___x_5062_);
if (v___x_5064_ == 0)
{
lean_object* v___x_5065_; 
v___x_5065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5063_);
return v___x_5065_;
}
else
{
uint8_t v___x_5066_; 
v___x_5066_ = lean_nat_dec_le(v___x_5062_, v___x_5062_);
if (v___x_5066_ == 0)
{
if (v___x_5064_ == 0)
{
lean_object* v___x_5067_; 
v___x_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5063_);
return v___x_5067_;
}
else
{
size_t v___x_5068_; size_t v___x_5069_; lean_object* v___x_5070_; 
v___x_5068_ = ((size_t)0ULL);
v___x_5069_ = lean_usize_of_nat(v___x_5062_);
v___x_5070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5057_, v_deps_5058_, v___x_5068_, v___x_5069_, v___x_5063_, v_a_5059_);
return v___x_5070_;
}
}
else
{
size_t v___x_5071_; size_t v___x_5072_; lean_object* v___x_5073_; 
v___x_5071_ = ((size_t)0ULL);
v___x_5072_ = lean_usize_of_nat(v___x_5062_);
v___x_5073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5057_, v_deps_5058_, v___x_5071_, v___x_5072_, v___x_5063_, v_a_5059_);
return v___x_5073_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_validateManifest_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkgEntries_5057_ = stack[0].m_obj;
lean_object* v_deps_5058_ = stack[1].m_obj;
lean_object* v_a_5059_ = stack[2].m_obj;
lean_object* v_res_5074_;
v_res_5074_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_5057_, v_deps_5058_, v_a_5059_);
stack->m_obj
 = v_res_5074_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_5075_, lean_object* v_deps_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_){
_start:
{
lean_object* v_res_5079_; 
v_res_5079_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_5075_, v_deps_5076_, v_a_5077_);
lean_dec_ref(v_a_5077_);
lean_dec_ref(v_deps_5076_);
lean_dec(v_pkgEntries_5075_);
return v_res_5079_;
}
}
uint8_t l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_5080_, lean_object* v_x_5081_){
_start:
{
if (lean_obj_tag(v_x_5080_) == 0)
{
if (lean_obj_tag(v_x_5081_) == 0)
{
uint8_t v___x_5082_; 
v___x_5082_ = 1;
return v___x_5082_;
}
else
{
uint8_t v___x_5083_; 
v___x_5083_ = 0;
return v___x_5083_;
}
}
else
{
if (lean_obj_tag(v_x_5081_) == 0)
{
uint8_t v___x_5084_; 
v___x_5084_ = 0;
return v___x_5084_;
}
else
{
lean_object* v_val_5085_; lean_object* v_val_5086_; uint8_t v___x_5087_; 
v_val_5085_ = lean_ctor_get(v_x_5080_, 0);
v_val_5086_ = lean_ctor_get(v_x_5081_, 0);
v___x_5087_ = lean_string_dec_eq(v_val_5085_, v_val_5086_);
return v___x_5087_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5080_ = stack[0].m_obj;
lean_object* v_x_5081_ = stack[1].m_obj;
uint8_t v_res_5088_;
v_res_5088_ = l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_5080_, v_x_5081_);
stack->m_num = v_res_5088_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_5089_, lean_object* v_x_5090_){
_start:
{
uint8_t v_res_5091_; lean_object* v_r_5092_; 
v_res_5091_ = l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_5089_, v_x_5090_);
lean_dec(v_x_5090_);
lean_dec(v_x_5089_);
v_r_5092_ = lean_box(v_res_5091_);
return v_r_5092_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_pkg_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v_leanOpts_5101_, uint8_t v_reconfigure_5102_, lean_object* v_as_5103_, size_t v_i_5104_, size_t v_stop_5105_, lean_object* v_b_5106_, lean_object* v___y_5107_){
_start:
{
uint8_t v___x_5109_; 
v___x_5109_ = lean_usize_dec_eq(v_i_5104_, v_stop_5105_);
if (v___x_5109_ == 0)
{
lean_object* v_ws_5110_; lean_object* v_depIdxs_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5241_; 
v_ws_5110_ = lean_ctor_get(v_b_5106_, 0);
v_depIdxs_5111_ = lean_ctor_get(v_b_5106_, 1);
v_isSharedCheck_5241_ = !lean_is_exclusive(v_b_5106_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5113_ = v_b_5106_;
v_isShared_5114_ = v_isSharedCheck_5241_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_depIdxs_5111_);
lean_inc(v_ws_5110_);
lean_dec(v_b_5106_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5241_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v_lakeEnv_5115_; lean_object* v_packages_5116_; size_t v___x_5117_; size_t v___x_5118_; lean_object* v___x_5119_; lean_object* v___f_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v_lakeEnv_5115_ = lean_ctor_get(v_ws_5110_, 0);
v_packages_5116_ = lean_ctor_get(v_ws_5110_, 4);
v___x_5117_ = ((size_t)1ULL);
v___x_5118_ = lean_usize_sub(v_i_5104_, v___x_5117_);
v___x_5119_ = lean_array_uget_borrowed(v_as_5103_, v___x_5118_);
lean_inc(v___x_5119_);
v___f_5120_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5120_, 0, v___x_5119_);
v___x_5121_ = lean_unsigned_to_nat(0u);
v___x_5122_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5120_, v_packages_5116_, v___x_5121_);
if (lean_obj_tag(v___x_5122_) == 1)
{
lean_object* v_val_5123_; lean_object* v___x_5124_; lean_object* v___x_5126_; 
v_val_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_val_5123_);
lean_dec_ref_known(v___x_5122_, 1);
v___x_5124_ = lean_array_push(v_depIdxs_5111_, v_val_5123_);
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 1, v___x_5124_);
v___x_5126_ = v___x_5113_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_ws_5110_);
lean_ctor_set(v_reuseFailAlloc_5128_, 1, v___x_5124_);
v___x_5126_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
v_i_5104_ = v___x_5118_;
v_b_5106_ = v___x_5126_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_5129_; lean_object* v_baseName_5130_; lean_object* v_name_5131_; lean_object* v_opts_5132_; uint8_t v___x_5133_; 
lean_dec(v___x_5122_);
v_wsIdx_5129_ = lean_ctor_get(v_pkg_5098_, 0);
v_baseName_5130_ = lean_ctor_get(v_pkg_5098_, 1);
v_name_5131_ = lean_ctor_get(v___x_5119_, 0);
v_opts_5132_ = lean_ctor_get(v___x_5119_, 4);
v___x_5133_ = lean_name_eq(v_baseName_5130_, v_name_5131_);
if (v___x_5133_ == 0)
{
lean_object* v___x_5134_; 
v___x_5134_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5099_, v_name_5131_);
if (lean_obj_tag(v___x_5134_) == 1)
{
lean_object* v_val_5135_; lean_object* v___x_5136_; lean_object* v_dir_5137_; lean_object* v___x_5138_; 
v_val_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_val_5135_);
lean_dec_ref_known(v___x_5134_, 1);
v___x_5136_ = lean_array_fget_borrowed(v_packages_5116_, v___x_5121_);
v_dir_5137_ = lean_ctor_get(v___x_5136_, 4);
lean_inc_ref(v___y_5100_);
lean_inc_ref(v_dir_5137_);
v___x_5138_ = l_Lake_PackageEntry_materialize(v_val_5135_, v_lakeEnv_5115_, v_dir_5137_, v___y_5100_, v___y_5107_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v_a_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5195_; 
v_a_5139_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5141_ = v___x_5138_;
v_isShared_5142_ = v_isSharedCheck_5195_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v___x_5138_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5195_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5143_; lean_object* v_wsIdx_5144_; lean_object* v___x_5145_; 
v___x_5143_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_5144_ = lean_array_get_size(v_packages_5116_);
lean_inc_ref(v_leanOpts_5101_);
lean_inc(v_opts_5132_);
v___x_5145_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5110_, v_a_5139_, v_opts_5132_, v_leanOpts_5101_, v_reconfigure_5102_, v___x_5143_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; lean_object* v_a_5147_; lean_object* v___x_5148_; lean_object* v___x_5150_; 
lean_del_object(v___x_5141_);
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5146_);
v_a_5147_ = lean_ctor_get(v___x_5145_, 1);
lean_inc(v_a_5147_);
lean_dec_ref_known(v___x_5145_, 2);
v___x_5148_ = lean_array_push(v_depIdxs_5111_, v_wsIdx_5144_);
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 1, v___x_5148_);
lean_ctor_set(v___x_5113_, 0, v_a_5146_);
v___x_5150_ = v___x_5113_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5146_);
lean_ctor_set(v_reuseFailAlloc_5167_, 1, v___x_5148_);
v___x_5150_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
lean_object* v___x_5151_; uint8_t v___x_5152_; 
v___x_5151_ = lean_array_get_size(v_a_5147_);
v___x_5152_ = lean_nat_dec_lt(v___x_5121_, v___x_5151_);
if (v___x_5152_ == 0)
{
lean_dec(v_a_5147_);
v_i_5104_ = v___x_5118_;
v_b_5106_ = v___x_5150_;
goto _start;
}
else
{
lean_object* v___x_5154_; size_t v___x_5155_; size_t v___x_5156_; lean_object* v___x_5157_; 
v___x_5154_ = lean_box(0);
v___x_5155_ = ((size_t)0ULL);
v___x_5156_ = lean_usize_of_nat(v___x_5151_);
v___x_5157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5147_, v___x_5155_, v___x_5156_, v___x_5154_, v___y_5107_);
lean_dec(v_a_5147_);
if (lean_obj_tag(v___x_5157_) == 0)
{
lean_dec_ref_known(v___x_5157_, 1);
v_i_5104_ = v___x_5118_;
v_b_5106_ = v___x_5150_;
goto _start;
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
lean_dec_ref(v___x_5150_);
lean_dec_ref(v_leanOpts_5101_);
lean_dec_ref(v___y_5100_);
lean_dec_ref(v_pkg_5098_);
v_a_5159_ = lean_ctor_get(v___x_5157_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5157_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5157_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5157_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5162_ == 0)
{
v___x_5164_ = v___x_5161_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
}
}
else
{
lean_object* v_a_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; 
lean_del_object(v___x_5113_);
lean_dec_ref(v_depIdxs_5111_);
lean_dec_ref(v_leanOpts_5101_);
lean_dec_ref(v___y_5100_);
lean_dec_ref(v_pkg_5098_);
v_a_5168_ = lean_ctor_get(v___x_5145_, 1);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5145_, 2);
v___x_5169_ = lean_array_get_size(v_a_5168_);
v___x_5170_ = lean_nat_dec_lt(v___x_5121_, v___x_5169_);
if (v___x_5170_ == 0)
{
lean_object* v___x_5171_; lean_object* v___x_5173_; 
lean_dec(v_a_5168_);
v___x_5171_ = lean_box(0);
if (v_isShared_5142_ == 0)
{
lean_ctor_set_tag(v___x_5141_, 1);
lean_ctor_set(v___x_5141_, 0, v___x_5171_);
v___x_5173_ = v___x_5141_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5171_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
else
{
lean_object* v___x_5175_; size_t v___x_5176_; size_t v___x_5177_; lean_object* v___x_5178_; 
lean_del_object(v___x_5141_);
v___x_5175_ = lean_box(0);
v___x_5176_ = ((size_t)0ULL);
v___x_5177_ = lean_usize_of_nat(v___x_5169_);
v___x_5178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5168_, v___x_5176_, v___x_5177_, v___x_5175_, v___y_5107_);
lean_dec(v_a_5168_);
if (lean_obj_tag(v___x_5178_) == 0)
{
lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5185_ == 0)
{
lean_object* v_unused_5186_; 
v_unused_5186_ = lean_ctor_get(v___x_5178_, 0);
lean_dec(v_unused_5186_);
v___x_5180_ = v___x_5178_;
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
else
{
lean_dec(v___x_5178_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5183_; 
if (v_isShared_5181_ == 0)
{
lean_ctor_set_tag(v___x_5180_, 1);
lean_ctor_set(v___x_5180_, 0, v___x_5175_);
v___x_5183_ = v___x_5180_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5175_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
else
{
lean_object* v_a_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5194_; 
v_a_5187_ = lean_ctor_get(v___x_5178_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5189_ = v___x_5178_;
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_a_5187_);
lean_dec(v___x_5178_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5192_; 
if (v_isShared_5190_ == 0)
{
v___x_5192_ = v___x_5189_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
v___x_5192_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
return v___x_5192_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5203_; 
lean_del_object(v___x_5113_);
lean_dec_ref(v_depIdxs_5111_);
lean_dec_ref(v_ws_5110_);
lean_dec_ref(v_leanOpts_5101_);
lean_dec_ref(v___y_5100_);
lean_dec_ref(v_pkg_5098_);
v_a_5196_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5198_ = v___x_5138_;
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_a_5196_);
lean_dec(v___x_5138_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5201_; 
if (v_isShared_5199_ == 0)
{
v___x_5201_ = v___x_5198_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_a_5196_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
else
{
uint8_t v___x_5204_; 
lean_inc(v_baseName_5130_);
lean_inc(v_wsIdx_5129_);
lean_dec(v___x_5134_);
lean_del_object(v___x_5113_);
lean_dec_ref(v_depIdxs_5111_);
lean_dec_ref(v_ws_5110_);
lean_dec_ref(v_leanOpts_5101_);
lean_dec_ref(v___y_5100_);
lean_dec_ref(v_pkg_5098_);
v___x_5204_ = lean_nat_dec_eq(v_wsIdx_5129_, v___x_5121_);
lean_dec(v_wsIdx_5129_);
if (v___x_5204_ == 0)
{
lean_object* v___x_5205_; uint8_t v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; uint8_t v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; 
v___x_5205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5206_ = 1;
lean_inc(v_name_5131_);
v___x_5207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5131_, v___x_5206_);
v___x_5208_ = lean_string_append(v___x_5205_, v___x_5207_);
lean_dec_ref(v___x_5207_);
v___x_5209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5210_ = lean_string_append(v___x_5208_, v___x_5209_);
v___x_5211_ = l_Lean_Name_toString(v_baseName_5130_, v___x_5204_);
v___x_5212_ = lean_string_append(v___x_5210_, v___x_5211_);
lean_dec_ref(v___x_5211_);
v___x_5213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5214_ = lean_string_append(v___x_5212_, v___x_5213_);
v___x_5215_ = 3;
v___x_5216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5216_, 0, v___x_5214_);
lean_ctor_set_uint8(v___x_5216_, sizeof(void*)*1, v___x_5215_);
lean_inc_ref(v___y_5107_);
v___x_5217_ = lean_apply_2(v___y_5107_, v___x_5216_, lean_box(0));
v___x_5218_ = lean_box(0);
v___x_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5218_);
return v___x_5219_;
}
else
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; uint8_t v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; 
lean_dec(v_baseName_5130_);
v___x_5220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5131_);
v___x_5221_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5131_, v___x_5204_);
v___x_5222_ = lean_string_append(v___x_5220_, v___x_5221_);
v___x_5223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5224_ = lean_string_append(v___x_5222_, v___x_5223_);
v___x_5225_ = lean_string_append(v___x_5224_, v___x_5221_);
lean_dec_ref(v___x_5221_);
v___x_5226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5227_ = lean_string_append(v___x_5225_, v___x_5226_);
v___x_5228_ = 3;
v___x_5229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5229_, 0, v___x_5227_);
lean_ctor_set_uint8(v___x_5229_, sizeof(void*)*1, v___x_5228_);
lean_inc_ref(v___y_5107_);
v___x_5230_ = lean_apply_2(v___y_5107_, v___x_5229_, lean_box(0));
v___x_5231_ = lean_box(0);
v___x_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5231_);
return v___x_5232_;
}
}
}
else
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; uint8_t v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; 
lean_inc(v_baseName_5130_);
lean_del_object(v___x_5113_);
lean_dec_ref(v_depIdxs_5111_);
lean_dec_ref(v_ws_5110_);
lean_dec_ref(v_leanOpts_5101_);
lean_dec_ref(v___y_5100_);
lean_dec_ref(v_pkg_5098_);
v___x_5233_ = l_Lean_Name_toString(v_baseName_5130_, v___x_5109_);
v___x_5234_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5235_ = lean_string_append(v___x_5233_, v___x_5234_);
v___x_5236_ = 3;
v___x_5237_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5237_, 0, v___x_5235_);
lean_ctor_set_uint8(v___x_5237_, sizeof(void*)*1, v___x_5236_);
lean_inc_ref(v___y_5107_);
v___x_5238_ = lean_apply_2(v___y_5107_, v___x_5237_, lean_box(0));
v___x_5239_ = lean_box(0);
v___x_5240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5240_, 0, v___x_5239_);
return v___x_5240_;
}
}
}
}
else
{
lean_object* v___x_5242_; 
lean_dec_ref(v_leanOpts_5101_);
lean_dec_ref(v___y_5100_);
lean_dec_ref(v_pkg_5098_);
v___x_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5242_, 0, v_b_5106_);
return v___x_5242_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_5098_ = stack[0].m_obj;
lean_object* v___y_5099_ = stack[1].m_obj;
lean_object* v___y_5100_ = stack[2].m_obj;
lean_object* v_leanOpts_5101_ = stack[3].m_obj;
uint8_t v_reconfigure_5102_ = stack[4].m_num;
lean_object* v_as_5103_ = stack[5].m_obj;
size_t v_i_5104_ = stack[6].m_num;
size_t v_stop_5105_ = stack[7].m_num;
lean_object* v_b_5106_ = stack[8].m_obj;
lean_object* v___y_5107_ = stack[9].m_obj;
lean_object* v_res_5243_;
v_res_5243_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5098_, v___y_5099_, v___y_5100_, v_leanOpts_5101_, v_reconfigure_5102_, v_as_5103_, v_i_5104_, v_stop_5105_, v_b_5106_, v___y_5107_);
stack->m_obj
 = v_res_5243_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_pkg_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v_leanOpts_5247_, lean_object* v_reconfigure_5248_, lean_object* v_as_5249_, lean_object* v_i_5250_, lean_object* v_stop_5251_, lean_object* v_b_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
uint8_t v_reconfigure_boxed_5255_; size_t v_i_boxed_5256_; size_t v_stop_boxed_5257_; lean_object* v_res_5258_; 
v_reconfigure_boxed_5255_ = lean_unbox(v_reconfigure_5248_);
v_i_boxed_5256_ = lean_unbox_usize(v_i_5250_);
lean_dec(v_i_5250_);
v_stop_boxed_5257_ = lean_unbox_usize(v_stop_5251_);
lean_dec(v_stop_5251_);
v_res_5258_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5244_, v___y_5245_, v___y_5246_, v_leanOpts_5247_, v_reconfigure_boxed_5255_, v_as_5249_, v_i_boxed_5256_, v_stop_boxed_5257_, v_b_5252_, v___y_5253_);
lean_dec_ref(v___y_5253_);
lean_dec_ref(v_as_5249_);
lean_dec(v___y_5245_);
return v_res_5258_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_start_5259_, lean_object* v_pkg_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v_leanOpts_5263_, uint8_t v_reconfigure_5264_, lean_object* v_as_5265_, size_t v_i_5266_, size_t v_stop_5267_, lean_object* v_b_5268_, lean_object* v___y_5269_){
_start:
{
uint8_t v___x_5271_; 
v___x_5271_ = lean_usize_dec_eq(v_i_5266_, v_stop_5267_);
if (v___x_5271_ == 0)
{
lean_object* v_ws_5272_; lean_object* v_depIdxs_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5403_; 
v_ws_5272_ = lean_ctor_get(v_b_5268_, 0);
v_depIdxs_5273_ = lean_ctor_get(v_b_5268_, 1);
v_isSharedCheck_5403_ = !lean_is_exclusive(v_b_5268_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5275_ = v_b_5268_;
v_isShared_5276_ = v_isSharedCheck_5403_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_depIdxs_5273_);
lean_inc(v_ws_5272_);
lean_dec(v_b_5268_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5403_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v_lakeEnv_5277_; lean_object* v_packages_5278_; size_t v___x_5279_; size_t v___x_5280_; lean_object* v___x_5281_; lean_object* v___f_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v_lakeEnv_5277_ = lean_ctor_get(v_ws_5272_, 0);
v_packages_5278_ = lean_ctor_get(v_ws_5272_, 4);
v___x_5279_ = ((size_t)1ULL);
v___x_5280_ = lean_usize_sub(v_i_5266_, v___x_5279_);
v___x_5281_ = lean_array_uget_borrowed(v_as_5265_, v___x_5280_);
lean_inc(v___x_5281_);
v___f_5282_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5282_, 0, v___x_5281_);
v___x_5283_ = lean_unsigned_to_nat(0u);
v___x_5284_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5282_, v_packages_5278_, v___x_5283_);
if (lean_obj_tag(v___x_5284_) == 1)
{
lean_object* v_val_5285_; lean_object* v___x_5286_; lean_object* v___x_5288_; 
v_val_5285_ = lean_ctor_get(v___x_5284_, 0);
lean_inc(v_val_5285_);
lean_dec_ref_known(v___x_5284_, 1);
v___x_5286_ = lean_array_push(v_depIdxs_5273_, v_val_5285_);
if (v_isShared_5276_ == 0)
{
lean_ctor_set(v___x_5275_, 1, v___x_5286_);
v___x_5288_ = v___x_5275_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_ws_5272_);
lean_ctor_set(v_reuseFailAlloc_5290_, 1, v___x_5286_);
v___x_5288_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
lean_object* v___x_5289_; 
v___x_5289_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5260_, v___y_5261_, v___y_5262_, v_leanOpts_5263_, v_reconfigure_5264_, v_as_5265_, v___x_5280_, v_stop_5267_, v___x_5288_, v___y_5269_);
return v___x_5289_;
}
}
else
{
lean_object* v_wsIdx_5291_; lean_object* v_baseName_5292_; lean_object* v_name_5293_; lean_object* v_opts_5294_; uint8_t v___x_5295_; 
lean_dec(v___x_5284_);
v_wsIdx_5291_ = lean_ctor_get(v_pkg_5260_, 0);
v_baseName_5292_ = lean_ctor_get(v_pkg_5260_, 1);
v_name_5293_ = lean_ctor_get(v___x_5281_, 0);
v_opts_5294_ = lean_ctor_get(v___x_5281_, 4);
v___x_5295_ = lean_name_eq(v_baseName_5292_, v_name_5293_);
if (v___x_5295_ == 0)
{
lean_object* v___x_5296_; 
v___x_5296_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5261_, v_name_5293_);
if (lean_obj_tag(v___x_5296_) == 1)
{
lean_object* v_val_5297_; lean_object* v___x_5298_; lean_object* v_dir_5299_; lean_object* v___x_5300_; 
v_val_5297_ = lean_ctor_get(v___x_5296_, 0);
lean_inc(v_val_5297_);
lean_dec_ref_known(v___x_5296_, 1);
v___x_5298_ = lean_array_fget_borrowed(v_packages_5278_, v___x_5283_);
v_dir_5299_ = lean_ctor_get(v___x_5298_, 4);
lean_inc_ref(v___y_5262_);
lean_inc_ref(v_dir_5299_);
v___x_5300_ = l_Lake_PackageEntry_materialize(v_val_5297_, v_lakeEnv_5277_, v_dir_5299_, v___y_5262_, v___y_5269_);
if (lean_obj_tag(v___x_5300_) == 0)
{
lean_object* v_a_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5357_; 
v_a_5301_ = lean_ctor_get(v___x_5300_, 0);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5300_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5303_ = v___x_5300_;
v_isShared_5304_ = v_isSharedCheck_5357_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_a_5301_);
lean_dec(v___x_5300_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5357_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5305_; lean_object* v_wsIdx_5306_; lean_object* v___x_5307_; 
v___x_5305_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_5306_ = lean_array_get_size(v_packages_5278_);
lean_inc_ref(v_leanOpts_5263_);
lean_inc(v_opts_5294_);
v___x_5307_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5272_, v_a_5301_, v_opts_5294_, v_leanOpts_5263_, v_reconfigure_5264_, v___x_5305_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v_a_5309_; lean_object* v___x_5310_; lean_object* v___x_5312_; 
lean_del_object(v___x_5303_);
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5308_);
v_a_5309_ = lean_ctor_get(v___x_5307_, 1);
lean_inc(v_a_5309_);
lean_dec_ref_known(v___x_5307_, 2);
v___x_5310_ = lean_array_push(v_depIdxs_5273_, v_wsIdx_5306_);
if (v_isShared_5276_ == 0)
{
lean_ctor_set(v___x_5275_, 1, v___x_5310_);
lean_ctor_set(v___x_5275_, 0, v_a_5308_);
v___x_5312_ = v___x_5275_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_a_5308_);
lean_ctor_set(v_reuseFailAlloc_5329_, 1, v___x_5310_);
v___x_5312_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
lean_object* v___x_5313_; uint8_t v___x_5314_; 
v___x_5313_ = lean_array_get_size(v_a_5309_);
v___x_5314_ = lean_nat_dec_lt(v___x_5283_, v___x_5313_);
if (v___x_5314_ == 0)
{
lean_object* v___x_5315_; 
lean_dec(v_a_5309_);
v___x_5315_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5260_, v___y_5261_, v___y_5262_, v_leanOpts_5263_, v_reconfigure_5264_, v_as_5265_, v___x_5280_, v_stop_5267_, v___x_5312_, v___y_5269_);
return v___x_5315_;
}
else
{
lean_object* v___x_5316_; size_t v___x_5317_; size_t v___x_5318_; lean_object* v___x_5319_; 
v___x_5316_ = lean_box(0);
v___x_5317_ = ((size_t)0ULL);
v___x_5318_ = lean_usize_of_nat(v___x_5313_);
v___x_5319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5309_, v___x_5317_, v___x_5318_, v___x_5316_, v___y_5269_);
lean_dec(v_a_5309_);
if (lean_obj_tag(v___x_5319_) == 0)
{
lean_object* v___x_5320_; 
lean_dec_ref_known(v___x_5319_, 1);
v___x_5320_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5260_, v___y_5261_, v___y_5262_, v_leanOpts_5263_, v_reconfigure_5264_, v_as_5265_, v___x_5280_, v_stop_5267_, v___x_5312_, v___y_5269_);
return v___x_5320_;
}
else
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
lean_dec_ref(v___x_5312_);
lean_dec_ref(v_leanOpts_5263_);
lean_dec_ref(v___y_5262_);
lean_dec_ref(v_pkg_5260_);
v_a_5321_ = lean_ctor_get(v___x_5319_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5319_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5323_ = v___x_5319_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5319_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5321_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
}
}
}
else
{
lean_object* v_a_5330_; lean_object* v___x_5331_; uint8_t v___x_5332_; 
lean_del_object(v___x_5275_);
lean_dec_ref(v_depIdxs_5273_);
lean_dec_ref(v_leanOpts_5263_);
lean_dec_ref(v___y_5262_);
lean_dec_ref(v_pkg_5260_);
v_a_5330_ = lean_ctor_get(v___x_5307_, 1);
lean_inc(v_a_5330_);
lean_dec_ref_known(v___x_5307_, 2);
v___x_5331_ = lean_array_get_size(v_a_5330_);
v___x_5332_ = lean_nat_dec_lt(v___x_5283_, v___x_5331_);
if (v___x_5332_ == 0)
{
lean_object* v___x_5333_; lean_object* v___x_5335_; 
lean_dec(v_a_5330_);
v___x_5333_ = lean_box(0);
if (v_isShared_5304_ == 0)
{
lean_ctor_set_tag(v___x_5303_, 1);
lean_ctor_set(v___x_5303_, 0, v___x_5333_);
v___x_5335_ = v___x_5303_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v___x_5333_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
else
{
lean_object* v___x_5337_; size_t v___x_5338_; size_t v___x_5339_; lean_object* v___x_5340_; 
lean_del_object(v___x_5303_);
v___x_5337_ = lean_box(0);
v___x_5338_ = ((size_t)0ULL);
v___x_5339_ = lean_usize_of_nat(v___x_5331_);
v___x_5340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5330_, v___x_5338_, v___x_5339_, v___x_5337_, v___y_5269_);
lean_dec(v_a_5330_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5347_; 
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5347_ == 0)
{
lean_object* v_unused_5348_; 
v_unused_5348_ = lean_ctor_get(v___x_5340_, 0);
lean_dec(v_unused_5348_);
v___x_5342_ = v___x_5340_;
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
else
{
lean_dec(v___x_5340_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5345_; 
if (v_isShared_5343_ == 0)
{
lean_ctor_set_tag(v___x_5342_, 1);
lean_ctor_set(v___x_5342_, 0, v___x_5337_);
v___x_5345_ = v___x_5342_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5337_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
else
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5356_; 
v_a_5349_ = lean_ctor_get(v___x_5340_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5351_ = v___x_5340_;
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5340_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5354_; 
if (v_isShared_5352_ == 0)
{
v___x_5354_ = v___x_5351_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
lean_del_object(v___x_5275_);
lean_dec_ref(v_depIdxs_5273_);
lean_dec_ref(v_ws_5272_);
lean_dec_ref(v_leanOpts_5263_);
lean_dec_ref(v___y_5262_);
lean_dec_ref(v_pkg_5260_);
v_a_5358_ = lean_ctor_get(v___x_5300_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5300_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5300_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5300_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
}
else
{
uint8_t v___x_5366_; 
lean_inc(v_baseName_5292_);
lean_inc(v_wsIdx_5291_);
lean_dec(v___x_5296_);
lean_del_object(v___x_5275_);
lean_dec_ref(v_depIdxs_5273_);
lean_dec_ref(v_ws_5272_);
lean_dec_ref(v_leanOpts_5263_);
lean_dec_ref(v___y_5262_);
lean_dec_ref(v_pkg_5260_);
v___x_5366_ = lean_nat_dec_eq(v_wsIdx_5291_, v___x_5283_);
lean_dec(v_wsIdx_5291_);
if (v___x_5366_ == 0)
{
lean_object* v___x_5367_; uint8_t v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; uint8_t v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; 
v___x_5367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5368_ = 1;
lean_inc(v_name_5293_);
v___x_5369_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5293_, v___x_5368_);
v___x_5370_ = lean_string_append(v___x_5367_, v___x_5369_);
lean_dec_ref(v___x_5369_);
v___x_5371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5372_ = lean_string_append(v___x_5370_, v___x_5371_);
v___x_5373_ = l_Lean_Name_toString(v_baseName_5292_, v___x_5366_);
v___x_5374_ = lean_string_append(v___x_5372_, v___x_5373_);
lean_dec_ref(v___x_5373_);
v___x_5375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5376_ = lean_string_append(v___x_5374_, v___x_5375_);
v___x_5377_ = 3;
v___x_5378_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5378_, 0, v___x_5376_);
lean_ctor_set_uint8(v___x_5378_, sizeof(void*)*1, v___x_5377_);
lean_inc_ref(v___y_5269_);
v___x_5379_ = lean_apply_2(v___y_5269_, v___x_5378_, lean_box(0));
v___x_5380_ = lean_box(0);
v___x_5381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5381_, 0, v___x_5380_);
return v___x_5381_;
}
else
{
lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; uint8_t v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; 
lean_dec(v_baseName_5292_);
v___x_5382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5293_);
v___x_5383_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5293_, v___x_5366_);
v___x_5384_ = lean_string_append(v___x_5382_, v___x_5383_);
v___x_5385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5386_ = lean_string_append(v___x_5384_, v___x_5385_);
v___x_5387_ = lean_string_append(v___x_5386_, v___x_5383_);
lean_dec_ref(v___x_5383_);
v___x_5388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5389_ = lean_string_append(v___x_5387_, v___x_5388_);
v___x_5390_ = 3;
v___x_5391_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5391_, 0, v___x_5389_);
lean_ctor_set_uint8(v___x_5391_, sizeof(void*)*1, v___x_5390_);
lean_inc_ref(v___y_5269_);
v___x_5392_ = lean_apply_2(v___y_5269_, v___x_5391_, lean_box(0));
v___x_5393_ = lean_box(0);
v___x_5394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5394_, 0, v___x_5393_);
return v___x_5394_;
}
}
}
else
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; uint8_t v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
lean_inc(v_baseName_5292_);
lean_del_object(v___x_5275_);
lean_dec_ref(v_depIdxs_5273_);
lean_dec_ref(v_ws_5272_);
lean_dec_ref(v_leanOpts_5263_);
lean_dec_ref(v___y_5262_);
lean_dec_ref(v_pkg_5260_);
v___x_5395_ = l_Lean_Name_toString(v_baseName_5292_, v___x_5271_);
v___x_5396_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5397_ = lean_string_append(v___x_5395_, v___x_5396_);
v___x_5398_ = 3;
v___x_5399_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5399_, 0, v___x_5397_);
lean_ctor_set_uint8(v___x_5399_, sizeof(void*)*1, v___x_5398_);
lean_inc_ref(v___y_5269_);
v___x_5400_ = lean_apply_2(v___y_5269_, v___x_5399_, lean_box(0));
v___x_5401_ = lean_box(0);
v___x_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5401_);
return v___x_5402_;
}
}
}
}
else
{
lean_object* v___x_5404_; 
lean_dec_ref(v_leanOpts_5263_);
lean_dec_ref(v___y_5262_);
lean_dec_ref(v_pkg_5260_);
v___x_5404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5404_, 0, v_b_5268_);
return v___x_5404_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_5259_ = stack[0].m_obj;
lean_object* v_pkg_5260_ = stack[1].m_obj;
lean_object* v___y_5261_ = stack[2].m_obj;
lean_object* v___y_5262_ = stack[3].m_obj;
lean_object* v_leanOpts_5263_ = stack[4].m_obj;
uint8_t v_reconfigure_5264_ = stack[5].m_num;
lean_object* v_as_5265_ = stack[6].m_obj;
size_t v_i_5266_ = stack[7].m_num;
size_t v_stop_5267_ = stack[8].m_num;
lean_object* v_b_5268_ = stack[9].m_obj;
lean_object* v___y_5269_ = stack[10].m_obj;
lean_object* v_res_5405_;
v_res_5405_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5259_, v_pkg_5260_, v___y_5261_, v___y_5262_, v_leanOpts_5263_, v_reconfigure_5264_, v_as_5265_, v_i_5266_, v_stop_5267_, v_b_5268_, v___y_5269_);
stack->m_obj
 = v_res_5405_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_start_5406_, lean_object* v_pkg_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v_leanOpts_5410_, lean_object* v_reconfigure_5411_, lean_object* v_as_5412_, lean_object* v_i_5413_, lean_object* v_stop_5414_, lean_object* v_b_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_){
_start:
{
uint8_t v_reconfigure_boxed_5418_; size_t v_i_boxed_5419_; size_t v_stop_boxed_5420_; lean_object* v_res_5421_; 
v_reconfigure_boxed_5418_ = lean_unbox(v_reconfigure_5411_);
v_i_boxed_5419_ = lean_unbox_usize(v_i_5413_);
lean_dec(v_i_5413_);
v_stop_boxed_5420_ = lean_unbox_usize(v_stop_5414_);
lean_dec(v_stop_5414_);
v_res_5421_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5406_, v_pkg_5407_, v___y_5408_, v___y_5409_, v_leanOpts_5410_, v_reconfigure_boxed_5418_, v_as_5412_, v_i_boxed_5419_, v_stop_boxed_5420_, v_b_5415_, v___y_5416_);
lean_dec_ref(v___y_5416_);
lean_dec_ref(v_as_5412_);
lean_dec(v___y_5408_);
lean_dec(v_start_5406_);
return v_res_5421_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v_leanOpts_5424_, uint8_t v_reconfigure_5425_, lean_object* v_ws_5426_, lean_object* v_i_5427_, lean_object* v_next_5428_, lean_object* v___y_5429_){
_start:
{
lean_object* v_packages_5431_; lean_object* v_pkg_5432_; lean_object* v_ws_5434_; lean_object* v_depIdxs_5435_; lean_object* v___y_5436_; lean_object* v_____x_5446_; lean_object* v___y_5447_; lean_object* v_depConfigs_5450_; lean_object* v_start_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v_s_5454_; lean_object* v___x_5455_; uint8_t v___x_5456_; 
v_packages_5431_ = lean_ctor_get(v_ws_5426_, 4);
v_pkg_5432_ = lean_array_fget(v_packages_5431_, v_i_5427_);
lean_dec(v_i_5427_);
v_depConfigs_5450_ = lean_ctor_get(v_pkg_5432_, 12);
v_start_5451_ = lean_array_get_size(v_packages_5431_);
v___x_5452_ = lean_array_get_size(v_depConfigs_5450_);
v___x_5453_ = lean_mk_empty_array_with_capacity(v___x_5452_);
lean_inc_ref(v___x_5453_);
lean_inc_ref(v_ws_5426_);
v_s_5454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5454_, 0, v_ws_5426_);
lean_ctor_set(v_s_5454_, 1, v___x_5453_);
v___x_5455_ = lean_unsigned_to_nat(0u);
v___x_5456_ = lean_nat_dec_le(v___x_5452_, v___x_5452_);
if (v___x_5456_ == 0)
{
uint8_t v___x_5457_; 
v___x_5457_ = lean_nat_dec_lt(v___x_5455_, v___x_5452_);
if (v___x_5457_ == 0)
{
lean_object* v_ws_5458_; lean_object* v_packages_5459_; lean_object* v___x_5460_; uint8_t v___x_5461_; 
lean_dec_ref_known(v_s_5454_, 2);
v_ws_5458_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5426_, v_pkg_5432_, v___x_5453_);
v_packages_5459_ = lean_ctor_get(v_ws_5458_, 4);
v___x_5460_ = lean_array_get_size(v_packages_5459_);
v___x_5461_ = lean_nat_dec_lt(v_next_5428_, v___x_5460_);
if (v___x_5461_ == 0)
{
lean_object* v___x_5462_; 
lean_dec(v_next_5428_);
lean_dec_ref(v_leanOpts_5424_);
lean_dec_ref(v___y_5423_);
v___x_5462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5462_, 0, v_ws_5458_);
return v___x_5462_;
}
else
{
lean_object* v___x_5463_; lean_object* v___x_5464_; 
v___x_5463_ = lean_unsigned_to_nat(1u);
v___x_5464_ = lean_nat_add(v_next_5428_, v___x_5463_);
v_ws_5426_ = v_ws_5458_;
v_i_5427_ = v_next_5428_;
v_next_5428_ = v___x_5464_;
goto _start;
}
}
else
{
size_t v___x_5466_; size_t v___x_5467_; lean_object* v___x_5468_; 
lean_dec_ref(v___x_5453_);
lean_dec_ref(v_ws_5426_);
v___x_5466_ = lean_usize_of_nat(v___x_5452_);
v___x_5467_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5424_);
lean_inc_ref(v___y_5423_);
lean_inc(v_pkg_5432_);
v___x_5468_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5451_, v_pkg_5432_, v___y_5422_, v___y_5423_, v_leanOpts_5424_, v_reconfigure_5425_, v_depConfigs_5450_, v___x_5466_, v___x_5467_, v_s_5454_, v___y_5429_);
if (lean_obj_tag(v___x_5468_) == 0)
{
lean_object* v_a_5469_; 
v_a_5469_ = lean_ctor_get(v___x_5468_, 0);
lean_inc(v_a_5469_);
lean_dec_ref_known(v___x_5468_, 1);
v_____x_5446_ = v_a_5469_;
v___y_5447_ = v___y_5429_;
goto v___jp_5445_;
}
else
{
lean_object* v_a_5470_; lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5477_; 
lean_dec(v_pkg_5432_);
lean_dec(v_next_5428_);
lean_dec_ref(v_leanOpts_5424_);
lean_dec_ref(v___y_5423_);
v_a_5470_ = lean_ctor_get(v___x_5468_, 0);
v_isSharedCheck_5477_ = !lean_is_exclusive(v___x_5468_);
if (v_isSharedCheck_5477_ == 0)
{
v___x_5472_ = v___x_5468_;
v_isShared_5473_ = v_isSharedCheck_5477_;
goto v_resetjp_5471_;
}
else
{
lean_inc(v_a_5470_);
lean_dec(v___x_5468_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5477_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
lean_object* v___x_5475_; 
if (v_isShared_5473_ == 0)
{
v___x_5475_ = v___x_5472_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_a_5470_);
v___x_5475_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
return v___x_5475_;
}
}
}
}
}
else
{
uint8_t v___x_5478_; 
v___x_5478_ = lean_nat_dec_lt(v___x_5455_, v___x_5452_);
if (v___x_5478_ == 0)
{
lean_dec_ref_known(v_s_5454_, 2);
v_ws_5434_ = v_ws_5426_;
v_depIdxs_5435_ = v___x_5453_;
v___y_5436_ = v___y_5429_;
goto v___jp_5433_;
}
else
{
size_t v___x_5479_; size_t v___x_5480_; lean_object* v___x_5481_; 
lean_dec_ref(v___x_5453_);
lean_dec_ref(v_ws_5426_);
v___x_5479_ = lean_usize_of_nat(v___x_5452_);
v___x_5480_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5424_);
lean_inc_ref(v___y_5423_);
lean_inc(v_pkg_5432_);
v___x_5481_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5451_, v_pkg_5432_, v___y_5422_, v___y_5423_, v_leanOpts_5424_, v_reconfigure_5425_, v_depConfigs_5450_, v___x_5479_, v___x_5480_, v_s_5454_, v___y_5429_);
if (lean_obj_tag(v___x_5481_) == 0)
{
lean_object* v_a_5482_; 
v_a_5482_ = lean_ctor_get(v___x_5481_, 0);
lean_inc(v_a_5482_);
lean_dec_ref_known(v___x_5481_, 1);
v_____x_5446_ = v_a_5482_;
v___y_5447_ = v___y_5429_;
goto v___jp_5445_;
}
else
{
lean_object* v_a_5483_; lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5490_; 
lean_dec(v_pkg_5432_);
lean_dec(v_next_5428_);
lean_dec_ref(v_leanOpts_5424_);
lean_dec_ref(v___y_5423_);
v_a_5483_ = lean_ctor_get(v___x_5481_, 0);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5481_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5485_ = v___x_5481_;
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
else
{
lean_inc(v_a_5483_);
lean_dec(v___x_5481_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5488_; 
if (v_isShared_5486_ == 0)
{
v___x_5488_ = v___x_5485_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_a_5483_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
}
v___jp_5433_:
{
lean_object* v_ws_5437_; lean_object* v_packages_5438_; lean_object* v___x_5439_; uint8_t v___x_5440_; 
v_ws_5437_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5434_, v_pkg_5432_, v_depIdxs_5435_);
v_packages_5438_ = lean_ctor_get(v_ws_5437_, 4);
v___x_5439_ = lean_array_get_size(v_packages_5438_);
v___x_5440_ = lean_nat_dec_lt(v_next_5428_, v___x_5439_);
if (v___x_5440_ == 0)
{
lean_object* v___x_5441_; 
lean_dec(v_next_5428_);
lean_dec_ref(v_leanOpts_5424_);
lean_dec_ref(v___y_5423_);
v___x_5441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5441_, 0, v_ws_5437_);
return v___x_5441_;
}
else
{
lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5442_ = lean_unsigned_to_nat(1u);
v___x_5443_ = lean_nat_add(v_next_5428_, v___x_5442_);
v_ws_5426_ = v_ws_5437_;
v_i_5427_ = v_next_5428_;
v_next_5428_ = v___x_5443_;
v___y_5429_ = v___y_5436_;
goto _start;
}
}
v___jp_5445_:
{
lean_object* v_ws_5448_; lean_object* v_depIdxs_5449_; 
v_ws_5448_ = lean_ctor_get(v_____x_5446_, 0);
lean_inc_ref(v_ws_5448_);
v_depIdxs_5449_ = lean_ctor_get(v_____x_5446_, 1);
lean_inc_ref(v_depIdxs_5449_);
lean_dec_ref(v_____x_5446_);
v_ws_5434_ = v_ws_5448_;
v_depIdxs_5435_ = v_depIdxs_5449_;
v___y_5436_ = v___y_5447_;
goto v___jp_5433_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5422_ = stack[0].m_obj;
lean_object* v___y_5423_ = stack[1].m_obj;
lean_object* v_leanOpts_5424_ = stack[2].m_obj;
uint8_t v_reconfigure_5425_ = stack[3].m_num;
lean_object* v_ws_5426_ = stack[4].m_obj;
lean_object* v_i_5427_ = stack[5].m_obj;
lean_object* v_next_5428_ = stack[6].m_obj;
lean_object* v___y_5429_ = stack[7].m_obj;
lean_object* v_res_5491_;
v_res_5491_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5422_, v___y_5423_, v_leanOpts_5424_, v_reconfigure_5425_, v_ws_5426_, v_i_5427_, v_next_5428_, v___y_5429_);
stack->m_obj
 = v_res_5491_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v_leanOpts_5494_, lean_object* v_reconfigure_5495_, lean_object* v_ws_5496_, lean_object* v_i_5497_, lean_object* v_next_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_){
_start:
{
uint8_t v_reconfigure_boxed_5501_; lean_object* v_res_5502_; 
v_reconfigure_boxed_5501_ = lean_unbox(v_reconfigure_5495_);
v_res_5502_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5492_, v___y_5493_, v_leanOpts_5494_, v_reconfigure_boxed_5501_, v_ws_5496_, v_i_5497_, v_next_5498_, v___y_5499_);
lean_dec_ref(v___y_5499_);
lean_dec(v___y_5492_);
return v_res_5502_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(lean_object* v_as_5503_, size_t v_i_5504_, size_t v_stop_5505_, lean_object* v_b_5506_){
_start:
{
uint8_t v___x_5507_; 
v___x_5507_ = lean_usize_dec_eq(v_i_5504_, v_stop_5505_);
if (v___x_5507_ == 0)
{
lean_object* v___x_5508_; lean_object* v_name_5509_; lean_object* v___x_5510_; size_t v___x_5511_; size_t v___x_5512_; 
v___x_5508_ = lean_array_uget_borrowed(v_as_5503_, v_i_5504_);
v_name_5509_ = lean_ctor_get(v___x_5508_, 0);
lean_inc(v___x_5508_);
lean_inc(v_name_5509_);
v___x_5510_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5509_, v___x_5508_, v_b_5506_);
v___x_5511_ = ((size_t)1ULL);
v___x_5512_ = lean_usize_add(v_i_5504_, v___x_5511_);
v_i_5504_ = v___x_5512_;
v_b_5506_ = v___x_5510_;
goto _start;
}
else
{
return v_b_5506_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5503_ = stack[0].m_obj;
size_t v_i_5504_ = stack[1].m_num;
size_t v_stop_5505_ = stack[2].m_num;
lean_object* v_b_5506_ = stack[3].m_obj;
lean_object* v_res_5514_;
v_res_5514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5503_, v_i_5504_, v_stop_5505_, v_b_5506_);
stack->m_obj
 = v_res_5514_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2___boxed(lean_object* v_as_5515_, lean_object* v_i_5516_, lean_object* v_stop_5517_, lean_object* v_b_5518_){
_start:
{
size_t v_i_boxed_5519_; size_t v_stop_boxed_5520_; lean_object* v_res_5521_; 
v_i_boxed_5519_ = lean_unbox_usize(v_i_5516_);
lean_dec(v_i_5516_);
v_stop_boxed_5520_ = lean_unbox_usize(v_stop_5517_);
lean_dec(v_stop_5517_);
v_res_5521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5515_, v_i_boxed_5519_, v_stop_boxed_5520_, v_b_5518_);
lean_dec_ref(v_as_5515_);
return v_res_5521_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5522_, size_t v_i_5523_, size_t v_stop_5524_, lean_object* v_b_5525_){
_start:
{
uint8_t v___x_5526_; 
v___x_5526_ = lean_usize_dec_eq(v_i_5523_, v_stop_5524_);
if (v___x_5526_ == 0)
{
lean_object* v___x_5527_; lean_object* v_name_5528_; lean_object* v___x_5529_; size_t v___x_5530_; size_t v___x_5531_; lean_object* v___x_5532_; 
v___x_5527_ = lean_array_uget_borrowed(v_as_5522_, v_i_5523_);
v_name_5528_ = lean_ctor_get(v___x_5527_, 0);
lean_inc(v___x_5527_);
lean_inc(v_name_5528_);
v___x_5529_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5528_, v___x_5527_, v_b_5525_);
v___x_5530_ = ((size_t)1ULL);
v___x_5531_ = lean_usize_add(v_i_5523_, v___x_5530_);
v___x_5532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5522_, v___x_5531_, v_stop_5524_, v___x_5529_);
return v___x_5532_;
}
else
{
return v_b_5525_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5522_ = stack[0].m_obj;
size_t v_i_5523_ = stack[1].m_num;
size_t v_stop_5524_ = stack[2].m_num;
lean_object* v_b_5525_ = stack[3].m_obj;
lean_object* v_res_5533_;
v_res_5533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5522_, v_i_5523_, v_stop_5524_, v_b_5525_);
stack->m_obj
 = v_res_5533_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5534_, lean_object* v_i_5535_, lean_object* v_stop_5536_, lean_object* v_b_5537_){
_start:
{
size_t v_i_boxed_5538_; size_t v_stop_boxed_5539_; lean_object* v_res_5540_; 
v_i_boxed_5538_ = lean_unbox_usize(v_i_5535_);
lean_dec(v_i_5535_);
v_stop_boxed_5539_ = lean_unbox_usize(v_stop_5536_);
lean_dec(v_stop_5536_);
v_res_5540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5534_, v_i_boxed_5538_, v_stop_boxed_5539_, v_b_5537_);
lean_dec_ref(v_as_5534_);
return v_res_5540_;
}
}
lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5550_, lean_object* v_manifest_5551_, lean_object* v_leanOpts_5552_, uint8_t v_reconfigure_5553_, lean_object* v_overrides_5554_, lean_object* v_a_5555_){
_start:
{
lean_object* v___y_5558_; lean_object* v___y_5559_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v___y_5562_; lean_object* v___y_5575_; lean_object* v___y_5576_; lean_object* v___y_5577_; lean_object* v___y_5578_; lean_object* v___y_5579_; lean_object* v___y_5580_; lean_object* v___y_5581_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5591_; lean_object* v___y_5592_; lean_object* v___y_5593_; lean_object* v___y_5594_; lean_object* v___y_5595_; lean_object* v___y_5606_; lean_object* v___y_5607_; lean_object* v___y_5608_; lean_object* v___y_5609_; lean_object* v_packagesDir_x3f_5652_; lean_object* v_packages_5653_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v___y_5669_; lean_object* v___x_5677_; lean_object* v___x_5678_; uint8_t v___x_5679_; 
v_packagesDir_x3f_5652_ = lean_ctor_get(v_manifest_5551_, 2);
lean_inc(v_packagesDir_x3f_5652_);
v_packages_5653_ = lean_ctor_get(v_manifest_5551_, 3);
lean_inc_ref(v_packages_5653_);
lean_dec_ref(v_manifest_5551_);
v___x_5677_ = lean_array_get_size(v_packages_5653_);
v___x_5678_ = lean_unsigned_to_nat(0u);
v___x_5679_ = lean_nat_dec_eq(v___x_5677_, v___x_5678_);
if (v___x_5679_ == 0)
{
lean_object* v_packages_5680_; lean_object* v___x_5681_; lean_object* v_config_5682_; lean_object* v_toWorkspaceConfig_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; uint8_t v___x_5687_; 
v_packages_5680_ = lean_ctor_get(v_ws_5550_, 4);
v___x_5681_ = lean_array_fget_borrowed(v_packages_5680_, v___x_5678_);
v_config_5682_ = lean_ctor_get(v___x_5681_, 6);
v_toWorkspaceConfig_5683_ = lean_ctor_get(v_config_5682_, 0);
lean_inc_ref(v_toWorkspaceConfig_5683_);
v___x_5684_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5683_);
v___x_5685_ = l_Lake_mkRelPathString(v___x_5684_);
v___x_5686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5685_);
v___x_5687_ = l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5652_, v___x_5686_);
lean_dec_ref_known(v___x_5686_, 1);
if (v___x_5687_ == 0)
{
lean_object* v___x_5688_; lean_object* v___x_5689_; 
v___x_5688_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5555_);
v___x_5689_ = lean_apply_2(v_a_5555_, v___x_5688_, lean_box(0));
v___y_5669_ = v_a_5555_;
goto v___jp_5668_;
}
else
{
v___y_5669_ = v_a_5555_;
goto v___jp_5668_;
}
}
else
{
v___y_5669_ = v_a_5555_;
goto v___jp_5668_;
}
v___jp_5557_:
{
lean_object* v___x_5563_; lean_object* v___x_5564_; 
v___x_5563_ = lean_array_get_size(v___y_5558_);
lean_dec_ref(v___y_5558_);
v___x_5564_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5561_, v___y_5562_, v_leanOpts_5552_, v_reconfigure_5553_, v_ws_5550_, v___y_5559_, v___x_5563_, v___y_5560_);
lean_dec(v___y_5561_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v_a_5565_; lean_object* v___x_5567_; uint8_t v_isShared_5568_; uint8_t v_isSharedCheck_5573_; 
v_a_5565_ = lean_ctor_get(v___x_5564_, 0);
v_isSharedCheck_5573_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5573_ == 0)
{
v___x_5567_ = v___x_5564_;
v_isShared_5568_ = v_isSharedCheck_5573_;
goto v_resetjp_5566_;
}
else
{
lean_inc(v_a_5565_);
lean_dec(v___x_5564_);
v___x_5567_ = lean_box(0);
v_isShared_5568_ = v_isSharedCheck_5573_;
goto v_resetjp_5566_;
}
v_resetjp_5566_:
{
lean_object* v___x_5569_; lean_object* v___x_5571_; 
v___x_5569_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_a_5565_);
if (v_isShared_5568_ == 0)
{
lean_ctor_set(v___x_5567_, 0, v___x_5569_);
v___x_5571_ = v___x_5567_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v___x_5569_);
v___x_5571_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
return v___x_5571_;
}
}
}
else
{
return v___x_5564_;
}
}
v___jp_5574_:
{
if (lean_obj_tag(v___y_5581_) == 0)
{
lean_dec_ref(v___y_5576_);
v___y_5558_ = v___y_5575_;
v___y_5559_ = v___y_5577_;
v___y_5560_ = v___y_5578_;
v___y_5561_ = v___y_5581_;
v___y_5562_ = v___y_5579_;
goto v___jp_5557_;
}
else
{
lean_object* v___x_5582_; uint8_t v___x_5583_; 
v___x_5582_ = lean_array_get_size(v___y_5576_);
lean_dec_ref(v___y_5576_);
v___x_5583_ = lean_nat_dec_eq(v___x_5582_, v___y_5580_);
if (v___x_5583_ == 0)
{
lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; 
lean_dec_ref(v___y_5579_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5575_);
lean_dec_ref(v_leanOpts_5552_);
lean_dec_ref(v_ws_5550_);
v___x_5584_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5578_);
v___x_5585_ = lean_apply_2(v___y_5578_, v___x_5584_, lean_box(0));
v___x_5586_ = lean_box(0);
v___x_5587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5587_, 0, v___x_5586_);
return v___x_5587_;
}
else
{
v___y_5558_ = v___y_5575_;
v___y_5559_ = v___y_5577_;
v___y_5560_ = v___y_5578_;
v___y_5561_ = v___y_5581_;
v___y_5562_ = v___y_5579_;
goto v___jp_5557_;
}
}
}
v___jp_5588_:
{
lean_object* v___x_5596_; uint8_t v___x_5597_; 
v___x_5596_ = lean_array_get_size(v_overrides_5554_);
v___x_5597_ = lean_nat_dec_lt(v___y_5594_, v___x_5596_);
if (v___x_5597_ == 0)
{
v___y_5575_ = v___y_5589_;
v___y_5576_ = v___y_5590_;
v___y_5577_ = v___y_5591_;
v___y_5578_ = v___y_5592_;
v___y_5579_ = v___y_5593_;
v___y_5580_ = v___y_5594_;
v___y_5581_ = v___y_5595_;
goto v___jp_5574_;
}
else
{
uint8_t v___x_5598_; 
v___x_5598_ = lean_nat_dec_le(v___x_5596_, v___x_5596_);
if (v___x_5598_ == 0)
{
if (v___x_5597_ == 0)
{
v___y_5575_ = v___y_5589_;
v___y_5576_ = v___y_5590_;
v___y_5577_ = v___y_5591_;
v___y_5578_ = v___y_5592_;
v___y_5579_ = v___y_5593_;
v___y_5580_ = v___y_5594_;
v___y_5581_ = v___y_5595_;
goto v___jp_5574_;
}
else
{
size_t v___x_5599_; size_t v___x_5600_; lean_object* v___x_5601_; 
v___x_5599_ = ((size_t)0ULL);
v___x_5600_ = lean_usize_of_nat(v___x_5596_);
v___x_5601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5554_, v___x_5599_, v___x_5600_, v___y_5595_);
v___y_5575_ = v___y_5589_;
v___y_5576_ = v___y_5590_;
v___y_5577_ = v___y_5591_;
v___y_5578_ = v___y_5592_;
v___y_5579_ = v___y_5593_;
v___y_5580_ = v___y_5594_;
v___y_5581_ = v___x_5601_;
goto v___jp_5574_;
}
}
else
{
size_t v___x_5602_; size_t v___x_5603_; lean_object* v___x_5604_; 
v___x_5602_ = ((size_t)0ULL);
v___x_5603_ = lean_usize_of_nat(v___x_5596_);
v___x_5604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5554_, v___x_5602_, v___x_5603_, v___y_5595_);
v___y_5575_ = v___y_5589_;
v___y_5576_ = v___y_5590_;
v___y_5577_ = v___y_5591_;
v___y_5578_ = v___y_5592_;
v___y_5579_ = v___y_5593_;
v___y_5580_ = v___y_5594_;
v___y_5581_ = v___x_5604_;
goto v___jp_5574_;
}
}
}
v___jp_5605_:
{
lean_object* v_packages_5610_; lean_object* v___x_5611_; lean_object* v_wsIdx_5612_; lean_object* v_dir_5613_; lean_object* v_depConfigs_5614_; lean_object* v___x_5615_; 
v_packages_5610_ = lean_ctor_get(v_ws_5550_, 4);
v___x_5611_ = lean_array_fget_borrowed(v_packages_5610_, v___y_5608_);
v_wsIdx_5612_ = lean_ctor_get(v___x_5611_, 0);
v_dir_5613_ = lean_ctor_get(v___x_5611_, 4);
v_depConfigs_5614_ = lean_ctor_get(v___x_5611_, 12);
v___x_5615_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5609_, v_depConfigs_5614_, v___y_5606_);
if (lean_obj_tag(v___x_5615_) == 0)
{
lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; 
lean_dec_ref_known(v___x_5615_, 1);
v___x_5616_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5613_);
v___x_5617_ = l_Lake_joinRelative(v_dir_5613_, v___x_5616_);
v___x_5618_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5619_ = l_Lake_joinRelative(v___x_5617_, v___x_5618_);
v___x_5620_ = l_Lake_Manifest_tryLoadEntries(v___x_5619_);
if (lean_obj_tag(v___x_5620_) == 0)
{
lean_object* v_a_5621_; lean_object* v___x_5622_; uint8_t v___x_5623_; 
v_a_5621_ = lean_ctor_get(v___x_5620_, 0);
lean_inc(v_a_5621_);
lean_dec_ref_known(v___x_5620_, 1);
v___x_5622_ = lean_array_get_size(v_a_5621_);
v___x_5623_ = lean_nat_dec_lt(v___y_5608_, v___x_5622_);
if (v___x_5623_ == 0)
{
lean_dec(v_a_5621_);
lean_inc(v_wsIdx_5612_);
lean_inc_ref(v_depConfigs_5614_);
lean_inc_ref(v_packages_5610_);
v___y_5589_ = v_packages_5610_;
v___y_5590_ = v_depConfigs_5614_;
v___y_5591_ = v_wsIdx_5612_;
v___y_5592_ = v___y_5606_;
v___y_5593_ = v___y_5607_;
v___y_5594_ = v___y_5608_;
v___y_5595_ = v___y_5609_;
goto v___jp_5588_;
}
else
{
uint8_t v___x_5624_; 
v___x_5624_ = lean_nat_dec_le(v___x_5622_, v___x_5622_);
if (v___x_5624_ == 0)
{
if (v___x_5623_ == 0)
{
lean_dec(v_a_5621_);
lean_inc(v_wsIdx_5612_);
lean_inc_ref(v_depConfigs_5614_);
lean_inc_ref(v_packages_5610_);
v___y_5589_ = v_packages_5610_;
v___y_5590_ = v_depConfigs_5614_;
v___y_5591_ = v_wsIdx_5612_;
v___y_5592_ = v___y_5606_;
v___y_5593_ = v___y_5607_;
v___y_5594_ = v___y_5608_;
v___y_5595_ = v___y_5609_;
goto v___jp_5588_;
}
else
{
size_t v___x_5625_; size_t v___x_5626_; lean_object* v___x_5627_; 
v___x_5625_ = ((size_t)0ULL);
v___x_5626_ = lean_usize_of_nat(v___x_5622_);
v___x_5627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5621_, v___x_5625_, v___x_5626_, v___y_5609_);
lean_dec(v_a_5621_);
lean_inc(v_wsIdx_5612_);
lean_inc_ref(v_depConfigs_5614_);
lean_inc_ref(v_packages_5610_);
v___y_5589_ = v_packages_5610_;
v___y_5590_ = v_depConfigs_5614_;
v___y_5591_ = v_wsIdx_5612_;
v___y_5592_ = v___y_5606_;
v___y_5593_ = v___y_5607_;
v___y_5594_ = v___y_5608_;
v___y_5595_ = v___x_5627_;
goto v___jp_5588_;
}
}
else
{
size_t v___x_5628_; size_t v___x_5629_; lean_object* v___x_5630_; 
v___x_5628_ = ((size_t)0ULL);
v___x_5629_ = lean_usize_of_nat(v___x_5622_);
v___x_5630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5621_, v___x_5628_, v___x_5629_, v___y_5609_);
lean_dec(v_a_5621_);
lean_inc(v_wsIdx_5612_);
lean_inc_ref(v_depConfigs_5614_);
lean_inc_ref(v_packages_5610_);
v___y_5589_ = v_packages_5610_;
v___y_5590_ = v_depConfigs_5614_;
v___y_5591_ = v_wsIdx_5612_;
v___y_5592_ = v___y_5606_;
v___y_5593_ = v___y_5607_;
v___y_5594_ = v___y_5608_;
v___y_5595_ = v___x_5630_;
goto v___jp_5588_;
}
}
}
else
{
lean_object* v_a_5631_; lean_object* v___x_5633_; uint8_t v_isShared_5634_; uint8_t v_isSharedCheck_5643_; 
lean_dec(v___y_5609_);
lean_dec_ref(v___y_5607_);
lean_dec_ref(v_leanOpts_5552_);
lean_dec_ref(v_ws_5550_);
v_a_5631_ = lean_ctor_get(v___x_5620_, 0);
v_isSharedCheck_5643_ = !lean_is_exclusive(v___x_5620_);
if (v_isSharedCheck_5643_ == 0)
{
v___x_5633_ = v___x_5620_;
v_isShared_5634_ = v_isSharedCheck_5643_;
goto v_resetjp_5632_;
}
else
{
lean_inc(v_a_5631_);
lean_dec(v___x_5620_);
v___x_5633_ = lean_box(0);
v_isShared_5634_ = v_isSharedCheck_5643_;
goto v_resetjp_5632_;
}
v_resetjp_5632_:
{
lean_object* v___x_5635_; uint8_t v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5641_; 
v___x_5635_ = lean_io_error_to_string(v_a_5631_);
v___x_5636_ = 3;
v___x_5637_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5637_, 0, v___x_5635_);
lean_ctor_set_uint8(v___x_5637_, sizeof(void*)*1, v___x_5636_);
lean_inc_ref(v___y_5606_);
v___x_5638_ = lean_apply_2(v___y_5606_, v___x_5637_, lean_box(0));
v___x_5639_ = lean_box(0);
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 0, v___x_5639_);
v___x_5641_ = v___x_5633_;
goto v_reusejp_5640_;
}
else
{
lean_object* v_reuseFailAlloc_5642_; 
v_reuseFailAlloc_5642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5642_, 0, v___x_5639_);
v___x_5641_ = v_reuseFailAlloc_5642_;
goto v_reusejp_5640_;
}
v_reusejp_5640_:
{
return v___x_5641_;
}
}
}
}
else
{
lean_object* v_a_5644_; lean_object* v___x_5646_; uint8_t v_isShared_5647_; uint8_t v_isSharedCheck_5651_; 
lean_dec(v___y_5609_);
lean_dec_ref(v___y_5607_);
lean_dec_ref(v_leanOpts_5552_);
lean_dec_ref(v_ws_5550_);
v_a_5644_ = lean_ctor_get(v___x_5615_, 0);
v_isSharedCheck_5651_ = !lean_is_exclusive(v___x_5615_);
if (v_isSharedCheck_5651_ == 0)
{
v___x_5646_ = v___x_5615_;
v_isShared_5647_ = v_isSharedCheck_5651_;
goto v_resetjp_5645_;
}
else
{
lean_inc(v_a_5644_);
lean_dec(v___x_5615_);
v___x_5646_ = lean_box(0);
v_isShared_5647_ = v_isSharedCheck_5651_;
goto v_resetjp_5645_;
}
v_resetjp_5645_:
{
lean_object* v___x_5649_; 
if (v_isShared_5647_ == 0)
{
v___x_5649_ = v___x_5646_;
goto v_reusejp_5648_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_a_5644_);
v___x_5649_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5648_;
}
v_reusejp_5648_:
{
return v___x_5649_;
}
}
}
}
v___jp_5654_:
{
lean_object* v_pkgEntries_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; uint8_t v___x_5660_; 
v_pkgEntries_5657_ = lean_box(1);
v___x_5658_ = lean_unsigned_to_nat(0u);
v___x_5659_ = lean_array_get_size(v_packages_5653_);
v___x_5660_ = lean_nat_dec_lt(v___x_5658_, v___x_5659_);
if (v___x_5660_ == 0)
{
lean_dec_ref(v_packages_5653_);
v___y_5606_ = v___y_5655_;
v___y_5607_ = v___y_5656_;
v___y_5608_ = v___x_5658_;
v___y_5609_ = v_pkgEntries_5657_;
goto v___jp_5605_;
}
else
{
uint8_t v___x_5661_; 
v___x_5661_ = lean_nat_dec_le(v___x_5659_, v___x_5659_);
if (v___x_5661_ == 0)
{
if (v___x_5660_ == 0)
{
lean_dec_ref(v_packages_5653_);
v___y_5606_ = v___y_5655_;
v___y_5607_ = v___y_5656_;
v___y_5608_ = v___x_5658_;
v___y_5609_ = v_pkgEntries_5657_;
goto v___jp_5605_;
}
else
{
size_t v___x_5662_; size_t v___x_5663_; lean_object* v___x_5664_; 
v___x_5662_ = ((size_t)0ULL);
v___x_5663_ = lean_usize_of_nat(v___x_5659_);
v___x_5664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5653_, v___x_5662_, v___x_5663_, v_pkgEntries_5657_);
lean_dec_ref(v_packages_5653_);
v___y_5606_ = v___y_5655_;
v___y_5607_ = v___y_5656_;
v___y_5608_ = v___x_5658_;
v___y_5609_ = v___x_5664_;
goto v___jp_5605_;
}
}
else
{
size_t v___x_5665_; size_t v___x_5666_; lean_object* v___x_5667_; 
v___x_5665_ = ((size_t)0ULL);
v___x_5666_ = lean_usize_of_nat(v___x_5659_);
v___x_5667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5653_, v___x_5665_, v___x_5666_, v_pkgEntries_5657_);
lean_dec_ref(v_packages_5653_);
v___y_5606_ = v___y_5655_;
v___y_5607_ = v___y_5656_;
v___y_5608_ = v___x_5658_;
v___y_5609_ = v___x_5667_;
goto v___jp_5605_;
}
}
}
v___jp_5668_:
{
if (lean_obj_tag(v_packagesDir_x3f_5652_) == 0)
{
lean_object* v_packages_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v_config_5673_; lean_object* v_toWorkspaceConfig_5674_; lean_object* v___x_5675_; 
v_packages_5670_ = lean_ctor_get(v_ws_5550_, 4);
v___x_5671_ = lean_unsigned_to_nat(0u);
v___x_5672_ = lean_array_fget_borrowed(v_packages_5670_, v___x_5671_);
v_config_5673_ = lean_ctor_get(v___x_5672_, 6);
v_toWorkspaceConfig_5674_ = lean_ctor_get(v_config_5673_, 0);
lean_inc_ref(v_toWorkspaceConfig_5674_);
v___x_5675_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5674_);
v___y_5655_ = v___y_5669_;
v___y_5656_ = v___x_5675_;
goto v___jp_5654_;
}
else
{
lean_object* v_val_5676_; 
v_val_5676_ = lean_ctor_get(v_packagesDir_x3f_5652_, 0);
lean_inc(v_val_5676_);
lean_dec_ref_known(v_packagesDir_x3f_5652_, 1);
v___y_5655_ = v___y_5669_;
v___y_5656_ = v_val_5676_;
goto v___jp_5654_;
}
}
}
}
LEAN_EXPORT void l_Lake_Workspace_materializeDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_5550_ = stack[0].m_obj;
lean_object* v_manifest_5551_ = stack[1].m_obj;
lean_object* v_leanOpts_5552_ = stack[2].m_obj;
uint8_t v_reconfigure_5553_ = stack[3].m_num;
lean_object* v_overrides_5554_ = stack[4].m_obj;
lean_object* v_a_5555_ = stack[5].m_obj;
lean_object* v_res_5690_;
v_res_5690_ = l_Lake_Workspace_materializeDeps(v_ws_5550_, v_manifest_5551_, v_leanOpts_5552_, v_reconfigure_5553_, v_overrides_5554_, v_a_5555_);
stack->m_obj
 = v_res_5690_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5691_, lean_object* v_manifest_5692_, lean_object* v_leanOpts_5693_, lean_object* v_reconfigure_5694_, lean_object* v_overrides_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_){
_start:
{
uint8_t v_reconfigure_boxed_5698_; lean_object* v_res_5699_; 
v_reconfigure_boxed_5698_ = lean_unbox(v_reconfigure_5694_);
v_res_5699_ = l_Lake_Workspace_materializeDeps(v_ws_5691_, v_manifest_5692_, v_leanOpts_5693_, v_reconfigure_boxed_5698_, v_overrides_5695_, v_a_5696_);
lean_dec_ref(v_a_5696_);
lean_dec_ref(v_overrides_5695_);
return v_res_5699_;
}
}
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v_leanOpts_5702_, uint8_t v_reconfigure_5703_, lean_object* v_ws_5704_, lean_object* v_i_5705_, lean_object* v_i__lt_5706_, lean_object* v_next_5707_, lean_object* v_lt__next_5708_, lean_object* v___y_5709_){
_start:
{
lean_object* v___x_5711_; 
v___x_5711_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5700_, v___y_5701_, v_leanOpts_5702_, v_reconfigure_5703_, v_ws_5704_, v_i_5705_, v_next_5707_, v___y_5709_);
return v___x_5711_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5700_ = stack[0].m_obj;
lean_object* v___y_5701_ = stack[1].m_obj;
lean_object* v_leanOpts_5702_ = stack[2].m_obj;
uint8_t v_reconfigure_5703_ = stack[3].m_num;
lean_object* v_ws_5704_ = stack[4].m_obj;
lean_object* v_i_5705_ = stack[5].m_obj;
lean_object* v_next_5707_ = stack[7].m_obj;
lean_object* v___y_5709_ = stack[9].m_obj;
lean_object* v_res_5712_;
v_res_5712_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5700_, v___y_5701_, v_leanOpts_5702_, v_reconfigure_5703_, v_ws_5704_, v_i_5705_, lean_box(0), v_next_5707_, lean_box(0), v___y_5709_);
stack->m_obj
 = v_res_5712_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v_leanOpts_5715_, lean_object* v_reconfigure_5716_, lean_object* v_ws_5717_, lean_object* v_i_5718_, lean_object* v_i__lt_5719_, lean_object* v_next_5720_, lean_object* v_lt__next_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_){
_start:
{
uint8_t v_reconfigure_boxed_5724_; lean_object* v_res_5725_; 
v_reconfigure_boxed_5724_ = lean_unbox(v_reconfigure_5716_);
v_res_5725_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5713_, v___y_5714_, v_leanOpts_5715_, v_reconfigure_boxed_5724_, v_ws_5717_, v_i_5718_, v_i__lt_5719_, v_next_5720_, v_lt__next_5721_, v___y_5722_);
lean_dec_ref(v___y_5722_);
lean_dec(v___y_5713_);
return v_res_5725_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(lean_object* v_start_5726_, lean_object* v_pkg_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v_leanOpts_5730_, uint8_t v_reconfigure_5731_, lean_object* v_as_5732_, size_t v_i_5733_, size_t v_stop_5734_, lean_object* v_b_5735_, lean_object* v___y_5736_){
_start:
{
lean_object* v___x_5738_; 
v___x_5738_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5727_, v___y_5728_, v___y_5729_, v_leanOpts_5730_, v_reconfigure_5731_, v_as_5732_, v_i_5733_, v_stop_5734_, v_b_5735_, v___y_5736_);
return v___x_5738_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_5726_ = stack[0].m_obj;
lean_object* v_pkg_5727_ = stack[1].m_obj;
lean_object* v___y_5728_ = stack[2].m_obj;
lean_object* v___y_5729_ = stack[3].m_obj;
lean_object* v_leanOpts_5730_ = stack[4].m_obj;
uint8_t v_reconfigure_5731_ = stack[5].m_num;
lean_object* v_as_5732_ = stack[6].m_obj;
size_t v_i_5733_ = stack[7].m_num;
size_t v_stop_5734_ = stack[8].m_num;
lean_object* v_b_5735_ = stack[9].m_obj;
lean_object* v___y_5736_ = stack[10].m_obj;
lean_object* v_res_5739_;
v_res_5739_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(v_start_5726_, v_pkg_5727_, v___y_5728_, v___y_5729_, v_leanOpts_5730_, v_reconfigure_5731_, v_as_5732_, v_i_5733_, v_stop_5734_, v_b_5735_, v___y_5736_);
stack->m_obj
 = v_res_5739_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_start_5740_, lean_object* v_pkg_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v_leanOpts_5744_, lean_object* v_reconfigure_5745_, lean_object* v_as_5746_, lean_object* v_i_5747_, lean_object* v_stop_5748_, lean_object* v_b_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_){
_start:
{
uint8_t v_reconfigure_boxed_5752_; size_t v_i_boxed_5753_; size_t v_stop_boxed_5754_; lean_object* v_res_5755_; 
v_reconfigure_boxed_5752_ = lean_unbox(v_reconfigure_5745_);
v_i_boxed_5753_ = lean_unbox_usize(v_i_5747_);
lean_dec(v_i_5747_);
v_stop_boxed_5754_ = lean_unbox_usize(v_stop_5748_);
lean_dec(v_stop_5748_);
v_res_5755_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(v_start_5740_, v_pkg_5741_, v___y_5742_, v___y_5743_, v_leanOpts_5744_, v_reconfigure_boxed_5752_, v_as_5746_, v_i_boxed_5753_, v_stop_boxed_5754_, v_b_5749_, v___y_5750_);
lean_dec_ref(v___y_5750_);
lean_dec_ref(v_as_5746_);
lean_dec(v___y_5742_);
lean_dec(v_start_5740_);
return v_res_5755_;
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

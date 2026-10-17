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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_132_ = lean_nat_add(v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec(v___y_130_);
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
lean_ctor_set(v___x_112_, 3, v___y_129_);
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
lean_ctor_set(v_reuseFailAlloc_137_, 3, v___y_129_);
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
v___y_129_ = v___x_144_;
v___y_130_ = v___x_145_;
v___y_131_ = v_size_146_;
goto v___jp_128_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___y_129_ = v___x_144_;
v___y_130_ = v___x_145_;
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
lean_object* v_wsIdx_472_; lean_object* v_baseName_473_; lean_object* v_keyName_474_; lean_object* v_origName_475_; lean_object* v_dir_476_; lean_object* v_relDir_477_; lean_object* v_config_478_; lean_object* v_configFile_479_; lean_object* v_relConfigFile_480_; lean_object* v_relManifestFile_481_; lean_object* v_scope_482_; lean_object* v_remoteUrl_483_; lean_object* v_depConfigs_484_; lean_object* v_depPkgs_485_; lean_object* v_targetDecls_486_; lean_object* v_targetDeclMap_487_; lean_object* v_defaultTargets_488_; lean_object* v_scripts_489_; lean_object* v_defaultScripts_490_; lean_object* v_postUpdateHooks_491_; lean_object* v_buildArchive_492_; lean_object* v_testDriver_493_; lean_object* v_lintDriver_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_517_; 
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
v_scripts_489_ = lean_ctor_get(v_pkg_470_, 18);
v_defaultScripts_490_ = lean_ctor_get(v_pkg_470_, 19);
v_postUpdateHooks_491_ = lean_ctor_get(v_pkg_470_, 20);
v_buildArchive_492_ = lean_ctor_get(v_pkg_470_, 21);
v_testDriver_493_ = lean_ctor_get(v_pkg_470_, 22);
v_lintDriver_494_ = lean_ctor_get(v_pkg_470_, 23);
v_isSharedCheck_517_ = !lean_is_exclusive(v_pkg_470_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_pkg_470_, 13);
lean_dec(v_unused_518_);
v___x_496_ = v_pkg_470_;
v_isShared_497_ = v_isSharedCheck_517_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_lintDriver_494_);
lean_inc(v_testDriver_493_);
lean_inc(v_buildArchive_492_);
lean_inc(v_postUpdateHooks_491_);
lean_inc(v_defaultScripts_490_);
lean_inc(v_scripts_489_);
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
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_517_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_lakeEnv_498_; lean_object* v_lakeConfig_499_; lean_object* v_lakeCache_500_; lean_object* v_lakeArgs_x3f_501_; lean_object* v_packages_502_; lean_object* v_packageMap_503_; lean_object* v_facetConfigs_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_516_; 
v_lakeEnv_498_ = lean_ctor_get(v_self_469_, 0);
v_lakeConfig_499_ = lean_ctor_get(v_self_469_, 1);
v_lakeCache_500_ = lean_ctor_get(v_self_469_, 2);
v_lakeArgs_x3f_501_ = lean_ctor_get(v_self_469_, 3);
v_packages_502_ = lean_ctor_get(v_self_469_, 4);
v_packageMap_503_ = lean_ctor_get(v_self_469_, 5);
v_facetConfigs_504_ = lean_ctor_get(v_self_469_, 6);
v_isSharedCheck_516_ = !lean_is_exclusive(v_self_469_);
if (v_isSharedCheck_516_ == 0)
{
v___x_506_ = v_self_469_;
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_facetConfigs_504_);
lean_inc(v_packageMap_503_);
lean_inc(v_packages_502_);
lean_inc(v_lakeArgs_x3f_501_);
lean_inc(v_lakeCache_500_);
lean_inc(v_lakeConfig_499_);
lean_inc(v_lakeEnv_498_);
lean_dec(v_self_469_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_pkg_509_; 
lean_inc(v_keyName_474_);
lean_inc(v_wsIdx_472_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 13, v_depIdxs_471_);
v_pkg_509_ = v___x_496_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_wsIdx_472_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_baseName_473_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_keyName_474_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_origName_475_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v_dir_476_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v_relDir_477_);
lean_ctor_set(v_reuseFailAlloc_515_, 6, v_config_478_);
lean_ctor_set(v_reuseFailAlloc_515_, 7, v_configFile_479_);
lean_ctor_set(v_reuseFailAlloc_515_, 8, v_relConfigFile_480_);
lean_ctor_set(v_reuseFailAlloc_515_, 9, v_relManifestFile_481_);
lean_ctor_set(v_reuseFailAlloc_515_, 10, v_scope_482_);
lean_ctor_set(v_reuseFailAlloc_515_, 11, v_remoteUrl_483_);
lean_ctor_set(v_reuseFailAlloc_515_, 12, v_depConfigs_484_);
lean_ctor_set(v_reuseFailAlloc_515_, 13, v_depIdxs_471_);
lean_ctor_set(v_reuseFailAlloc_515_, 14, v_depPkgs_485_);
lean_ctor_set(v_reuseFailAlloc_515_, 15, v_targetDecls_486_);
lean_ctor_set(v_reuseFailAlloc_515_, 16, v_targetDeclMap_487_);
lean_ctor_set(v_reuseFailAlloc_515_, 17, v_defaultTargets_488_);
lean_ctor_set(v_reuseFailAlloc_515_, 18, v_scripts_489_);
lean_ctor_set(v_reuseFailAlloc_515_, 19, v_defaultScripts_490_);
lean_ctor_set(v_reuseFailAlloc_515_, 20, v_postUpdateHooks_491_);
lean_ctor_set(v_reuseFailAlloc_515_, 21, v_buildArchive_492_);
lean_ctor_set(v_reuseFailAlloc_515_, 22, v_testDriver_493_);
lean_ctor_set(v_reuseFailAlloc_515_, 23, v_lintDriver_494_);
v_pkg_509_ = v_reuseFailAlloc_515_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
lean_inc_ref(v_pkg_509_);
v___x_510_ = lean_array_fset(v_packages_502_, v_wsIdx_472_, v_pkg_509_);
lean_dec(v_wsIdx_472_);
v___x_511_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_474_, v_pkg_509_, v_packageMap_503_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 5, v___x_511_);
lean_ctor_set(v___x_506_, 4, v___x_510_);
v___x_513_ = v___x_506_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_lakeEnv_498_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_lakeConfig_499_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_lakeCache_500_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_lakeArgs_x3f_501_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_514_, 5, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 6, v_facetConfigs_504_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs(lean_object* v_self_519_, lean_object* v_pkg_520_, lean_object* v_depIdxs_521_, lean_object* v_h__wsIdx_522_, lean_object* v_h__depIdxs_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_self_519_, v_pkg_520_, v_depIdxs_521_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(lean_object* v_val_525_, size_t v_sz_526_, size_t v_i_527_, lean_object* v_bs_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = lean_usize_dec_lt(v_i_527_, v_sz_526_);
if (v___x_529_ == 0)
{
return v_bs_528_;
}
else
{
lean_object* v_v_530_; lean_object* v___x_531_; lean_object* v_bs_x27_532_; lean_object* v___x_533_; size_t v___x_534_; size_t v___x_535_; lean_object* v___x_536_; 
v_v_530_ = lean_array_uget(v_bs_528_, v_i_527_);
v___x_531_ = lean_unsigned_to_nat(0u);
v_bs_x27_532_ = lean_array_uset(v_bs_528_, v_i_527_, v___x_531_);
v___x_533_ = lean_array_fget_borrowed(v_val_525_, v_v_530_);
lean_dec(v_v_530_);
v___x_534_ = ((size_t)1ULL);
v___x_535_ = lean_usize_add(v_i_527_, v___x_534_);
lean_inc(v___x_533_);
v___x_536_ = lean_array_uset(v_bs_x27_532_, v_i_527_, v___x_533_);
v_i_527_ = v___x_535_;
v_bs_528_ = v___x_536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0___boxed(lean_object* v_val_538_, lean_object* v_sz_539_, lean_object* v_i_540_, lean_object* v_bs_541_){
_start:
{
size_t v_sz_boxed_542_; size_t v_i_boxed_543_; lean_object* v_res_544_; 
v_sz_boxed_542_ = lean_unbox_usize(v_sz_539_);
lean_dec(v_sz_539_);
v_i_boxed_543_ = lean_unbox_usize(v_i_540_);
lean_dec(v_i_540_);
v_res_544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_val_538_, v_sz_boxed_542_, v_i_boxed_543_, v_bs_541_);
lean_dec_ref(v_val_538_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_zero_547_; uint8_t v_isZero_548_; 
v_zero_547_ = lean_unsigned_to_nat(0u);
v_isZero_548_ = lean_nat_dec_eq(v_x_545_, v_zero_547_);
if (v_isZero_548_ == 1)
{
lean_dec(v_x_545_);
return v_x_546_;
}
else
{
lean_object* v_one_549_; lean_object* v_n_550_; lean_object* v_pkg_551_; lean_object* v_wsIdx_552_; lean_object* v_baseName_553_; lean_object* v_keyName_554_; lean_object* v_origName_555_; lean_object* v_dir_556_; lean_object* v_relDir_557_; lean_object* v_config_558_; lean_object* v_configFile_559_; lean_object* v_relConfigFile_560_; lean_object* v_relManifestFile_561_; lean_object* v_scope_562_; lean_object* v_remoteUrl_563_; lean_object* v_depConfigs_564_; lean_object* v_depIdxs_565_; lean_object* v_targetDecls_566_; lean_object* v_targetDeclMap_567_; lean_object* v_defaultTargets_568_; lean_object* v_scripts_569_; lean_object* v_defaultScripts_570_; lean_object* v_postUpdateHooks_571_; lean_object* v_buildArchive_572_; lean_object* v_testDriver_573_; lean_object* v_lintDriver_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_586_; 
v_one_549_ = lean_unsigned_to_nat(1u);
v_n_550_ = lean_nat_sub(v_x_545_, v_one_549_);
lean_dec(v_x_545_);
v_pkg_551_ = lean_array_fget(v_x_546_, v_n_550_);
v_wsIdx_552_ = lean_ctor_get(v_pkg_551_, 0);
v_baseName_553_ = lean_ctor_get(v_pkg_551_, 1);
v_keyName_554_ = lean_ctor_get(v_pkg_551_, 2);
v_origName_555_ = lean_ctor_get(v_pkg_551_, 3);
v_dir_556_ = lean_ctor_get(v_pkg_551_, 4);
v_relDir_557_ = lean_ctor_get(v_pkg_551_, 5);
v_config_558_ = lean_ctor_get(v_pkg_551_, 6);
v_configFile_559_ = lean_ctor_get(v_pkg_551_, 7);
v_relConfigFile_560_ = lean_ctor_get(v_pkg_551_, 8);
v_relManifestFile_561_ = lean_ctor_get(v_pkg_551_, 9);
v_scope_562_ = lean_ctor_get(v_pkg_551_, 10);
v_remoteUrl_563_ = lean_ctor_get(v_pkg_551_, 11);
v_depConfigs_564_ = lean_ctor_get(v_pkg_551_, 12);
v_depIdxs_565_ = lean_ctor_get(v_pkg_551_, 13);
v_targetDecls_566_ = lean_ctor_get(v_pkg_551_, 15);
v_targetDeclMap_567_ = lean_ctor_get(v_pkg_551_, 16);
v_defaultTargets_568_ = lean_ctor_get(v_pkg_551_, 17);
v_scripts_569_ = lean_ctor_get(v_pkg_551_, 18);
v_defaultScripts_570_ = lean_ctor_get(v_pkg_551_, 19);
v_postUpdateHooks_571_ = lean_ctor_get(v_pkg_551_, 20);
v_buildArchive_572_ = lean_ctor_get(v_pkg_551_, 21);
v_testDriver_573_ = lean_ctor_get(v_pkg_551_, 22);
v_lintDriver_574_ = lean_ctor_get(v_pkg_551_, 23);
v_isSharedCheck_586_ = !lean_is_exclusive(v_pkg_551_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v_pkg_551_, 14);
lean_dec(v_unused_587_);
v___x_576_ = v_pkg_551_;
v_isShared_577_ = v_isSharedCheck_586_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_lintDriver_574_);
lean_inc(v_testDriver_573_);
lean_inc(v_buildArchive_572_);
lean_inc(v_postUpdateHooks_571_);
lean_inc(v_defaultScripts_570_);
lean_inc(v_scripts_569_);
lean_inc(v_defaultTargets_568_);
lean_inc(v_targetDeclMap_567_);
lean_inc(v_targetDecls_566_);
lean_inc(v_depIdxs_565_);
lean_inc(v_depConfigs_564_);
lean_inc(v_remoteUrl_563_);
lean_inc(v_scope_562_);
lean_inc(v_relManifestFile_561_);
lean_inc(v_relConfigFile_560_);
lean_inc(v_configFile_559_);
lean_inc(v_config_558_);
lean_inc(v_relDir_557_);
lean_inc(v_dir_556_);
lean_inc(v_origName_555_);
lean_inc(v_keyName_554_);
lean_inc(v_baseName_553_);
lean_inc(v_wsIdx_552_);
lean_dec(v_pkg_551_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_586_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
size_t v_sz_578_; size_t v___x_579_; lean_object* v_depPkgs_580_; lean_object* v___x_582_; 
v_sz_578_ = lean_array_size(v_depIdxs_565_);
v___x_579_ = ((size_t)0ULL);
lean_inc_ref(v_depIdxs_565_);
v_depPkgs_580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_x_546_, v_sz_578_, v___x_579_, v_depIdxs_565_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 14, v_depPkgs_580_);
v___x_582_ = v___x_576_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_wsIdx_552_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_baseName_553_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_keyName_554_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_origName_555_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v_dir_556_);
lean_ctor_set(v_reuseFailAlloc_585_, 5, v_relDir_557_);
lean_ctor_set(v_reuseFailAlloc_585_, 6, v_config_558_);
lean_ctor_set(v_reuseFailAlloc_585_, 7, v_configFile_559_);
lean_ctor_set(v_reuseFailAlloc_585_, 8, v_relConfigFile_560_);
lean_ctor_set(v_reuseFailAlloc_585_, 9, v_relManifestFile_561_);
lean_ctor_set(v_reuseFailAlloc_585_, 10, v_scope_562_);
lean_ctor_set(v_reuseFailAlloc_585_, 11, v_remoteUrl_563_);
lean_ctor_set(v_reuseFailAlloc_585_, 12, v_depConfigs_564_);
lean_ctor_set(v_reuseFailAlloc_585_, 13, v_depIdxs_565_);
lean_ctor_set(v_reuseFailAlloc_585_, 14, v_depPkgs_580_);
lean_ctor_set(v_reuseFailAlloc_585_, 15, v_targetDecls_566_);
lean_ctor_set(v_reuseFailAlloc_585_, 16, v_targetDeclMap_567_);
lean_ctor_set(v_reuseFailAlloc_585_, 17, v_defaultTargets_568_);
lean_ctor_set(v_reuseFailAlloc_585_, 18, v_scripts_569_);
lean_ctor_set(v_reuseFailAlloc_585_, 19, v_defaultScripts_570_);
lean_ctor_set(v_reuseFailAlloc_585_, 20, v_postUpdateHooks_571_);
lean_ctor_set(v_reuseFailAlloc_585_, 21, v_buildArchive_572_);
lean_ctor_set(v_reuseFailAlloc_585_, 22, v_testDriver_573_);
lean_ctor_set(v_reuseFailAlloc_585_, 23, v_lintDriver_574_);
v___x_582_ = v_reuseFailAlloc_585_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v_pkgs_x27_583_; 
v_pkgs_x27_583_ = lean_array_fset(v_x_546_, v_n_550_, v___x_582_);
v_x_545_ = v_n_550_;
v_x_546_ = v_pkgs_x27_583_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(lean_object* v___x_588_, lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
lean_object* v_zero_591_; uint8_t v_isZero_592_; 
v_zero_591_ = lean_unsigned_to_nat(0u);
v_isZero_592_ = lean_nat_dec_eq(v_x_589_, v_zero_591_);
if (v_isZero_592_ == 1)
{
return v_x_590_;
}
else
{
lean_object* v_one_593_; lean_object* v_n_594_; lean_object* v_pkg_595_; lean_object* v_wsIdx_596_; lean_object* v_baseName_597_; lean_object* v_keyName_598_; lean_object* v_origName_599_; lean_object* v_dir_600_; lean_object* v_relDir_601_; lean_object* v_config_602_; lean_object* v_configFile_603_; lean_object* v_relConfigFile_604_; lean_object* v_relManifestFile_605_; lean_object* v_scope_606_; lean_object* v_remoteUrl_607_; lean_object* v_depConfigs_608_; lean_object* v_depIdxs_609_; lean_object* v_targetDecls_610_; lean_object* v_targetDeclMap_611_; lean_object* v_defaultTargets_612_; lean_object* v_scripts_613_; lean_object* v_defaultScripts_614_; lean_object* v_postUpdateHooks_615_; lean_object* v_buildArchive_616_; lean_object* v_testDriver_617_; lean_object* v_lintDriver_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_630_; 
v_one_593_ = lean_unsigned_to_nat(1u);
v_n_594_ = lean_nat_sub(v_x_589_, v_one_593_);
v_pkg_595_ = lean_array_fget(v_x_590_, v_n_594_);
v_wsIdx_596_ = lean_ctor_get(v_pkg_595_, 0);
v_baseName_597_ = lean_ctor_get(v_pkg_595_, 1);
v_keyName_598_ = lean_ctor_get(v_pkg_595_, 2);
v_origName_599_ = lean_ctor_get(v_pkg_595_, 3);
v_dir_600_ = lean_ctor_get(v_pkg_595_, 4);
v_relDir_601_ = lean_ctor_get(v_pkg_595_, 5);
v_config_602_ = lean_ctor_get(v_pkg_595_, 6);
v_configFile_603_ = lean_ctor_get(v_pkg_595_, 7);
v_relConfigFile_604_ = lean_ctor_get(v_pkg_595_, 8);
v_relManifestFile_605_ = lean_ctor_get(v_pkg_595_, 9);
v_scope_606_ = lean_ctor_get(v_pkg_595_, 10);
v_remoteUrl_607_ = lean_ctor_get(v_pkg_595_, 11);
v_depConfigs_608_ = lean_ctor_get(v_pkg_595_, 12);
v_depIdxs_609_ = lean_ctor_get(v_pkg_595_, 13);
v_targetDecls_610_ = lean_ctor_get(v_pkg_595_, 15);
v_targetDeclMap_611_ = lean_ctor_get(v_pkg_595_, 16);
v_defaultTargets_612_ = lean_ctor_get(v_pkg_595_, 17);
v_scripts_613_ = lean_ctor_get(v_pkg_595_, 18);
v_defaultScripts_614_ = lean_ctor_get(v_pkg_595_, 19);
v_postUpdateHooks_615_ = lean_ctor_get(v_pkg_595_, 20);
v_buildArchive_616_ = lean_ctor_get(v_pkg_595_, 21);
v_testDriver_617_ = lean_ctor_get(v_pkg_595_, 22);
v_lintDriver_618_ = lean_ctor_get(v_pkg_595_, 23);
v_isSharedCheck_630_ = !lean_is_exclusive(v_pkg_595_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v_pkg_595_, 14);
lean_dec(v_unused_631_);
v___x_620_ = v_pkg_595_;
v_isShared_621_ = v_isSharedCheck_630_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_lintDriver_618_);
lean_inc(v_testDriver_617_);
lean_inc(v_buildArchive_616_);
lean_inc(v_postUpdateHooks_615_);
lean_inc(v_defaultScripts_614_);
lean_inc(v_scripts_613_);
lean_inc(v_defaultTargets_612_);
lean_inc(v_targetDeclMap_611_);
lean_inc(v_targetDecls_610_);
lean_inc(v_depIdxs_609_);
lean_inc(v_depConfigs_608_);
lean_inc(v_remoteUrl_607_);
lean_inc(v_scope_606_);
lean_inc(v_relManifestFile_605_);
lean_inc(v_relConfigFile_604_);
lean_inc(v_configFile_603_);
lean_inc(v_config_602_);
lean_inc(v_relDir_601_);
lean_inc(v_dir_600_);
lean_inc(v_origName_599_);
lean_inc(v_keyName_598_);
lean_inc(v_baseName_597_);
lean_inc(v_wsIdx_596_);
lean_dec(v_pkg_595_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_630_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
size_t v_sz_622_; size_t v___x_623_; lean_object* v_depPkgs_624_; lean_object* v___x_626_; 
v_sz_622_ = lean_array_size(v_depIdxs_609_);
v___x_623_ = ((size_t)0ULL);
lean_inc_ref(v_depIdxs_609_);
v_depPkgs_624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__0(v_x_590_, v_sz_622_, v___x_623_, v_depIdxs_609_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 14, v_depPkgs_624_);
v___x_626_ = v___x_620_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_wsIdx_596_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_baseName_597_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_keyName_598_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v_origName_599_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v_dir_600_);
lean_ctor_set(v_reuseFailAlloc_629_, 5, v_relDir_601_);
lean_ctor_set(v_reuseFailAlloc_629_, 6, v_config_602_);
lean_ctor_set(v_reuseFailAlloc_629_, 7, v_configFile_603_);
lean_ctor_set(v_reuseFailAlloc_629_, 8, v_relConfigFile_604_);
lean_ctor_set(v_reuseFailAlloc_629_, 9, v_relManifestFile_605_);
lean_ctor_set(v_reuseFailAlloc_629_, 10, v_scope_606_);
lean_ctor_set(v_reuseFailAlloc_629_, 11, v_remoteUrl_607_);
lean_ctor_set(v_reuseFailAlloc_629_, 12, v_depConfigs_608_);
lean_ctor_set(v_reuseFailAlloc_629_, 13, v_depIdxs_609_);
lean_ctor_set(v_reuseFailAlloc_629_, 14, v_depPkgs_624_);
lean_ctor_set(v_reuseFailAlloc_629_, 15, v_targetDecls_610_);
lean_ctor_set(v_reuseFailAlloc_629_, 16, v_targetDeclMap_611_);
lean_ctor_set(v_reuseFailAlloc_629_, 17, v_defaultTargets_612_);
lean_ctor_set(v_reuseFailAlloc_629_, 18, v_scripts_613_);
lean_ctor_set(v_reuseFailAlloc_629_, 19, v_defaultScripts_614_);
lean_ctor_set(v_reuseFailAlloc_629_, 20, v_postUpdateHooks_615_);
lean_ctor_set(v_reuseFailAlloc_629_, 21, v_buildArchive_616_);
lean_ctor_set(v_reuseFailAlloc_629_, 22, v_testDriver_617_);
lean_ctor_set(v_reuseFailAlloc_629_, 23, v_lintDriver_618_);
v___x_626_ = v_reuseFailAlloc_629_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v_pkgs_x27_627_; lean_object* v___x_628_; 
v_pkgs_x27_627_ = lean_array_fset(v_x_590_, v_n_594_, v___x_626_);
v___x_628_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(v_n_594_, v_pkgs_x27_627_);
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1___boxed(lean_object* v___x_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(v___x_632_, v_x_633_, v_x_634_);
lean_dec(v_x_633_);
lean_dec(v___x_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_, lean_object* v_b_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_eq(v_i_637_, v_stop_638_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v_keyName_642_; lean_object* v___x_643_; size_t v___x_644_; size_t v___x_645_; 
v___x_641_ = lean_array_uget_borrowed(v_as_636_, v_i_637_);
v_keyName_642_ = lean_ctor_get(v___x_641_, 2);
lean_inc(v___x_641_);
lean_inc(v_keyName_642_);
v___x_643_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_642_, v___x_641_, v_b_639_);
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_add(v_i_637_, v___x_644_);
v_i_637_ = v___x_645_;
v_b_639_ = v___x_643_;
goto _start;
}
else
{
return v_b_639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2___boxed(lean_object* v_as_647_, lean_object* v_i_648_, lean_object* v_stop_649_, lean_object* v_b_650_){
_start:
{
size_t v_i_boxed_651_; size_t v_stop_boxed_652_; lean_object* v_res_653_; 
v_i_boxed_651_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_stop_boxed_652_ = lean_unbox_usize(v_stop_649_);
lean_dec(v_stop_649_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_as_647_, v_i_boxed_651_, v_stop_boxed_652_, v_b_650_);
lean_dec_ref(v_as_647_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(lean_object* v_self_654_){
_start:
{
lean_object* v_lakeEnv_655_; lean_object* v_lakeConfig_656_; lean_object* v_lakeCache_657_; lean_object* v_lakeArgs_x3f_658_; lean_object* v_packages_659_; lean_object* v_facetConfigs_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_679_; 
v_lakeEnv_655_ = lean_ctor_get(v_self_654_, 0);
v_lakeConfig_656_ = lean_ctor_get(v_self_654_, 1);
v_lakeCache_657_ = lean_ctor_get(v_self_654_, 2);
v_lakeArgs_x3f_658_ = lean_ctor_get(v_self_654_, 3);
v_packages_659_ = lean_ctor_get(v_self_654_, 4);
v_facetConfigs_660_ = lean_ctor_get(v_self_654_, 6);
v_isSharedCheck_679_ = !lean_is_exclusive(v_self_654_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v_self_654_, 5);
lean_dec(v_unused_680_);
v___x_662_ = v_self_654_;
v_isShared_663_ = v_isSharedCheck_679_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_facetConfigs_660_);
lean_inc(v_packages_659_);
lean_inc(v_lakeArgs_x3f_658_);
lean_inc(v_lakeCache_657_);
lean_inc(v_lakeConfig_656_);
lean_inc(v_lakeEnv_655_);
lean_dec(v_self_654_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_679_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v_val_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_664_ = lean_array_get_size(v_packages_659_);
v_val_665_ = l_Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1(v___x_664_, v___x_664_, v_packages_659_);
v___x_666_ = lean_box(1);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_array_get_size(v_val_665_);
v___x_669_ = lean_nat_dec_lt(v___x_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_671_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 5, v___x_666_);
lean_ctor_set(v___x_662_, 4, v_val_665_);
v___x_671_ = v___x_662_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_lakeEnv_655_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_lakeConfig_656_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_lakeCache_657_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_lakeArgs_x3f_658_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v_val_665_);
lean_ctor_set(v_reuseFailAlloc_672_, 5, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_672_, 6, v_facetConfigs_660_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_668_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__2(v_val_665_, v___x_673_, v___x_674_, v___x_666_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 5, v___x_675_);
lean_ctor_set(v___x_662_, 4, v_val_665_);
v___x_677_ = v___x_662_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_lakeEnv_655_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_lakeConfig_656_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_lakeCache_657_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_lakeArgs_x3f_658_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_val_665_);
lean_ctor_set(v_reuseFailAlloc_678_, 5, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_678_, 6, v_facetConfigs_660_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(lean_object* v___x_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___redArg(v_x_682_, v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1___boxed(lean_object* v___x_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Nat_foldRev___at___00Nat_foldRev___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs_spec__1_spec__1(v___x_685_, v_x_686_, v_x_687_);
lean_dec(v___x_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(lean_object* v_ws_689_, lean_object* v_size_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_mk_empty_array_with_capacity(v_size_690_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_ws_689_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init___boxed(lean_object* v_ws_693_, lean_object* v_size_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(v_ws_693_, v_size_694_);
lean_dec(v_size_694_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___redArg(lean_object* v_s_696_, lean_object* v_wsIdx_697_){
_start:
{
lean_object* v_ws_698_; lean_object* v_depIdxs_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
v_ws_698_ = lean_ctor_get(v_s_696_, 0);
v_depIdxs_699_ = lean_ctor_get(v_s_696_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_s_696_);
if (v_isSharedCheck_707_ == 0)
{
v___x_701_ = v_s_696_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_depIdxs_699_);
lean_inc(v_ws_698_);
lean_dec(v_s_696_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_array_push(v_depIdxs_699_, v_wsIdx_697_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_ws_698_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(lean_object* v_n_708_, lean_object* v_s_709_, lean_object* v_wsIdx_710_){
_start:
{
lean_object* v_ws_711_; lean_object* v_depIdxs_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
v_ws_711_ = lean_ctor_get(v_s_709_, 0);
v_depIdxs_712_ = lean_ctor_get(v_s_709_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_s_709_);
if (v_isSharedCheck_720_ == 0)
{
v___x_714_ = v_s_709_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_depIdxs_712_);
lean_inc(v_ws_711_);
lean_dec(v_s_709_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_array_push(v_depIdxs_712_, v_wsIdx_710_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_ws_711_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___boxed(lean_object* v_n_721_, lean_object* v_s_722_, lean_object* v_wsIdx_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(v_n_721_, v_s_722_, v_wsIdx_723_);
lean_dec(v_n_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(lean_object* v_s_725_, lean_object* v_dep_726_, lean_object* v_lakeOpts_727_, lean_object* v_leanOpts_728_, uint8_t v_reconfigure_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_ws_732_; lean_object* v_depIdxs_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_762_; 
v_ws_732_ = lean_ctor_get(v_s_725_, 0);
v_depIdxs_733_ = lean_ctor_get(v_s_725_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_s_725_);
if (v_isSharedCheck_762_ == 0)
{
v___x_735_ = v_s_725_;
v_isShared_736_ = v_isSharedCheck_762_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_depIdxs_733_);
lean_inc(v_ws_732_);
lean_dec(v_s_725_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_762_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_packages_737_; lean_object* v_wsIdx_738_; lean_object* v___x_739_; 
v_packages_737_ = lean_ctor_get(v_ws_732_, 4);
v_wsIdx_738_ = lean_array_get_size(v_packages_737_);
v___x_739_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_732_, v_dep_726_, v_lakeOpts_727_, v_leanOpts_728_, v_reconfigure_729_, v_a_730_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_752_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_a_741_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_752_ == 0)
{
v___x_743_ = v___x_739_;
v_isShared_744_ = v_isSharedCheck_752_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_752_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = lean_array_push(v_depIdxs_733_, v_wsIdx_738_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_745_);
lean_ctor_set(v___x_735_, 0, v_a_740_);
v___x_747_ = v___x_735_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_740_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_745_);
v___x_747_ = v_reuseFailAlloc_751_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_747_);
v___x_749_ = v___x_743_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_a_741_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_del_object(v___x_735_);
lean_dec_ref(v_depIdxs_733_);
v_a_753_ = lean_ctor_get(v___x_739_, 0);
v_a_754_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_739_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_inc(v_a_753_);
lean_dec(v___x_739_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_753_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg___boxed(lean_object* v_s_763_, lean_object* v_dep_764_, lean_object* v_lakeOpts_765_, lean_object* v_leanOpts_766_, lean_object* v_reconfigure_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
uint8_t v_reconfigure_boxed_770_; lean_object* v_res_771_; 
v_reconfigure_boxed_770_ = lean_unbox(v_reconfigure_767_);
v_res_771_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(v_s_763_, v_dep_764_, v_lakeOpts_765_, v_leanOpts_766_, v_reconfigure_boxed_770_, v_a_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(lean_object* v_n_772_, lean_object* v_s_773_, lean_object* v_dep_774_, lean_object* v_lakeOpts_775_, lean_object* v_leanOpts_776_, uint8_t v_reconfigure_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_ws_780_; lean_object* v_depIdxs_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_810_; 
v_ws_780_ = lean_ctor_get(v_s_773_, 0);
v_depIdxs_781_ = lean_ctor_get(v_s_773_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_s_773_);
if (v_isSharedCheck_810_ == 0)
{
v___x_783_ = v_s_773_;
v_isShared_784_ = v_isSharedCheck_810_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_depIdxs_781_);
lean_inc(v_ws_780_);
lean_dec(v_s_773_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_810_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_packages_785_; lean_object* v_wsIdx_786_; lean_object* v___x_787_; 
v_packages_785_ = lean_ctor_get(v_ws_780_, 4);
v_wsIdx_786_ = lean_array_get_size(v_packages_785_);
v___x_787_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_780_, v_dep_774_, v_lakeOpts_775_, v_leanOpts_776_, v_reconfigure_777_, v_a_778_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_800_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_a_789_ = lean_ctor_get(v___x_787_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_800_ == 0)
{
v___x_791_ = v___x_787_;
v_isShared_792_ = v_isSharedCheck_800_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_800_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_array_push(v_depIdxs_781_, v_wsIdx_786_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_793_);
lean_ctor_set(v___x_783_, 0, v_a_788_);
v___x_795_ = v___x_783_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_788_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_799_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_795_);
v___x_797_ = v___x_791_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_a_789_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_del_object(v___x_783_);
lean_dec_ref(v_depIdxs_781_);
v_a_801_ = lean_ctor_get(v___x_787_, 0);
v_a_802_ = lean_ctor_get(v___x_787_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_787_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_inc(v_a_801_);
lean_dec(v___x_787_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_801_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_a_802_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed(lean_object* v_n_811_, lean_object* v_s_812_, lean_object* v_dep_813_, lean_object* v_lakeOpts_814_, lean_object* v_leanOpts_815_, lean_object* v_reconfigure_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
uint8_t v_reconfigure_boxed_819_; lean_object* v_res_820_; 
v_reconfigure_boxed_819_ = lean_unbox(v_reconfigure_816_);
v_res_820_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(v_n_811_, v_s_812_, v_dep_813_, v_lakeOpts_814_, v_leanOpts_815_, v_reconfigure_boxed_819_, v_a_817_);
lean_dec(v_n_811_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___redArg(lean_object* v_inst_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = lean_apply_2(v_inst_821_, lean_box(0), lean_box(0));
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(lean_object* v_m_823_, lean_object* v_00_u03b1_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_as_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_apply_2(v_inst_825_, lean_box(0), lean_box(0));
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___boxed(lean_object* v_m_829_, lean_object* v_00_u03b1_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_as_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(v_m_829_, v_00_u03b1_830_, v_inst_831_, v_inst_832_, v_as_833_);
lean_dec_ref(v_as_833_);
lean_dec(v_inst_832_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object* v_resolve_835_, lean_object* v_pkg_836_, lean_object* v_dep_837_, lean_object* v_ws_838_, lean_object* v_toBind_839_, lean_object* v___f_840_, lean_object* v_____r_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_apply_3(v_resolve_835_, v_pkg_836_, v_dep_837_, v_ws_838_);
v___x_843_ = lean_apply_4(v_toBind_839_, lean_box(0), lean_box(0), v___x_842_, v___f_840_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object* v_start_844_, lean_object* v_s_845_, lean_object* v_opts_846_, lean_object* v_leanOpts_847_, uint8_t v_reconfigure_848_, lean_object* v_inst_849_, lean_object* v_matDep_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_box(v_reconfigure_848_);
v___x_852_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed), 8, 6);
lean_closure_set(v___x_852_, 0, v_start_844_);
lean_closure_set(v___x_852_, 1, v_s_845_);
lean_closure_set(v___x_852_, 2, v_matDep_850_);
lean_closure_set(v___x_852_, 3, v_opts_846_);
lean_closure_set(v___x_852_, 4, v_leanOpts_847_);
lean_closure_set(v___x_852_, 5, v___x_851_);
v___x_853_ = lean_apply_2(v_inst_849_, lean_box(0), v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object* v_start_854_, lean_object* v_s_855_, lean_object* v_opts_856_, lean_object* v_leanOpts_857_, lean_object* v_reconfigure_858_, lean_object* v_inst_859_, lean_object* v_matDep_860_){
_start:
{
uint8_t v_reconfigure_boxed_861_; lean_object* v_res_862_; 
v_reconfigure_boxed_861_ = lean_unbox(v_reconfigure_858_);
v_res_862_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(v_start_854_, v_s_855_, v_opts_856_, v_leanOpts_857_, v_reconfigure_boxed_861_, v_inst_859_, v_matDep_860_);
return v_res_862_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object* v_dep_863_, lean_object* v_x_864_){
_start:
{
lean_object* v_baseName_865_; lean_object* v_name_866_; uint8_t v___x_867_; 
v_baseName_865_ = lean_ctor_get(v_x_864_, 1);
v_name_866_ = lean_ctor_get(v_dep_863_, 0);
v___x_867_ = lean_name_eq(v_baseName_865_, v_name_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed(lean_object* v_dep_868_, lean_object* v_x_869_){
_start:
{
uint8_t v_res_870_; lean_object* v_r_871_; 
v_res_870_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(v_dep_868_, v_x_869_);
lean_dec_ref(v_x_869_);
lean_dec_ref(v_dep_868_);
v_r_871_ = lean_box(v_res_870_);
return v_r_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object* v___f_872_, lean_object* v_____r_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = lean_apply_1(v___f_872_, v_____r_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object* v_toPure_876_, lean_object* v_start_877_, lean_object* v_leanOpts_878_, uint8_t v_reconfigure_879_, lean_object* v_inst_880_, lean_object* v_resolve_881_, lean_object* v_pkg_882_, lean_object* v_toBind_883_, lean_object* v_baseName_884_, lean_object* v_inst_885_, lean_object* v_dep_886_, lean_object* v_s_887_){
_start:
{
lean_object* v_ws_888_; lean_object* v_depIdxs_889_; lean_object* v_packages_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_ws_888_ = lean_ctor_get(v_s_887_, 0);
lean_inc_ref(v_ws_888_);
v_depIdxs_889_ = lean_ctor_get(v_s_887_, 1);
v_packages_890_ = lean_ctor_get(v_ws_888_, 4);
lean_inc_ref(v_dep_886_);
v___f_891_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_891_, 0, v_dep_886_);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_891_, v_packages_890_, v___x_892_);
if (lean_obj_tag(v___x_893_) == 1)
{
lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_903_; 
lean_inc_ref(v_depIdxs_889_);
lean_dec_ref(v_dep_886_);
lean_dec(v_inst_885_);
lean_dec(v_baseName_884_);
lean_dec(v_toBind_883_);
lean_dec_ref(v_pkg_882_);
lean_dec(v_resolve_881_);
lean_dec(v_inst_880_);
lean_dec_ref(v_leanOpts_878_);
lean_dec(v_start_877_);
v_isSharedCheck_903_ = !lean_is_exclusive(v_s_887_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; lean_object* v_unused_905_; 
v_unused_904_ = lean_ctor_get(v_s_887_, 1);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v_s_887_, 0);
lean_dec(v_unused_905_);
v___x_895_ = v_s_887_;
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
else
{
lean_dec(v_s_887_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_val_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v_val_897_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v___x_893_, 1);
v___x_898_ = lean_array_push(v_depIdxs_889_, v_val_897_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v___x_898_);
v___x_900_ = v___x_895_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_ws_888_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_898_);
v___x_900_ = v_reuseFailAlloc_902_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = lean_apply_2(v_toPure_876_, lean_box(0), v___x_900_);
return v___x_901_;
}
}
}
else
{
lean_object* v_name_906_; lean_object* v_opts_907_; lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___f_910_; uint8_t v___x_911_; 
lean_dec(v___x_893_);
lean_dec(v_toPure_876_);
v_name_906_ = lean_ctor_get(v_dep_886_, 0);
v_opts_907_ = lean_ctor_get(v_dep_886_, 4);
v___x_908_ = lean_box(v_reconfigure_879_);
lean_inc(v_opts_907_);
v___f_909_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_909_, 0, v_start_877_);
lean_closure_set(v___f_909_, 1, v_s_887_);
lean_closure_set(v___f_909_, 2, v_opts_907_);
lean_closure_set(v___f_909_, 3, v_leanOpts_878_);
lean_closure_set(v___f_909_, 4, v___x_908_);
lean_closure_set(v___f_909_, 5, v_inst_880_);
lean_inc_ref(v___f_909_);
lean_inc(v_toBind_883_);
lean_inc_ref(v_ws_888_);
lean_inc_ref(v_dep_886_);
lean_inc_ref(v_pkg_882_);
lean_inc(v_resolve_881_);
v___f_910_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4), 7, 6);
lean_closure_set(v___f_910_, 0, v_resolve_881_);
lean_closure_set(v___f_910_, 1, v_pkg_882_);
lean_closure_set(v___f_910_, 2, v_dep_886_);
lean_closure_set(v___f_910_, 3, v_ws_888_);
lean_closure_set(v___f_910_, 4, v_toBind_883_);
lean_closure_set(v___f_910_, 5, v___f_909_);
v___x_911_ = lean_name_eq(v_baseName_884_, v_name_906_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec_ref(v___f_910_);
lean_dec(v_inst_885_);
lean_dec(v_baseName_884_);
v___x_912_ = lean_box(0);
v___x_913_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(v_resolve_881_, v_pkg_882_, v_dep_886_, v_ws_888_, v_toBind_883_, v___f_909_, v___x_912_);
return v___x_913_;
}
else
{
lean_object* v___f_914_; uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec_ref(v___f_909_);
lean_dec_ref(v_ws_888_);
lean_dec_ref(v_dep_886_);
lean_dec_ref(v_pkg_882_);
lean_dec(v_resolve_881_);
v___f_914_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5), 2, 1);
lean_closure_set(v___f_914_, 0, v___f_910_);
v___x_915_ = 0;
v___x_916_ = l_Lean_Name_toString(v_baseName_884_, v___x_915_);
v___x_917_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_918_ = lean_string_append(v___x_916_, v___x_917_);
v___x_919_ = lean_apply_2(v_inst_885_, lean_box(0), v___x_918_);
v___x_920_ = lean_apply_4(v_toBind_883_, lean_box(0), lean_box(0), v___x_919_, v___f_914_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object* v_toPure_921_, lean_object* v_start_922_, lean_object* v_leanOpts_923_, lean_object* v_reconfigure_924_, lean_object* v_inst_925_, lean_object* v_resolve_926_, lean_object* v_pkg_927_, lean_object* v_toBind_928_, lean_object* v_baseName_929_, lean_object* v_inst_930_, lean_object* v_dep_931_, lean_object* v_s_932_){
_start:
{
uint8_t v_reconfigure_boxed_933_; lean_object* v_res_934_; 
v_reconfigure_boxed_933_ = lean_unbox(v_reconfigure_924_);
v_res_934_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(v_toPure_921_, v_start_922_, v_leanOpts_923_, v_reconfigure_boxed_933_, v_inst_925_, v_resolve_926_, v_pkg_927_, v_toBind_928_, v_baseName_929_, v_inst_930_, v_dep_931_, v_s_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0___boxed(lean_object* v_next_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_resolve_939_, lean_object* v_leanOpts_940_, lean_object* v_reconfigure_941_, lean_object* v_ws_942_, lean_object* v_____x_943_){
_start:
{
uint8_t v_reconfigure_boxed_944_; lean_object* v_res_945_; 
v_reconfigure_boxed_944_ = lean_unbox(v_reconfigure_941_);
v_res_945_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(v_next_935_, v_inst_936_, v_inst_937_, v_inst_938_, v_resolve_939_, v_leanOpts_940_, v_reconfigure_boxed_944_, v_ws_942_, v_____x_943_);
lean_dec(v_next_935_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object* v_pkg_946_, lean_object* v_next_947_, lean_object* v_toPure_948_, lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_resolve_952_, lean_object* v_leanOpts_953_, uint8_t v_reconfigure_954_, lean_object* v_toBind_955_, lean_object* v_____x_956_){
_start:
{
lean_object* v_ws_957_; lean_object* v_depIdxs_958_; lean_object* v_ws_959_; lean_object* v_packages_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_ws_957_ = lean_ctor_get(v_____x_956_, 0);
lean_inc_ref(v_ws_957_);
v_depIdxs_958_ = lean_ctor_get(v_____x_956_, 1);
lean_inc_ref(v_depIdxs_958_);
lean_dec_ref(v_____x_956_);
v_ws_959_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_957_, v_pkg_946_, v_depIdxs_958_);
v_packages_960_ = lean_ctor_get(v_ws_959_, 4);
v___x_961_ = lean_array_get_size(v_packages_960_);
v___x_962_ = lean_nat_dec_lt(v_next_947_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec(v_toBind_955_);
lean_dec_ref(v_leanOpts_953_);
lean_dec(v_resolve_952_);
lean_dec(v_inst_951_);
lean_dec(v_inst_950_);
lean_dec_ref(v_inst_949_);
lean_dec(v_next_947_);
v___x_963_ = lean_apply_2(v_toPure_948_, lean_box(0), v_ws_959_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v___f_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_964_ = lean_box(v_reconfigure_954_);
v___f_965_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_965_, 0, v_next_947_);
lean_closure_set(v___f_965_, 1, v_inst_949_);
lean_closure_set(v___f_965_, 2, v_inst_950_);
lean_closure_set(v___f_965_, 3, v_inst_951_);
lean_closure_set(v___f_965_, 4, v_resolve_952_);
lean_closure_set(v___f_965_, 5, v_leanOpts_953_);
lean_closure_set(v___f_965_, 6, v___x_964_);
lean_closure_set(v___f_965_, 7, v_ws_959_);
v___x_966_ = lean_apply_2(v_toPure_948_, lean_box(0), lean_box(0));
v___x_967_ = lean_apply_4(v_toBind_955_, lean_box(0), lean_box(0), v___x_966_, v___f_965_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed(lean_object* v_pkg_968_, lean_object* v_next_969_, lean_object* v_toPure_970_, lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_resolve_974_, lean_object* v_leanOpts_975_, lean_object* v_reconfigure_976_, lean_object* v_toBind_977_, lean_object* v_____x_978_){
_start:
{
uint8_t v_reconfigure_boxed_979_; lean_object* v_res_980_; 
v_reconfigure_boxed_979_ = lean_unbox(v_reconfigure_976_);
v_res_980_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(v_pkg_968_, v_next_969_, v_toPure_970_, v_inst_971_, v_inst_972_, v_inst_973_, v_resolve_974_, v_leanOpts_975_, v_reconfigure_boxed_979_, v_toBind_977_, v_____x_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_resolve_984_, lean_object* v_leanOpts_985_, uint8_t v_reconfigure_986_, lean_object* v_ws_987_, lean_object* v_i_988_, lean_object* v_next_989_){
_start:
{
lean_object* v_packages_990_; lean_object* v_pkg_991_; lean_object* v_toApplicative_992_; lean_object* v_baseName_993_; lean_object* v_depConfigs_994_; lean_object* v_toBind_995_; lean_object* v_toPure_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v_s_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v_packages_990_ = lean_ctor_get(v_ws_987_, 4);
lean_inc_ref(v_packages_990_);
v_pkg_991_ = lean_array_fget(v_packages_990_, v_i_988_);
v_toApplicative_992_ = lean_ctor_get(v_inst_981_, 0);
v_baseName_993_ = lean_ctor_get(v_pkg_991_, 1);
lean_inc(v_baseName_993_);
v_depConfigs_994_ = lean_ctor_get(v_pkg_991_, 12);
lean_inc_ref(v_depConfigs_994_);
v_toBind_995_ = lean_ctor_get(v_inst_981_, 1);
lean_inc_n(v_toBind_995_, 2);
v_toPure_996_ = lean_ctor_get(v_toApplicative_992_, 1);
v___x_997_ = lean_array_get_size(v_depConfigs_994_);
v___x_998_ = lean_mk_empty_array_with_capacity(v___x_997_);
v_s_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_999_, 0, v_ws_987_);
lean_ctor_set(v_s_999_, 1, v___x_998_);
v___x_1000_ = lean_box(v_reconfigure_986_);
lean_inc_ref(v_leanOpts_985_);
lean_inc(v_resolve_984_);
lean_inc(v_inst_983_);
lean_inc(v_inst_982_);
lean_inc_ref(v_inst_981_);
lean_inc(v_toPure_996_);
lean_inc(v_pkg_991_);
v___f_1001_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_1001_, 0, v_pkg_991_);
lean_closure_set(v___f_1001_, 1, v_next_989_);
lean_closure_set(v___f_1001_, 2, v_toPure_996_);
lean_closure_set(v___f_1001_, 3, v_inst_981_);
lean_closure_set(v___f_1001_, 4, v_inst_982_);
lean_closure_set(v___f_1001_, 5, v_inst_983_);
lean_closure_set(v___f_1001_, 6, v_resolve_984_);
lean_closure_set(v___f_1001_, 7, v_leanOpts_985_);
lean_closure_set(v___f_1001_, 8, v___x_1000_);
lean_closure_set(v___f_1001_, 9, v_toBind_995_);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_nat_dec_lt(v___x_1002_, v___x_997_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_inc(v_toPure_996_);
lean_dec_ref(v_depConfigs_994_);
lean_dec(v_baseName_993_);
lean_dec(v_pkg_991_);
lean_dec_ref(v_packages_990_);
lean_dec_ref(v_leanOpts_985_);
lean_dec(v_resolve_984_);
lean_dec(v_inst_983_);
lean_dec(v_inst_982_);
lean_dec_ref(v_inst_981_);
v___x_1004_ = lean_apply_2(v_toPure_996_, lean_box(0), v_s_999_);
v___x_1005_ = lean_apply_4(v_toBind_995_, lean_box(0), lean_box(0), v___x_1004_, v___f_1001_);
return v___x_1005_;
}
else
{
lean_object* v_start_1006_; lean_object* v___x_1007_; lean_object* v___f_1008_; size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_start_1006_ = lean_array_get_size(v_packages_990_);
lean_dec_ref(v_packages_990_);
v___x_1007_ = lean_box(v_reconfigure_986_);
lean_inc(v_toBind_995_);
lean_inc(v_toPure_996_);
v___f_1008_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed), 12, 10);
lean_closure_set(v___f_1008_, 0, v_toPure_996_);
lean_closure_set(v___f_1008_, 1, v_start_1006_);
lean_closure_set(v___f_1008_, 2, v_leanOpts_985_);
lean_closure_set(v___f_1008_, 3, v___x_1007_);
lean_closure_set(v___f_1008_, 4, v_inst_983_);
lean_closure_set(v___f_1008_, 5, v_resolve_984_);
lean_closure_set(v___f_1008_, 6, v_pkg_991_);
lean_closure_set(v___f_1008_, 7, v_toBind_995_);
lean_closure_set(v___f_1008_, 8, v_baseName_993_);
lean_closure_set(v___f_1008_, 9, v_inst_982_);
v___x_1009_ = lean_usize_of_nat(v___x_997_);
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_981_, v___f_1008_, v_depConfigs_994_, v___x_1009_, v___x_1010_, v_s_999_);
v___x_1012_ = lean_apply_4(v_toBind_995_, lean_box(0), lean_box(0), v___x_1011_, v___f_1001_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object* v_next_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_resolve_1017_, lean_object* v_leanOpts_1018_, uint8_t v_reconfigure_1019_, lean_object* v_ws_1020_, lean_object* v_____x_1021_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_nat_add(v_next_1013_, v___x_1022_);
v___x_1024_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1014_, v_inst_1015_, v_inst_1016_, v_resolve_1017_, v_leanOpts_1018_, v_reconfigure_1019_, v_ws_1020_, v_next_1013_, v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_resolve_1028_, lean_object* v_leanOpts_1029_, lean_object* v_reconfigure_1030_, lean_object* v_ws_1031_, lean_object* v_i_1032_, lean_object* v_next_1033_){
_start:
{
uint8_t v_reconfigure_boxed_1034_; lean_object* v_res_1035_; 
v_reconfigure_boxed_1034_ = lean_unbox(v_reconfigure_1030_);
v_res_1035_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1025_, v_inst_1026_, v_inst_1027_, v_resolve_1028_, v_leanOpts_1029_, v_reconfigure_boxed_1034_, v_ws_1031_, v_i_1032_, v_next_1033_);
lean_dec(v_i_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* v_m_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_resolve_1040_, lean_object* v_leanOpts_1041_, uint8_t v_reconfigure_1042_, lean_object* v_ws_1043_, lean_object* v_i_1044_, lean_object* v_i__lt_1045_, lean_object* v_next_1046_, lean_object* v_lt__next_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1037_, v_inst_1038_, v_inst_1039_, v_resolve_1040_, v_leanOpts_1041_, v_reconfigure_1042_, v_ws_1043_, v_i_1044_, v_next_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object* v_m_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_resolve_1053_, lean_object* v_leanOpts_1054_, lean_object* v_reconfigure_1055_, lean_object* v_ws_1056_, lean_object* v_i_1057_, lean_object* v_i__lt_1058_, lean_object* v_next_1059_, lean_object* v_lt__next_1060_){
_start:
{
uint8_t v_reconfigure_boxed_1061_; lean_object* v_res_1062_; 
v_reconfigure_boxed_1061_ = lean_unbox(v_reconfigure_1055_);
v_res_1062_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(v_m_1049_, v_inst_1050_, v_inst_1051_, v_inst_1052_, v_resolve_1053_, v_leanOpts_1054_, v_reconfigure_boxed_1061_, v_ws_1056_, v_i_1057_, v_i__lt_1058_, v_next_1059_, v_lt__next_1060_);
lean_dec(v_i_1057_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___redArg(lean_object* v_x_1063_, lean_object* v_h__1_1064_, lean_object* v_h__2_1065_){
_start:
{
if (lean_obj_tag(v_x_1063_) == 1)
{
lean_object* v_val_1066_; lean_object* v___x_1067_; 
lean_dec(v_h__2_1065_);
v_val_1066_ = lean_ctor_get(v_x_1063_, 0);
lean_inc(v_val_1066_);
lean_dec_ref_known(v_x_1063_, 1);
v___x_1067_ = lean_apply_1(v_h__1_1064_, v_val_1066_);
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; 
lean_dec(v_h__1_1064_);
v___x_1068_ = lean_apply_2(v_h__2_1065_, v_x_1063_, lean_box(0));
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(lean_object* v_ws_1069_, lean_object* v_s_1070_, lean_object* v_motive_1071_, lean_object* v_x_1072_, lean_object* v_h__1_1073_, lean_object* v_h__2_1074_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 1)
{
lean_object* v_val_1075_; lean_object* v___x_1076_; 
lean_dec(v_h__2_1074_);
v_val_1075_ = lean_ctor_get(v_x_1072_, 0);
lean_inc(v_val_1075_);
lean_dec_ref_known(v_x_1072_, 1);
v___x_1076_ = lean_apply_1(v_h__1_1073_, v_val_1075_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; 
lean_dec(v_h__1_1073_);
v___x_1077_ = lean_apply_2(v_h__2_1074_, v_x_1072_, lean_box(0));
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___boxed(lean_object* v_ws_1078_, lean_object* v_s_1079_, lean_object* v_motive_1080_, lean_object* v_x_1081_, lean_object* v_h__1_1082_, lean_object* v_h__2_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(v_ws_1078_, v_s_1079_, v_motive_1080_, v_x_1081_, v_h__1_1082_, v_h__2_1083_);
lean_dec_ref(v_s_1079_);
lean_dec_ref(v_ws_1078_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___redArg(lean_object* v_x_1085_, lean_object* v_h__1_1086_){
_start:
{
lean_object* v_ws_1087_; lean_object* v_depIdxs_1088_; lean_object* v___x_1089_; 
v_ws_1087_ = lean_ctor_get(v_x_1085_, 0);
lean_inc_ref(v_ws_1087_);
v_depIdxs_1088_ = lean_ctor_get(v_x_1085_, 1);
lean_inc_ref(v_depIdxs_1088_);
lean_dec_ref(v_x_1085_);
v___x_1089_ = lean_apply_4(v_h__1_1086_, v_ws_1087_, v_depIdxs_1088_, lean_box(0), lean_box(0));
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(lean_object* v_ws_1090_, lean_object* v_motive_1091_, lean_object* v_x_1092_, lean_object* v_h__1_1093_){
_start:
{
lean_object* v_ws_1094_; lean_object* v_depIdxs_1095_; lean_object* v___x_1096_; 
v_ws_1094_ = lean_ctor_get(v_x_1092_, 0);
lean_inc_ref(v_ws_1094_);
v_depIdxs_1095_ = lean_ctor_get(v_x_1092_, 1);
lean_inc_ref(v_depIdxs_1095_);
lean_dec_ref(v_x_1092_);
v___x_1096_ = lean_apply_4(v_h__1_1093_, v_ws_1094_, v_depIdxs_1095_, lean_box(0), lean_box(0));
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___boxed(lean_object* v_ws_1097_, lean_object* v_motive_1098_, lean_object* v_x_1099_, lean_object* v_h__1_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(v_ws_1097_, v_motive_1098_, v_x_1099_, v_h__1_1100_);
lean_dec_ref(v_ws_1097_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___redArg(lean_object* v_h__1_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_apply_1(v_h__1_1102_, lean_box(0));
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(lean_object* v_ws_1104_, lean_object* v_motive_1105_, lean_object* v_x_1106_, lean_object* v_h__1_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_apply_1(v_h__1_1107_, lean_box(0));
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___boxed(lean_object* v_ws_1109_, lean_object* v_motive_1110_, lean_object* v_x_1111_, lean_object* v_h__1_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(v_ws_1109_, v_motive_1110_, v_x_1111_, v_h__1_1112_);
lean_dec_ref(v_ws_1109_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_ws_1118_, lean_object* v_resolve_1119_, lean_object* v_root_1120_, lean_object* v_next_1121_, lean_object* v_leanOpts_1122_, uint8_t v_reconfigure_1123_){
_start:
{
lean_object* v_toApplicative_1124_; lean_object* v_toFunctor_1125_; lean_object* v_map_1126_; lean_object* v___f_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_toApplicative_1124_ = lean_ctor_get(v_inst_1115_, 0);
v_toFunctor_1125_ = lean_ctor_get(v_toApplicative_1124_, 0);
v_map_1126_ = lean_ctor_get(v_toFunctor_1125_, 0);
lean_inc(v_map_1126_);
v___f_1127_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0));
v___x_1128_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1115_, v_inst_1116_, v_inst_1117_, v_resolve_1119_, v_leanOpts_1122_, v_reconfigure_1123_, v_ws_1118_, v_root_1120_, v_next_1121_);
v___x_1129_ = lean_apply_4(v_map_1126_, lean_box(0), lean_box(0), v___f_1127_, v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_ws_1133_, lean_object* v_resolve_1134_, lean_object* v_root_1135_, lean_object* v_next_1136_, lean_object* v_leanOpts_1137_, lean_object* v_reconfigure_1138_){
_start:
{
uint8_t v_reconfigure_boxed_1139_; lean_object* v_res_1140_; 
v_reconfigure_boxed_1139_ = lean_unbox(v_reconfigure_1138_);
v_res_1140_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(v_inst_1130_, v_inst_1131_, v_inst_1132_, v_ws_1133_, v_resolve_1134_, v_root_1135_, v_next_1136_, v_leanOpts_1137_, v_reconfigure_boxed_1139_);
lean_dec(v_root_1135_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* v_m_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_ws_1145_, lean_object* v_resolve_1146_, lean_object* v_root_1147_, lean_object* v_root__lt_1148_, lean_object* v_next_1149_, lean_object* v_next__lt_1150_, lean_object* v_leanOpts_1151_, uint8_t v_reconfigure_1152_){
_start:
{
lean_object* v_toApplicative_1153_; lean_object* v_toFunctor_1154_; lean_object* v_map_1155_; lean_object* v___f_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_toApplicative_1153_ = lean_ctor_get(v_inst_1142_, 0);
v_toFunctor_1154_ = lean_ctor_get(v_toApplicative_1153_, 0);
v_map_1155_ = lean_ctor_get(v_toFunctor_1154_, 0);
lean_inc(v_map_1155_);
v___f_1156_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___closed__0));
v___x_1157_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1142_, v_inst_1143_, v_inst_1144_, v_resolve_1146_, v_leanOpts_1151_, v_reconfigure_1152_, v_ws_1145_, v_root_1147_, v_next_1149_);
v___x_1158_ = lean_apply_4(v_map_1155_, lean_box(0), lean_box(0), v___f_1156_, v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object* v_m_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_ws_1163_, lean_object* v_resolve_1164_, lean_object* v_root_1165_, lean_object* v_root__lt_1166_, lean_object* v_next_1167_, lean_object* v_next__lt_1168_, lean_object* v_leanOpts_1169_, lean_object* v_reconfigure_1170_){
_start:
{
uint8_t v_reconfigure_boxed_1171_; lean_object* v_res_1172_; 
v_reconfigure_boxed_1171_ = lean_unbox(v_reconfigure_1170_);
v_res_1172_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(v_m_1159_, v_inst_1160_, v_inst_1161_, v_inst_1162_, v_ws_1163_, v_resolve_1164_, v_root_1165_, v_root__lt_1166_, v_next_1167_, v_next__lt_1168_, v_leanOpts_1169_, v_reconfigure_boxed_1171_);
lean_dec(v_root_1165_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object* v_x_1173_, lean_object* v_init_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_apply_1(v_x_1173_, v_init_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object* v_m_1176_, lean_object* v_00_u03b1_1177_, lean_object* v_x_1178_, lean_object* v_init_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_apply_1(v_x_1178_, v_init_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(lean_object* v_as_1181_, size_t v_i_1182_, size_t v_stop_1183_, lean_object* v_b_1184_){
_start:
{
uint8_t v___x_1185_; 
v___x_1185_ = lean_usize_dec_eq(v_i_1182_, v_stop_1183_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v_name_1187_; lean_object* v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; 
v___x_1186_ = lean_array_uget_borrowed(v_as_1181_, v_i_1182_);
v_name_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_name_1187_);
v___x_1188_ = l_Lean_NameSet_insert(v_b_1184_, v_name_1187_);
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_add(v_i_1182_, v___x_1189_);
v_i_1182_ = v___x_1190_;
v_b_1184_ = v___x_1188_;
goto _start;
}
else
{
return v_b_1184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2___boxed(lean_object* v_as_1192_, lean_object* v_i_1193_, lean_object* v_stop_1194_, lean_object* v_b_1195_){
_start:
{
size_t v_i_boxed_1196_; size_t v_stop_boxed_1197_; lean_object* v_res_1198_; 
v_i_boxed_1196_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_stop_boxed_1197_ = lean_unbox_usize(v_stop_1194_);
lean_dec(v_stop_1194_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_as_1192_, v_i_boxed_1196_, v_stop_boxed_1197_, v_b_1195_);
lean_dec_ref(v_as_1192_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(lean_object* v_as_1199_, size_t v_sz_1200_, size_t v_i_1201_, lean_object* v_b_1202_, lean_object* v___y_1203_){
_start:
{
uint8_t v___x_1205_; 
v___x_1205_ = lean_usize_dec_lt(v_i_1201_, v_sz_1200_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_b_1202_);
lean_ctor_set(v___x_1206_, 1, v___y_1203_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
else
{
lean_object* v_a_1208_; lean_object* v_name_1209_; lean_object* v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; 
v_a_1208_ = lean_array_uget_borrowed(v_as_1199_, v_i_1201_);
v_name_1209_ = lean_ctor_get(v_a_1208_, 0);
lean_inc(v_name_1209_);
v___x_1210_ = l_Lean_NameSet_insert(v_b_1202_, v_name_1209_);
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_add(v_i_1201_, v___x_1211_);
v_i_1201_ = v___x_1212_;
v_b_1202_ = v___x_1210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg___boxed(lean_object* v_as_1214_, lean_object* v_sz_1215_, lean_object* v_i_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
size_t v_sz_boxed_1220_; size_t v_i_boxed_1221_; lean_object* v_res_1222_; 
v_sz_boxed_1220_ = lean_unbox_usize(v_sz_1215_);
lean_dec(v_sz_1215_);
v_i_boxed_1221_ = lean_unbox_usize(v_i_1216_);
lean_dec(v_i_1216_);
v_res_1222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1214_, v_sz_boxed_1220_, v_i_boxed_1221_, v_b_1217_, v___y_1218_);
lean_dec_ref(v_as_1214_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_fst_1225_, lean_object* v_init_1226_, lean_object* v_x_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 0)
{
lean_object* v_k_1231_; lean_object* v_l_1232_; lean_object* v_r_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_k_1231_ = lean_ctor_get(v_x_1227_, 1);
lean_inc(v_k_1231_);
v_l_1232_ = lean_ctor_get(v_x_1227_, 3);
lean_inc(v_l_1232_);
v_r_1233_ = lean_ctor_get(v_x_1227_, 4);
lean_inc(v_r_1233_);
lean_dec_ref_known(v_x_1227_, 5);
v___x_1234_ = lean_box(0);
v___x_1235_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1225_, v_init_1226_, v_l_1232_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1254_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1254_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1254_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_snd_1240_; uint8_t v___x_1241_; 
v_snd_1240_ = lean_ctor_get(v_a_1236_, 1);
lean_inc(v_snd_1240_);
lean_dec(v_a_1236_);
v___x_1241_ = l_Lean_NameSet_contains(v_fst_1225_, v_k_1231_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_dec(v_snd_1240_);
lean_dec(v_r_1233_);
v___x_1242_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__0));
v___x_1243_ = l_Lean_Name_toString(v_k_1231_, v___x_1241_);
v___x_1244_ = lean_string_append(v___x_1242_, v___x_1243_);
lean_dec_ref(v___x_1243_);
v___x_1245_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___closed__1));
v___x_1246_ = lean_string_append(v___x_1244_, v___x_1245_);
v___x_1247_ = 3;
v___x_1248_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set_uint8(v___x_1248_, sizeof(void*)*1, v___x_1247_);
lean_inc_ref(v___y_1229_);
v___x_1249_ = lean_apply_2(v___y_1229_, v___x_1248_, lean_box(0));
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 1);
lean_ctor_set(v___x_1238_, 0, v___x_1234_);
v___x_1251_ = v___x_1238_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1234_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
else
{
lean_del_object(v___x_1238_);
lean_dec(v_k_1231_);
v_init_1226_ = v___x_1234_;
v_x_1227_ = v_r_1233_;
v___y_1228_ = v_snd_1240_;
goto _start;
}
}
}
else
{
lean_dec(v_r_1233_);
lean_dec(v_k_1231_);
return v___x_1235_;
}
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_init_1226_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v___y_1228_);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_fst_1258_, lean_object* v_init_1259_, lean_object* v_x_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1258_, v_init_1259_, v_x_1260_, v___y_1261_, v___y_1262_);
lean_dec_ref(v___y_1262_);
lean_dec(v_fst_1258_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(lean_object* v_toUpdate_1265_, lean_object* v_depConfigs_1266_, lean_object* v___x_1267_, lean_object* v_entries_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___y_1273_; 
if (lean_obj_tag(v_toUpdate_1265_) == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1315_ = l_Lean_NameSet_empty;
v___x_1316_ = lean_array_get_size(v_depConfigs_1266_);
v___x_1317_ = lean_nat_dec_lt(v___x_1267_, v___x_1316_);
if (v___x_1317_ == 0)
{
v___y_1273_ = v___x_1315_;
goto v___jp_1272_;
}
else
{
size_t v___x_1318_; size_t v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = ((size_t)0ULL);
v___x_1319_ = lean_usize_of_nat(v___x_1316_);
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__2(v_depConfigs_1266_, v___x_1318_, v___x_1319_, v___x_1315_);
v___y_1273_ = v___x_1320_;
goto v___jp_1272_;
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v___y_1269_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
v___jp_1272_:
{
size_t v_sz_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v_sz_1274_ = lean_array_size(v_entries_1268_);
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_entries_1268_, v_sz_1274_, v___x_1275_, v___y_1273_, v___y_1269_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v_fst_1278_; lean_object* v_snd_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v_fst_1278_ = lean_ctor_get(v_a_1277_, 0);
lean_inc(v_fst_1278_);
v_snd_1279_ = lean_ctor_get(v_a_1277_, 1);
lean_inc(v_snd_1279_);
lean_dec(v_a_1277_);
v___x_1280_ = lean_box(0);
v___x_1281_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_fst_1278_, v___x_1280_, v_toUpdate_1265_, v_snd_1279_, v___y_1270_);
lean_dec(v_fst_1278_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1298_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1298_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1298_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_snd_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1296_; 
v_snd_1286_ = lean_ctor_get(v_a_1282_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_a_1282_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v_a_1282_, 0);
lean_dec(v_unused_1297_);
v___x_1288_ = v_a_1282_;
v_isShared_1289_ = v_isSharedCheck_1296_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_snd_1286_);
lean_dec(v_a_1282_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1296_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1280_);
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_snd_1286_);
v___x_1291_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1293_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1291_);
v___x_1293_ = v___x_1284_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
v_a_1299_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1281_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1281_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v_toUpdate_1265_);
v_a_1307_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1276_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1276_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0___boxed(lean_object* v_toUpdate_1324_, lean_object* v_depConfigs_1325_, lean_object* v___x_1326_, lean_object* v_entries_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1324_, v_depConfigs_1325_, v___x_1326_, v_entries_1327_, v___y_1328_, v___y_1329_);
lean_dec_ref(v___y_1329_);
lean_dec_ref(v_entries_1327_);
lean_dec(v___x_1326_);
lean_dec_ref(v_depConfigs_1325_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(lean_object* v_as_1332_, size_t v_i_1333_, size_t v_stop_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_usize_dec_eq(v_i_1333_, v_stop_1334_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; 
v___x_1339_ = lean_array_uget_borrowed(v_as_1332_, v_i_1333_);
lean_inc_ref(v___y_1336_);
lean_inc(v___x_1339_);
v___x_1340_ = lean_apply_2(v___y_1336_, v___x_1339_, lean_box(0));
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_add(v_i_1333_, v___x_1341_);
v_i_1333_ = v___x_1342_;
v_b_1335_ = v___x_1340_;
goto _start;
}
else
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_b_1335_);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3___boxed(lean_object* v_as_1345_, lean_object* v_i_1346_, lean_object* v_stop_1347_, lean_object* v_b_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
size_t v_i_boxed_1351_; size_t v_stop_boxed_1352_; lean_object* v_res_1353_; 
v_i_boxed_1351_ = lean_unbox_usize(v_i_1346_);
lean_dec(v_i_1346_);
v_stop_boxed_1352_ = lean_unbox_usize(v_stop_1347_);
lean_dec(v_stop_1347_);
v_res_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_as_1345_, v_i_boxed_1351_, v_stop_boxed_1352_, v_b_1348_, v___y_1349_);
lean_dec_ref(v___y_1349_);
lean_dec_ref(v_as_1345_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(lean_object* v_toUpdate_1354_, lean_object* v_as_1355_, size_t v_i_1356_, size_t v_stop_1357_, lean_object* v_b_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_fst_1362_; lean_object* v_snd_1363_; uint8_t v___x_1369_; 
v___x_1369_ = lean_usize_dec_eq(v_i_1356_, v_stop_1357_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; uint8_t v_inherited_1371_; 
v___x_1370_ = lean_array_uget_borrowed(v_as_1355_, v_i_1356_);
v_inherited_1371_ = lean_ctor_get_uint8(v___x_1370_, sizeof(void*)*5);
if (v_inherited_1371_ == 0)
{
lean_object* v_name_1372_; uint8_t v___x_1373_; 
v_name_1372_ = lean_ctor_get(v___x_1370_, 0);
v___x_1373_ = l_Lean_NameSet_contains(v_toUpdate_1354_, v_name_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_box(0);
lean_inc(v___x_1370_);
lean_inc(v_name_1372_);
v___x_1375_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1372_, v___x_1370_, v___y_1359_);
v_fst_1362_ = v___x_1374_;
v_snd_1363_ = v___x_1375_;
goto v___jp_1361_;
}
else
{
goto v___jp_1367_;
}
}
else
{
goto v___jp_1367_;
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_b_1358_);
lean_ctor_set(v___x_1376_, 1, v___y_1359_);
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
v___jp_1361_:
{
size_t v___x_1364_; size_t v___x_1365_; 
v___x_1364_ = ((size_t)1ULL);
v___x_1365_ = lean_usize_add(v_i_1356_, v___x_1364_);
v_i_1356_ = v___x_1365_;
v_b_1358_ = v_fst_1362_;
v___y_1359_ = v_snd_1363_;
goto _start;
}
v___jp_1367_:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_box(0);
v_fst_1362_ = v___x_1368_;
v_snd_1363_ = v___y_1359_;
goto v___jp_1361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg___boxed(lean_object* v_toUpdate_1378_, lean_object* v_as_1379_, lean_object* v_i_1380_, lean_object* v_stop_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
size_t v_i_boxed_1385_; size_t v_stop_boxed_1386_; lean_object* v_res_1387_; 
v_i_boxed_1385_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_stop_boxed_1386_ = lean_unbox_usize(v_stop_1381_);
lean_dec(v_stop_1381_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1378_, v_as_1379_, v_i_boxed_1385_, v_stop_boxed_1386_, v_b_1382_, v___y_1383_);
lean_dec_ref(v_as_1379_);
lean_dec(v_toUpdate_1378_);
return v_res_1387_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1395_ = lean_array_get_size(v___x_1394_);
return v___x_1395_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1396_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_nat_dec_lt(v___x_1397_, v___x_1396_);
return v___x_1398_;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7(void){
_start:
{
lean_object* v___x_1399_; size_t v___x_1400_; 
v___x_1399_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1400_ = lean_usize_of_nat(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* v_ws_1403_, lean_object* v_toUpdate_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___y_1409_; lean_object* v___y_1414_; lean_object* v_fst_1415_; lean_object* v_snd_1416_; lean_object* v_packages_1435_; lean_object* v___x_1436_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v_val_1441_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v_a_1460_; lean_object* v___x_1462_; lean_object* v_baseName_1463_; lean_object* v_dir_1464_; lean_object* v_config_1465_; lean_object* v_relManifestFile_1466_; lean_object* v_depConfigs_1467_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; uint8_t v_fst_1472_; lean_object* v_snd_1473_; lean_object* v_packagesDir_x3f_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; uint8_t v___x_1527_; lean_object* v_rootName_1528_; lean_object* v_fst_1530_; lean_object* v_snd_1531_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v_val_1598_; lean_object* v___x_1612_; 
v_packages_1435_ = lean_ctor_get(v_ws_1403_, 4);
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_array_fget_borrowed(v_packages_1435_, v___x_1436_);
v_baseName_1463_ = lean_ctor_get(v___x_1462_, 1);
v_dir_1464_ = lean_ctor_get(v___x_1462_, 4);
v_config_1465_ = lean_ctor_get(v___x_1462_, 6);
v_relManifestFile_1466_ = lean_ctor_get(v___x_1462_, 9);
v_depConfigs_1467_ = lean_ctor_get(v___x_1462_, 12);
v___x_1527_ = 0;
lean_inc(v_baseName_1463_);
v_rootName_1528_ = l_Lean_Name_toString(v_baseName_1463_, v___x_1527_);
lean_inc_ref(v_relManifestFile_1466_);
lean_inc_ref(v_dir_1464_);
v___x_1595_ = l_Lake_joinRelative(v_dir_1464_, v_relManifestFile_1466_);
v___x_1596_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1612_ = l_Lake_Manifest_load(v___x_1595_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set_tag(v___x_1615_, 1);
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
v_val_1598_ = v___x_1618_;
goto v___jp_1597_;
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
v_a_1621_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1612_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1612_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set_tag(v___x_1623_, 0);
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
v_val_1598_ = v___x_1626_;
goto v___jp_1597_;
}
}
}
v___jp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = lean_box(0);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___y_1409_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
v___jp_1413_:
{
if (lean_obj_tag(v_fst_1415_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_snd_1416_);
v_a_1417_ = lean_ctor_get(v_fst_1415_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_fst_1415_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1419_ = v_fst_1415_;
v_isShared_1420_ = v_isSharedCheck_1431_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v_fst_1415_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1431_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1421_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_1422_ = lean_io_error_to_string(v_a_1417_);
v___x_1423_ = lean_string_append(v___x_1421_, v___x_1422_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = 3;
v___x_1425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set_uint8(v___x_1425_, sizeof(void*)*1, v___x_1424_);
lean_inc_ref(v___y_1414_);
v___x_1426_ = lean_apply_2(v___y_1414_, v___x_1425_, lean_box(0));
v___x_1427_ = lean_box(0);
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 1);
lean_ctor_set(v___x_1419_, 0, v___x_1427_);
v___x_1429_ = v___x_1419_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec_ref(v_fst_1415_);
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v_snd_1416_);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
v___jp_1437_:
{
lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1442_ = lean_array_get_size(v___y_1438_);
v___x_1443_ = lean_nat_dec_lt(v___x_1436_, v___x_1442_);
if (v___x_1443_ == 0)
{
v___y_1414_ = v___y_1439_;
v_fst_1415_ = v_val_1441_;
v_snd_1416_ = v___y_1440_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; lean_object* v___x_1447_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = ((size_t)0ULL);
v___x_1446_ = lean_usize_of_nat(v___x_1442_);
v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1438_, v___x_1445_, v___x_1446_, v___x_1444_, v___y_1439_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_dec_ref_known(v___x_1447_, 1);
v___y_1414_ = v___y_1439_;
v_fst_1415_ = v_val_1441_;
v_snd_1416_ = v___y_1440_;
goto v___jp_1413_;
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec_ref(v_val_1441_);
lean_dec(v___y_1440_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
v___jp_1456_:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_a_1460_);
v___y_1438_ = v___y_1457_;
v___y_1439_ = v___y_1458_;
v___y_1440_ = v___y_1459_;
v_val_1441_ = v___x_1461_;
goto v___jp_1437_;
}
v___jp_1468_:
{
lean_object* v_toWorkspaceConfig_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v_toWorkspaceConfig_1474_ = lean_ctor_get(v_config_1465_, 0);
v___x_1475_ = l_System_FilePath_normalize(v___y_1469_);
lean_inc_ref(v_toWorkspaceConfig_1474_);
v___x_1476_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1474_);
lean_inc_ref(v___x_1476_);
v___x_1477_ = l_System_FilePath_normalize(v___x_1476_);
v___x_1478_ = lean_string_dec_eq(v___x_1475_, v___x_1477_);
lean_dec_ref(v___x_1477_);
lean_dec_ref(v___x_1475_);
if (v___x_1478_ == 0)
{
if (v_fst_1472_ == 0)
{
lean_dec_ref(v___x_1476_);
lean_dec_ref(v___y_1471_);
v___y_1409_ = v_snd_1473_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1479_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_1480_ = lean_string_append(v___x_1479_, v___y_1471_);
v___x_1481_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_1482_ = lean_string_append(v___x_1480_, v___x_1481_);
lean_inc_ref(v_dir_1464_);
v___x_1483_ = l_Lake_joinRelative(v_dir_1464_, v___x_1476_);
v___x_1484_ = lean_string_append(v___x_1482_, v___x_1483_);
v___x_1485_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1486_ = lean_string_append(v___x_1484_, v___x_1485_);
v___x_1487_ = 1;
v___x_1488_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set_uint8(v___x_1488_, sizeof(void*)*1, v___x_1487_);
lean_inc_ref(v___y_1470_);
v___x_1489_ = lean_apply_2(v___y_1470_, v___x_1488_, lean_box(0));
v___x_1490_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_1483_);
v___x_1491_ = l_Lake_createParentDirs(v___x_1483_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v___x_1492_; 
lean_dec_ref_known(v___x_1491_, 1);
v___x_1492_ = lean_io_rename(v___y_1471_, v___x_1483_);
lean_dec_ref(v___x_1483_);
lean_dec_ref(v___y_1471_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set_tag(v___x_1495_, 1);
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
v___y_1438_ = v___x_1490_;
v___y_1439_ = v___y_1470_;
v___y_1440_ = v_snd_1473_;
v_val_1441_ = v___x_1498_;
goto v___jp_1437_;
}
}
}
else
{
lean_object* v_a_1501_; 
v_a_1501_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1492_, 1);
v___y_1457_ = v___x_1490_;
v___y_1458_ = v___y_1470_;
v___y_1459_ = v_snd_1473_;
v_a_1460_ = v_a_1501_;
goto v___jp_1456_;
}
}
else
{
lean_object* v_a_1502_; 
lean_dec_ref(v___x_1483_);
lean_dec_ref(v___y_1471_);
v_a_1502_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1491_, 1);
v___y_1457_ = v___x_1490_;
v___y_1458_ = v___y_1470_;
v___y_1459_ = v_snd_1473_;
v_a_1460_ = v_a_1502_;
goto v___jp_1456_;
}
}
}
else
{
lean_dec_ref(v___x_1476_);
lean_dec_ref(v___y_1471_);
v___y_1409_ = v_snd_1473_;
goto v___jp_1408_;
}
}
v___jp_1503_:
{
if (lean_obj_tag(v_packagesDir_x3f_1504_) == 1)
{
lean_object* v_val_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; uint8_t v___x_1511_; 
v_val_1507_ = lean_ctor_get(v_packagesDir_x3f_1504_, 0);
lean_inc_n(v_val_1507_, 2);
lean_dec_ref_known(v_packagesDir_x3f_1504_, 1);
lean_inc_ref(v_dir_1464_);
v___x_1508_ = l_Lake_joinRelative(v_dir_1464_, v_val_1507_);
v___x_1509_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1510_ = l_System_FilePath_pathExists(v___x_1508_);
v___x_1511_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1511_ == 0)
{
v___y_1469_ = v_val_1507_;
v___y_1470_ = v___y_1506_;
v___y_1471_ = v___x_1508_;
v_fst_1472_ = v___x_1510_;
v_snd_1473_ = v___y_1505_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1509_, v___x_1513_, v___x_1514_, v___x_1512_, v___y_1506_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_dec_ref_known(v___x_1515_, 1);
v___y_1469_ = v_val_1507_;
v___y_1470_ = v___y_1506_;
v___y_1471_ = v___x_1508_;
v_fst_1472_ = v___x_1510_;
v_snd_1473_ = v___y_1505_;
goto v___jp_1468_;
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec_ref(v___x_1508_);
lean_dec(v_val_1507_);
lean_dec(v___y_1505_);
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec(v_packagesDir_x3f_1504_);
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___y_1505_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
v___jp_1529_:
{
if (lean_obj_tag(v_fst_1530_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1579_; 
v_a_1532_ = lean_ctor_get(v_fst_1530_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_fst_1530_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1534_ = v_fst_1530_;
v_isShared_1535_ = v_isSharedCheck_1579_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v_fst_1530_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1579_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
if (lean_obj_tag(v_a_1532_) == 11)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec_ref_known(v_a_1532_, 2);
lean_del_object(v___x_1534_);
v___x_1536_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_1537_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1404_, v_depConfigs_1467_, v___x_1436_, v___x_1536_, v_snd_1531_, v_a_1406_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1559_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1559_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1559_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_snd_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1557_; 
v_snd_1542_ = lean_ctor_get(v_a_1538_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_a_1538_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v_a_1538_, 0);
lean_dec(v_unused_1558_);
v___x_1544_ = v_a_1538_;
v_isShared_1545_ = v_isSharedCheck_1557_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_snd_1542_);
lean_dec(v_a_1538_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1557_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1546_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8));
v___x_1547_ = lean_string_append(v_rootName_1528_, v___x_1546_);
v___x_1548_ = 1;
v___x_1549_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set_uint8(v___x_1549_, sizeof(void*)*1, v___x_1548_);
lean_inc_ref(v_a_1406_);
v___x_1550_ = lean_apply_2(v_a_1406_, v___x_1549_, lean_box(0));
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1550_);
v___x_1552_ = v___x_1544_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_snd_1542_);
v___x_1552_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1552_);
v___x_1554_ = v___x_1540_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_1528_);
return v___x_1537_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_1404_) == 0)
{
lean_object* v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
lean_dec_ref_known(v_toUpdate_1404_, 5);
lean_dec(v_snd_1531_);
lean_dec_ref(v_rootName_1528_);
v___x_1560_ = lean_io_error_to_string(v_a_1532_);
v___x_1561_ = 3;
v___x_1562_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set_uint8(v___x_1562_, sizeof(void*)*1, v___x_1561_);
lean_inc_ref(v_a_1406_);
v___x_1563_ = lean_apply_2(v_a_1406_, v___x_1562_, lean_box(0));
v___x_1564_ = lean_box(0);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 1);
lean_ctor_set(v___x_1534_, 0, v___x_1564_);
v___x_1566_ = v___x_1534_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1568_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_1569_ = lean_string_append(v_rootName_1528_, v___x_1568_);
v___x_1570_ = lean_io_error_to_string(v_a_1532_);
v___x_1571_ = lean_string_append(v___x_1569_, v___x_1570_);
lean_dec_ref(v___x_1570_);
v___x_1572_ = 2;
v___x_1573_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*1, v___x_1572_);
lean_inc_ref(v_a_1406_);
v___x_1574_ = lean_apply_2(v_a_1406_, v___x_1573_, lean_box(0));
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v_snd_1531_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1575_);
v___x_1577_ = v___x_1534_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v_packagesDir_x3f_1581_; lean_object* v_packages_1582_; lean_object* v___x_1583_; 
lean_dec_ref(v_rootName_1528_);
v_a_1580_ = lean_ctor_get(v_fst_1530_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v_fst_1530_, 1);
v_packagesDir_x3f_1581_ = lean_ctor_get(v_a_1580_, 2);
lean_inc(v_packagesDir_x3f_1581_);
v_packages_1582_ = lean_ctor_get(v_a_1580_, 3);
lean_inc_ref(v_packages_1582_);
lean_dec(v_a_1580_);
lean_inc(v_toUpdate_1404_);
v___x_1583_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_1404_, v_depConfigs_1467_, v___x_1436_, v_packages_1582_, v_snd_1531_, v_a_1406_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
if (lean_obj_tag(v_toUpdate_1404_) == 0)
{
lean_object* v_snd_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_snd_1585_ = lean_ctor_get(v_a_1584_, 1);
lean_inc(v_snd_1585_);
lean_dec(v_a_1584_);
v___x_1586_ = lean_array_get_size(v_packages_1582_);
v___x_1587_ = lean_nat_dec_lt(v___x_1436_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_dec_ref_known(v_toUpdate_1404_, 5);
lean_dec_ref(v_packages_1582_);
v_packagesDir_x3f_1504_ = v_packagesDir_x3f_1581_;
v___y_1505_ = v_snd_1585_;
v___y_1506_ = v_a_1406_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v___x_1588_ = lean_box(0);
v___x_1589_ = ((size_t)0ULL);
v___x_1590_ = lean_usize_of_nat(v___x_1586_);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1404_, v_packages_1582_, v___x_1589_, v___x_1590_, v___x_1588_, v_snd_1585_);
lean_dec_ref(v_packages_1582_);
lean_dec_ref_known(v_toUpdate_1404_, 5);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v_snd_1593_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v_snd_1593_ = lean_ctor_get(v_a_1592_, 1);
lean_inc(v_snd_1593_);
lean_dec(v_a_1592_);
v_packagesDir_x3f_1504_ = v_packagesDir_x3f_1581_;
v___y_1505_ = v_snd_1593_;
v___y_1506_ = v_a_1406_;
goto v___jp_1503_;
}
else
{
lean_dec(v_packagesDir_x3f_1581_);
return v___x_1591_;
}
}
}
else
{
lean_object* v_snd_1594_; 
lean_dec_ref(v_packages_1582_);
v_snd_1594_ = lean_ctor_get(v_a_1584_, 1);
lean_inc(v_snd_1594_);
lean_dec(v_a_1584_);
v_packagesDir_x3f_1504_ = v_packagesDir_x3f_1581_;
v___y_1505_ = v_snd_1594_;
v___y_1506_ = v_a_1406_;
goto v___jp_1503_;
}
}
else
{
lean_dec_ref(v_packages_1582_);
lean_dec(v_packagesDir_x3f_1581_);
lean_dec(v_toUpdate_1404_);
return v___x_1583_;
}
}
}
v___jp_1597_:
{
uint8_t v___x_1599_; 
v___x_1599_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1599_ == 0)
{
v_fst_1530_ = v_val_1598_;
v_snd_1531_ = v_a_1405_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1600_; size_t v___x_1601_; size_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1600_ = lean_box(0);
v___x_1601_ = ((size_t)0ULL);
v___x_1602_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_1596_, v___x_1601_, v___x_1602_, v___x_1600_, v_a_1406_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_dec_ref_known(v___x_1603_, 1);
v_fst_1530_ = v_val_1598_;
v_snd_1531_ = v_a_1405_;
goto v___jp_1529_;
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec_ref(v_val_1598_);
lean_dec_ref(v_rootName_1528_);
lean_dec(v_a_1405_);
lean_dec(v_toUpdate_1404_);
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_1629_, lean_object* v_toUpdate_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1629_, v_toUpdate_1630_, v_a_1631_, v_a_1632_);
lean_dec_ref(v_a_1632_);
lean_dec_ref(v_ws_1629_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* v_as_1635_, size_t v_sz_1636_, size_t v_i_1637_, lean_object* v_b_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___redArg(v_as_1635_, v_sz_1636_, v_i_1637_, v_b_1638_, v___y_1639_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* v_as_1643_, lean_object* v_sz_1644_, lean_object* v_i_1645_, lean_object* v_b_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
size_t v_sz_boxed_1650_; size_t v_i_boxed_1651_; lean_object* v_res_1652_; 
v_sz_boxed_1650_ = lean_unbox_usize(v_sz_1644_);
lean_dec(v_sz_1644_);
v_i_boxed_1651_ = lean_unbox_usize(v_i_1645_);
lean_dec(v_i_1645_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_1643_, v_sz_boxed_1650_, v_i_boxed_1651_, v_b_1646_, v___y_1647_, v___y_1648_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v_as_1643_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(lean_object* v_toUpdate_1653_, lean_object* v_as_1654_, size_t v_i_1655_, size_t v_stop_1656_, lean_object* v_b_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_1653_, v_as_1654_, v_i_1655_, v_stop_1656_, v_b_1657_, v___y_1658_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___boxed(lean_object* v_toUpdate_1662_, lean_object* v_as_1663_, lean_object* v_i_1664_, lean_object* v_stop_1665_, lean_object* v_b_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
size_t v_i_boxed_1670_; size_t v_stop_boxed_1671_; lean_object* v_res_1672_; 
v_i_boxed_1670_ = lean_unbox_usize(v_i_1664_);
lean_dec(v_i_1664_);
v_stop_boxed_1671_ = lean_unbox_usize(v_stop_1665_);
lean_dec(v_stop_1665_);
v_res_1672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4(v_toUpdate_1662_, v_as_1663_, v_i_boxed_1670_, v_stop_boxed_1671_, v_b_1666_, v___y_1667_, v___y_1668_);
lean_dec_ref(v___y_1668_);
lean_dec_ref(v_as_1663_);
lean_dec(v_toUpdate_1662_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_dep_1673_, lean_object* v_as_1674_, size_t v_i_1675_, size_t v_stop_1676_, lean_object* v_b_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_fst_1681_; lean_object* v_snd_1682_; lean_object* v___y_1687_; lean_object* v_name_1688_; uint8_t v___x_1691_; 
v___x_1691_ = lean_usize_dec_eq(v_i_1675_, v_stop_1676_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v_name_1693_; lean_object* v_scope_1694_; lean_object* v_configFile_1695_; lean_object* v_manifestFile_x3f_1696_; lean_object* v_src_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1724_; 
v___x_1692_ = lean_array_uget(v_as_1674_, v_i_1675_);
v_name_1693_ = lean_ctor_get(v___x_1692_, 0);
v_scope_1694_ = lean_ctor_get(v___x_1692_, 1);
v_configFile_1695_ = lean_ctor_get(v___x_1692_, 2);
v_manifestFile_x3f_1696_ = lean_ctor_get(v___x_1692_, 3);
v_src_1697_ = lean_ctor_get(v___x_1692_, 4);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1699_ = v___x_1692_;
v_isShared_1700_ = v_isSharedCheck_1724_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_src_1697_);
lean_inc(v_manifestFile_x3f_1696_);
lean_inc(v_configFile_1695_);
lean_inc(v_scope_1694_);
lean_inc(v_name_1693_);
lean_dec(v___x_1692_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1724_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
uint8_t v___x_1701_; 
v___x_1701_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1693_, v___y_1678_);
if (v___x_1701_ == 0)
{
uint8_t v___x_1702_; 
v___x_1702_ = 1;
if (lean_obj_tag(v_src_1697_) == 0)
{
uint8_t v_copy_1703_; 
v_copy_1703_ = lean_ctor_get_uint8(v_src_1697_, sizeof(void*)*1);
if (v_copy_1703_ == 0)
{
lean_object* v_dir_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1716_; 
v_dir_1704_ = lean_ctor_get(v_src_1697_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_src_1697_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1706_ = v_src_1697_;
v_isShared_1707_ = v_isSharedCheck_1716_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_dir_1704_);
lean_dec(v_src_1697_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1716_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v_relPkgDir_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v_relPkgDir_1708_ = lean_ctor_get(v_dep_1673_, 1);
lean_inc_ref(v_relPkgDir_1708_);
v___x_1709_ = l_Lake_joinRelative(v_relPkgDir_1708_, v_dir_1704_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1709_);
v___x_1711_ = v___x_1706_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1715_, sizeof(void*)*1, v_copy_1703_);
v___x_1711_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1713_; 
lean_inc(v_name_1693_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v___x_1711_);
v___x_1713_ = v___x_1699_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_name_1693_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_scope_1694_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v_configFile_1695_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_manifestFile_x3f_1696_);
lean_ctor_set(v_reuseFailAlloc_1714_, 4, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_ctor_set_uint8(v___x_1713_, sizeof(void*)*5, v___x_1702_);
v___y_1687_ = v___x_1713_;
v_name_1688_ = v_name_1693_;
goto v___jp_1686_;
}
}
}
}
else
{
lean_object* v___x_1718_; 
lean_inc(v_name_1693_);
if (v_isShared_1700_ == 0)
{
v___x_1718_ = v___x_1699_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_name_1693_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_scope_1694_);
lean_ctor_set(v_reuseFailAlloc_1719_, 2, v_configFile_1695_);
lean_ctor_set(v_reuseFailAlloc_1719_, 3, v_manifestFile_x3f_1696_);
lean_ctor_set(v_reuseFailAlloc_1719_, 4, v_src_1697_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*5, v___x_1702_);
v___y_1687_ = v___x_1718_;
v_name_1688_ = v_name_1693_;
goto v___jp_1686_;
}
}
}
else
{
lean_object* v___x_1721_; 
lean_inc(v_name_1693_);
if (v_isShared_1700_ == 0)
{
v___x_1721_ = v___x_1699_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_name_1693_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_scope_1694_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_configFile_1695_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_manifestFile_x3f_1696_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_src_1697_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*5, v___x_1702_);
v___y_1687_ = v___x_1721_;
v_name_1688_ = v_name_1693_;
goto v___jp_1686_;
}
}
}
else
{
lean_object* v___x_1723_; 
lean_del_object(v___x_1699_);
lean_dec_ref(v_src_1697_);
lean_dec(v_manifestFile_x3f_1696_);
lean_dec_ref(v_configFile_1695_);
lean_dec_ref(v_scope_1694_);
lean_dec(v_name_1693_);
v___x_1723_ = lean_box(0);
v_fst_1681_ = v___x_1723_;
v_snd_1682_ = v___y_1678_;
goto v___jp_1680_;
}
}
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_dec_ref(v_dep_1673_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_b_1677_);
lean_ctor_set(v___x_1725_, 1, v___y_1678_);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
v___jp_1680_:
{
size_t v___x_1683_; size_t v___x_1684_; 
v___x_1683_ = ((size_t)1ULL);
v___x_1684_ = lean_usize_add(v_i_1675_, v___x_1683_);
v_i_1675_ = v___x_1684_;
v_b_1677_ = v_fst_1681_;
v___y_1678_ = v_snd_1682_;
goto _start;
}
v___jp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_box(0);
v___x_1690_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1688_, v___y_1687_, v___y_1678_);
v_fst_1681_ = v___x_1689_;
v_snd_1682_ = v___x_1690_;
goto v___jp_1680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1727_, lean_object* v_as_1728_, lean_object* v_i_1729_, lean_object* v_stop_1730_, lean_object* v_b_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
size_t v_i_boxed_1734_; size_t v_stop_boxed_1735_; lean_object* v_res_1736_; 
v_i_boxed_1734_ = lean_unbox_usize(v_i_1729_);
lean_dec(v_i_1729_);
v_stop_boxed_1735_ = lean_unbox_usize(v_stop_1730_);
lean_dec(v_stop_1730_);
v_res_1736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1727_, v_as_1728_, v_i_boxed_1734_, v_stop_boxed_1735_, v_b_1731_, v___y_1732_);
lean_dec_ref(v_as_1728_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_manifestEntry_1743_; lean_object* v_pkgDir_1744_; lean_object* v_name_1745_; lean_object* v_manifestFile_x3f_1746_; lean_object* v___y_1748_; lean_object* v_fst_1749_; lean_object* v_snd_1750_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v_val_1802_; lean_object* v___y_1818_; 
v_manifestEntry_1743_ = lean_ctor_get(v_dep_1739_, 4);
v_pkgDir_1744_ = lean_ctor_get(v_dep_1739_, 0);
v_name_1745_ = lean_ctor_get(v_manifestEntry_1743_, 0);
v_manifestFile_x3f_1746_ = lean_ctor_get(v_manifestEntry_1743_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1746_) == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1744_);
v___x_1839_ = l_Lake_joinRelative(v_pkgDir_1744_, v___x_1838_);
v___y_1818_ = v___x_1839_;
goto v___jp_1817_;
}
else
{
lean_object* v_val_1840_; lean_object* v___x_1841_; 
v_val_1840_ = lean_ctor_get(v_manifestFile_x3f_1746_, 0);
lean_inc(v_val_1840_);
lean_inc_ref(v_pkgDir_1744_);
v___x_1841_ = l_Lake_joinRelative(v_pkgDir_1744_, v_val_1840_);
v___y_1818_ = v___x_1841_;
goto v___jp_1817_;
}
v___jp_1747_:
{
if (lean_obj_tag(v_fst_1749_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1780_; 
lean_inc(v_name_1745_);
lean_dec_ref(v_dep_1739_);
v_a_1751_ = lean_ctor_get(v_fst_1749_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_fst_1749_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1753_ = v_fst_1749_;
v_isShared_1754_ = v_isSharedCheck_1780_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v_fst_1749_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1780_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
if (lean_obj_tag(v_a_1751_) == 11)
{
uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_dec_ref_known(v_a_1751_, 2);
v___x_1755_ = 0;
v___x_1756_ = l_Lean_Name_toString(v_name_1745_, v___x_1755_);
v___x_1757_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1758_ = lean_string_append(v___x_1756_, v___x_1757_);
v___x_1759_ = lean_string_append(v___x_1758_, v___y_1748_);
lean_dec_ref(v___y_1748_);
v___x_1760_ = 2;
v___x_1761_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*1, v___x_1760_);
lean_inc_ref(v_a_1741_);
v___x_1762_ = lean_apply_2(v_a_1741_, v___x_1761_, lean_box(0));
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_snd_1750_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1763_);
v___x_1765_ = v___x_1753_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
else
{
uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
lean_dec_ref(v___y_1748_);
v___x_1767_ = 0;
v___x_1768_ = l_Lean_Name_toString(v_name_1745_, v___x_1767_);
v___x_1769_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1770_ = lean_string_append(v___x_1768_, v___x_1769_);
v___x_1771_ = lean_io_error_to_string(v_a_1751_);
v___x_1772_ = lean_string_append(v___x_1770_, v___x_1771_);
lean_dec_ref(v___x_1771_);
v___x_1773_ = 2;
v___x_1774_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set_uint8(v___x_1774_, sizeof(void*)*1, v___x_1773_);
lean_inc_ref(v_a_1741_);
v___x_1775_ = lean_apply_2(v_a_1741_, v___x_1774_, lean_box(0));
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v_snd_1750_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1776_);
v___x_1778_ = v___x_1753_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v___y_1748_);
v_a_1781_ = lean_ctor_get(v_fst_1749_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_fst_1749_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1783_ = v_fst_1749_;
v_isShared_1784_ = v_isSharedCheck_1797_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v_fst_1749_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1797_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v_packages_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_packages_1785_ = lean_ctor_get(v_a_1781_, 3);
lean_inc_ref(v_packages_1785_);
lean_dec(v_a_1781_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_array_get_size(v_packages_1785_);
v___x_1788_ = lean_box(0);
v___x_1789_ = lean_nat_dec_lt(v___x_1786_, v___x_1787_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
lean_dec_ref(v_packages_1785_);
lean_dec_ref(v_dep_1739_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v_snd_1750_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set_tag(v___x_1783_, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1790_);
v___x_1792_ = v___x_1783_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
else
{
size_t v___x_1794_; size_t v___x_1795_; lean_object* v___x_1796_; 
lean_del_object(v___x_1783_);
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = lean_usize_of_nat(v___x_1787_);
v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1739_, v_packages_1785_, v___x_1794_, v___x_1795_, v___x_1788_, v_snd_1750_);
lean_dec_ref(v_packages_1785_);
return v___x_1796_;
}
}
}
}
v___jp_1798_:
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1803_ = lean_array_get_size(v___y_1799_);
v___x_1804_ = lean_nat_dec_lt(v___y_1801_, v___x_1803_);
if (v___x_1804_ == 0)
{
v___y_1748_ = v___y_1800_;
v_fst_1749_ = v_val_1802_;
v_snd_1750_ = v_a_1740_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1805_; size_t v___x_1806_; size_t v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = lean_box(0);
v___x_1806_ = ((size_t)0ULL);
v___x_1807_ = lean_usize_of_nat(v___x_1803_);
v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_1799_, v___x_1806_, v___x_1807_, v___x_1805_, v_a_1741_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_dec_ref_known(v___x_1808_, 1);
v___y_1748_ = v___y_1800_;
v_fst_1749_ = v_val_1802_;
v_snd_1750_ = v_a_1740_;
goto v___jp_1747_;
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec_ref(v_val_1802_);
lean_dec_ref(v___y_1800_);
lean_dec(v_a_1740_);
lean_dec_ref(v_dep_1739_);
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
v___jp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1818_);
v___x_1821_ = l_Lake_Manifest_load(v___y_1818_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 1);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
v___y_1799_ = v___x_1820_;
v___y_1800_ = v___y_1818_;
v___y_1801_ = v___x_1819_;
v_val_1802_ = v___x_1827_;
goto v___jp_1798_;
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_a_1830_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1821_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1821_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 0);
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
v___y_1799_ = v___x_1820_;
v___y_1800_ = v___y_1818_;
v___y_1801_ = v___x_1819_;
v_val_1802_ = v___x_1835_;
goto v___jp_1798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1842_, v_a_1843_, v_a_1844_);
lean_dec_ref(v_a_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1847_, lean_object* v_as_1848_, size_t v_i_1849_, size_t v_stop_1850_, lean_object* v_b_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1847_, v_as_1848_, v_i_1849_, v_stop_1850_, v_b_1851_, v___y_1852_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1856_, lean_object* v_as_1857_, lean_object* v_i_1858_, lean_object* v_stop_1859_, lean_object* v_b_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
size_t v_i_boxed_1864_; size_t v_stop_boxed_1865_; lean_object* v_res_1866_; 
v_i_boxed_1864_ = lean_unbox_usize(v_i_1858_);
lean_dec(v_i_1858_);
v_stop_boxed_1865_ = lean_unbox_usize(v_stop_1859_);
lean_dec(v_stop_1859_);
v_res_1866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1856_, v_as_1857_, v_i_boxed_1864_, v_stop_boxed_1865_, v_b_1860_, v___y_1861_, v___y_1862_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_as_1857_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1868_, lean_object* v_pkg_1869_, lean_object* v_dep_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
uint8_t v___y_1875_; lean_object* v___y_1876_; lean_object* v_name_1906_; lean_object* v___x_1907_; 
v_name_1906_ = lean_ctor_get(v_dep_1870_, 0);
v___x_1907_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1871_, v_name_1906_);
if (lean_obj_tag(v___x_1907_) == 1)
{
lean_object* v_val_1908_; lean_object* v_lakeEnv_1909_; lean_object* v_packages_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v_config_1913_; lean_object* v_dir_1914_; lean_object* v_toWorkspaceConfig_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec_ref(v_dep_1870_);
lean_dec_ref(v_pkg_1869_);
v_val_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_val_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v_lakeEnv_1909_ = lean_ctor_get(v_ws_1868_, 0);
lean_inc_ref(v_lakeEnv_1909_);
v_packages_1910_ = lean_ctor_get(v_ws_1868_, 4);
lean_inc_ref(v_packages_1910_);
lean_dec_ref(v_ws_1868_);
v___x_1911_ = lean_unsigned_to_nat(0u);
v___x_1912_ = lean_array_fget(v_packages_1910_, v___x_1911_);
lean_dec_ref(v_packages_1910_);
v_config_1913_ = lean_ctor_get(v___x_1912_, 6);
lean_inc_ref(v_config_1913_);
v_dir_1914_ = lean_ctor_get(v___x_1912_, 4);
lean_inc_ref(v_dir_1914_);
lean_dec(v___x_1912_);
v_toWorkspaceConfig_1915_ = lean_ctor_get(v_config_1913_, 0);
lean_inc_ref(v_toWorkspaceConfig_1915_);
lean_dec_ref(v_config_1913_);
v___x_1916_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1915_);
v___x_1917_ = l_Lake_PackageEntry_materialize(v_val_1908_, v_lakeEnv_1909_, v_dir_1914_, v___x_1916_, v_a_1872_);
lean_dec_ref(v_lakeEnv_1909_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1926_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1918_);
lean_ctor_set(v___x_1922_, 1, v_a_1871_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1922_);
v___x_1924_ = v___x_1920_;
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
lean_dec(v_a_1871_);
v_a_1927_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1917_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1917_);
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
else
{
lean_object* v_wsIdx_1935_; lean_object* v_relDir_1936_; uint8_t v___y_1938_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
lean_dec(v___x_1907_);
v_wsIdx_1935_ = lean_ctor_get(v_pkg_1869_, 0);
lean_inc(v_wsIdx_1935_);
v_relDir_1936_ = lean_ctor_get(v_pkg_1869_, 5);
lean_inc_ref(v_relDir_1936_);
lean_dec_ref(v_pkg_1869_);
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_nat_dec_eq(v_wsIdx_1935_, v___x_1942_);
lean_dec(v_wsIdx_1935_);
if (v___x_1943_ == 0)
{
uint8_t v___x_1944_; 
v___x_1944_ = 1;
v___y_1938_ = v___x_1944_;
goto v___jp_1937_;
}
else
{
uint8_t v___x_1945_; 
v___x_1945_ = 0;
v___y_1938_ = v___x_1945_;
goto v___jp_1937_;
}
v___jp_1937_:
{
lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1940_ = lean_string_dec_eq(v_relDir_1936_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lake_joinRelative(v_relDir_1936_, v___x_1939_);
v___y_1875_ = v___y_1938_;
v___y_1876_ = v___x_1941_;
goto v___jp_1874_;
}
else
{
v___y_1875_ = v___y_1938_;
v___y_1876_ = v_relDir_1936_;
goto v___jp_1874_;
}
}
}
v___jp_1874_:
{
lean_object* v_lakeEnv_1877_; lean_object* v_packages_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v_config_1881_; lean_object* v_dir_1882_; lean_object* v_toWorkspaceConfig_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_lakeEnv_1877_ = lean_ctor_get(v_ws_1868_, 0);
lean_inc_ref(v_lakeEnv_1877_);
v_packages_1878_ = lean_ctor_get(v_ws_1868_, 4);
lean_inc_ref(v_packages_1878_);
lean_dec_ref(v_ws_1868_);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = lean_array_fget(v_packages_1878_, v___x_1879_);
lean_dec_ref(v_packages_1878_);
v_config_1881_ = lean_ctor_get(v___x_1880_, 6);
lean_inc_ref(v_config_1881_);
v_dir_1882_ = lean_ctor_get(v___x_1880_, 4);
lean_inc_ref(v_dir_1882_);
lean_dec(v___x_1880_);
v_toWorkspaceConfig_1883_ = lean_ctor_get(v_config_1881_, 0);
lean_inc_ref(v_toWorkspaceConfig_1883_);
lean_dec_ref(v_config_1881_);
v___x_1884_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1883_);
v___x_1885_ = l_Lake_Dependency_materialize(v_dep_1870_, v___y_1875_, v_lakeEnv_1877_, v_dir_1882_, v___x_1884_, v___y_1876_, v_a_1872_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1897_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1897_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1897_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_manifestEntry_1890_; lean_object* v_name_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
v_manifestEntry_1890_ = lean_ctor_get(v_a_1886_, 4);
v_name_1891_ = lean_ctor_get(v_manifestEntry_1890_, 0);
lean_inc_ref(v_manifestEntry_1890_);
lean_inc(v_name_1891_);
v___x_1892_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1891_, v_manifestEntry_1890_, v_a_1871_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_a_1886_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1893_);
v___x_1895_ = v___x_1888_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1871_);
v_a_1898_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1885_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1885_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_1946_, lean_object* v_pkg_1947_, lean_object* v_dep_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1946_, v_pkg_1947_, v_dep_1948_, v_a_1949_, v_a_1950_);
lean_dec_ref(v_a_1950_);
return v_res_1952_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_1953_; 
v___x_1953_ = 4;
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_1954_, lean_object* v_tc_x3f_1955_, uint8_t v_fixed_1956_, lean_object* v_self_1957_){
_start:
{
lean_object* v_clashes_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_clashes_1958_ = lean_ctor_get(v_self_1957_, 2);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_self_1957_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; lean_object* v_unused_1967_; 
v_unused_1966_ = lean_ctor_get(v_self_1957_, 1);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v_self_1957_, 0);
lean_dec(v_unused_1967_);
v___x_1960_ = v_self_1957_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_clashes_1958_);
lean_dec(v_self_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v_tc_x3f_1955_);
lean_ctor_set(v___x_1960_, 0, v_src_1954_);
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_src_1954_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_tc_x3f_1955_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_clashes_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_ctor_set_uint8(v___x_1963_, sizeof(void*)*3, v_fixed_1956_);
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_1968_, lean_object* v_tc_x3f_1969_, lean_object* v_fixed_1970_, lean_object* v_self_1971_){
_start:
{
uint8_t v_fixed_boxed_1972_; lean_object* v_res_1973_; 
v_fixed_boxed_1972_ = lean_unbox(v_fixed_1970_);
v_res_1973_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_1968_, v_tc_x3f_1969_, v_fixed_boxed_1972_, v_self_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_1974_, lean_object* v_ver_1975_, uint8_t v_fixed_1976_, lean_object* v_self_1977_){
_start:
{
lean_object* v_src_1978_; lean_object* v_tc_x3f_1979_; lean_object* v_clashes_1980_; uint8_t v_fixed_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1990_; 
v_src_1978_ = lean_ctor_get(v_self_1977_, 0);
v_tc_x3f_1979_ = lean_ctor_get(v_self_1977_, 1);
v_clashes_1980_ = lean_ctor_get(v_self_1977_, 2);
v_fixed_1981_ = lean_ctor_get_uint8(v_self_1977_, sizeof(void*)*3);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_self_1977_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1983_ = v_self_1977_;
v_isShared_1984_ = v_isSharedCheck_1990_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_clashes_1980_);
lean_inc(v_tc_x3f_1979_);
lean_inc(v_src_1978_);
lean_dec(v_self_1977_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1990_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1985_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1985_, 0, v_src_1974_);
lean_ctor_set(v___x_1985_, 1, v_ver_1975_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*2, v_fixed_1976_);
v___x_1986_ = lean_array_push(v_clashes_1980_, v___x_1985_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 2, v___x_1986_);
v___x_1988_ = v___x_1983_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_src_1978_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_tc_x3f_1979_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v___x_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1989_, sizeof(void*)*3, v_fixed_1981_);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_1991_, lean_object* v_ver_1992_, lean_object* v_fixed_1993_, lean_object* v_self_1994_){
_start:
{
uint8_t v_fixed_boxed_1995_; lean_object* v_res_1996_; 
v_fixed_boxed_1995_ = lean_unbox(v_fixed_1993_);
v_res_1996_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_1991_, v_ver_1992_, v_fixed_boxed_1995_, v_self_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v___x_2001_, lean_object* v_as_2002_, size_t v_i_2003_, size_t v_stop_2004_, lean_object* v_b_2005_){
_start:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_usize_dec_eq(v_i_2003_, v_stop_2004_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v_src_2008_; lean_object* v_ver_2009_; uint8_t v_fixed_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2027_; 
v___x_2007_ = lean_array_uget_borrowed(v_as_2002_, v_i_2003_);
v_src_2008_ = lean_ctor_get(v___x_2007_, 0);
v_ver_2009_ = lean_ctor_get(v___x_2007_, 1);
v_fixed_2010_ = lean_ctor_get_uint8(v___x_2007_, sizeof(void*)*2);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = lean_nat_dec_lt(v___x_2011_, v___x_2001_);
if (v_fixed_2010_ == 0)
{
lean_object* v___x_2031_; 
v___x_2031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2027_ = v___x_2031_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2032_; 
v___x_2032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2027_ = v___x_2032_;
goto v___jp_2026_;
}
v___jp_2013_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; size_t v___x_2023_; size_t v___x_2024_; 
v___x_2017_ = lean_string_append(v___y_2015_, v___y_2016_);
lean_dec_ref(v___y_2016_);
v___x_2018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2019_ = lean_string_append(v___x_2017_, v___x_2018_);
lean_inc(v_src_2008_);
v___x_2020_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2008_, v___x_2012_);
v___x_2021_ = lean_string_append(v___x_2019_, v___x_2020_);
lean_dec_ref(v___x_2020_);
v___x_2022_ = lean_string_append(v___x_2021_, v___y_2014_);
v___x_2023_ = ((size_t)1ULL);
v___x_2024_ = lean_usize_add(v_i_2003_, v___x_2023_);
v_i_2003_ = v___x_2024_;
v_b_2005_ = v___x_2022_;
goto _start;
}
v___jp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v_toString_2030_; 
v___x_2028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2029_ = lean_string_append(v_b_2005_, v___x_2028_);
v_toString_2030_ = lean_ctor_get(v_ver_2009_, 0);
lean_inc_ref(v_toString_2030_);
v___y_2014_ = v___y_2027_;
v___y_2015_ = v___x_2029_;
v___y_2016_ = v_toString_2030_;
goto v___jp_2013_;
}
}
else
{
return v_b_2005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v___x_2033_, lean_object* v_as_2034_, lean_object* v_i_2035_, lean_object* v_stop_2036_, lean_object* v_b_2037_){
_start:
{
size_t v_i_boxed_2038_; size_t v_stop_boxed_2039_; lean_object* v_res_2040_; 
v_i_boxed_2038_ = lean_unbox_usize(v_i_2035_);
lean_dec(v_i_2035_);
v_stop_boxed_2039_ = lean_unbox_usize(v_stop_2036_);
lean_dec(v_stop_2036_);
v_res_2040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2033_, v_as_2034_, v_i_boxed_2038_, v_stop_boxed_2039_, v_b_2037_);
lean_dec_ref(v_as_2034_);
lean_dec(v___x_2033_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v___x_2041_, lean_object* v_as_2042_, size_t v_i_2043_, size_t v_stop_2044_, lean_object* v_b_2045_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_usize_dec_eq(v_i_2043_, v_stop_2044_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; lean_object* v_src_2048_; lean_object* v_ver_2049_; uint8_t v_fixed_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2067_; 
v___x_2047_ = lean_array_uget_borrowed(v_as_2042_, v_i_2043_);
v_src_2048_ = lean_ctor_get(v___x_2047_, 0);
v_ver_2049_ = lean_ctor_get(v___x_2047_, 1);
v_fixed_2050_ = lean_ctor_get_uint8(v___x_2047_, sizeof(void*)*2);
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = lean_nat_dec_lt(v___x_2051_, v___x_2041_);
if (v_fixed_2050_ == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2067_ = v___x_2071_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2072_; 
v___x_2072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2067_ = v___x_2072_;
goto v___jp_2066_;
}
v___jp_2053_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; size_t v___x_2063_; size_t v___x_2064_; lean_object* v___x_2065_; 
v___x_2057_ = lean_string_append(v___y_2055_, v___y_2056_);
lean_dec_ref(v___y_2056_);
v___x_2058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2059_ = lean_string_append(v___x_2057_, v___x_2058_);
lean_inc(v_src_2048_);
v___x_2060_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_2048_, v___x_2052_);
v___x_2061_ = lean_string_append(v___x_2059_, v___x_2060_);
lean_dec_ref(v___x_2060_);
v___x_2062_ = lean_string_append(v___x_2061_, v___y_2054_);
v___x_2063_ = ((size_t)1ULL);
v___x_2064_ = lean_usize_add(v_i_2043_, v___x_2063_);
v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v___x_2041_, v_as_2042_, v___x_2064_, v_stop_2044_, v___x_2062_);
return v___x_2065_;
}
v___jp_2066_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_toString_2070_; 
v___x_2068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_2069_ = lean_string_append(v_b_2045_, v___x_2068_);
v_toString_2070_ = lean_ctor_get(v_ver_2049_, 0);
lean_inc_ref(v_toString_2070_);
v___y_2054_ = v___y_2067_;
v___y_2055_ = v___x_2069_;
v___y_2056_ = v_toString_2070_;
goto v___jp_2053_;
}
}
else
{
return v_b_2045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v___x_2073_, lean_object* v_as_2074_, lean_object* v_i_2075_, lean_object* v_stop_2076_, lean_object* v_b_2077_){
_start:
{
size_t v_i_boxed_2078_; size_t v_stop_boxed_2079_; lean_object* v_res_2080_; 
v_i_boxed_2078_ = lean_unbox_usize(v_i_2075_);
lean_dec(v_i_2075_);
v_stop_boxed_2079_ = lean_unbox_usize(v_stop_2076_);
lean_dec(v_stop_2076_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___x_2073_, v_as_2074_, v_i_boxed_2078_, v_stop_boxed_2079_, v_b_2077_);
lean_dec_ref(v_as_2074_);
lean_dec(v___x_2073_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_2081_, lean_object* v_as_2082_, size_t v_i_2083_, size_t v_stop_2084_, lean_object* v_b_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_a_2089_; uint8_t v___x_2093_; 
v___x_2093_ = lean_usize_dec_eq(v_i_2083_, v_stop_2084_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v_relPkgDir_2095_; lean_object* v_manifestEntry_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2094_ = lean_array_uget_borrowed(v_as_2082_, v_i_2083_);
v_relPkgDir_2095_ = lean_ctor_get(v___x_2094_, 1);
v_manifestEntry_2096_ = lean_ctor_get(v___x_2094_, 4);
lean_inc_ref(v_relPkgDir_2095_);
lean_inc_ref(v___x_2081_);
v___x_2097_ = l_Lake_joinRelative(v___x_2081_, v_relPkgDir_2095_);
v___x_2098_ = l_Lake_toolchainFileName;
v___x_2099_ = l_System_FilePath_join(v___x_2097_, v___x_2098_);
v___x_2100_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2099_);
lean_dec_ref(v___x_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
if (lean_obj_tag(v_a_2101_) == 1)
{
lean_object* v_tc_x3f_2102_; 
v_tc_x3f_2102_ = lean_ctor_get(v_b_2085_, 1);
if (lean_obj_tag(v_tc_x3f_2102_) == 1)
{
lean_object* v_val_2103_; lean_object* v_src_2104_; lean_object* v_clashes_2105_; uint8_t v_fixed_2106_; lean_object* v_val_2107_; uint8_t v___x_2108_; 
v_val_2103_ = lean_ctor_get(v_a_2101_, 0);
v_src_2104_ = lean_ctor_get(v_b_2085_, 0);
v_clashes_2105_ = lean_ctor_get(v_b_2085_, 2);
v_fixed_2106_ = lean_ctor_get_uint8(v_b_2085_, sizeof(void*)*3);
v_val_2107_ = lean_ctor_get(v_tc_x3f_2102_, 0);
v___x_2108_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2094_);
if (v___x_2108_ == 0)
{
uint8_t v___x_2114_; 
v___x_2114_ = l_Lake_ToolchainVer_ble(v_val_2103_, v_val_2107_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2123_; 
lean_inc_ref(v_clashes_2105_);
lean_inc(v_src_2104_);
lean_inc_ref(v_tc_x3f_2102_);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_b_2085_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; lean_object* v_unused_2125_; lean_object* v_unused_2126_; 
v_unused_2124_ = lean_ctor_get(v_b_2085_, 2);
lean_dec(v_unused_2124_);
v_unused_2125_ = lean_ctor_get(v_b_2085_, 1);
lean_dec(v_unused_2125_);
v_unused_2126_ = lean_ctor_get(v_b_2085_, 0);
lean_dec(v_unused_2126_);
v___x_2116_ = v_b_2085_;
v_isShared_2117_ = v_isSharedCheck_2123_;
goto v_resetjp_2115_;
}
else
{
lean_dec(v_b_2085_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2123_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
if (v_fixed_2106_ == 0)
{
uint8_t v___x_2118_; 
v___x_2118_ = l_Lake_ToolchainVer_blt(v_val_2107_, v_val_2103_);
if (v___x_2118_ == 0)
{
lean_inc(v_val_2103_);
lean_del_object(v___x_2116_);
lean_dec_ref_known(v_a_2101_, 1);
goto v___jp_2109_;
}
else
{
lean_object* v_name_2119_; lean_object* v___x_2121_; 
lean_dec(v_src_2104_);
lean_dec_ref_known(v_tc_x3f_2102_, 1);
v_name_2119_ = lean_ctor_get(v_manifestEntry_2096_, 0);
lean_inc(v_name_2119_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 1, v_a_2101_);
lean_ctor_set(v___x_2116_, 0, v_name_2119_);
v___x_2121_ = v___x_2116_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_name_2119_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_a_2101_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v_clashes_2105_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*3, v___x_2108_);
v_a_2089_ = v___x_2121_;
goto v___jp_2088_;
}
}
}
else
{
lean_inc(v_val_2103_);
lean_del_object(v___x_2116_);
lean_dec_ref_known(v_a_2101_, 1);
goto v___jp_2109_;
}
}
}
else
{
lean_dec_ref_known(v_a_2101_, 1);
v_a_2089_ = v_b_2085_;
goto v___jp_2088_;
}
}
else
{
if (v_fixed_2106_ == 0)
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2141_; 
lean_inc_ref(v_clashes_2105_);
lean_inc(v_src_2104_);
lean_inc_ref(v_tc_x3f_2102_);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_b_2085_);
if (v_isSharedCheck_2141_ == 0)
{
lean_object* v_unused_2142_; lean_object* v_unused_2143_; lean_object* v_unused_2144_; 
v_unused_2142_ = lean_ctor_get(v_b_2085_, 2);
lean_dec(v_unused_2142_);
v_unused_2143_ = lean_ctor_get(v_b_2085_, 1);
lean_dec(v_unused_2143_);
v_unused_2144_ = lean_ctor_get(v_b_2085_, 0);
lean_dec(v_unused_2144_);
v___x_2128_ = v_b_2085_;
v_isShared_2129_ = v_isSharedCheck_2141_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v_b_2085_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2141_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
uint8_t v___x_2130_; 
v___x_2130_ = l_Lake_ToolchainVer_ble(v_val_2107_, v_val_2103_);
if (v___x_2130_ == 0)
{
lean_object* v_name_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
lean_inc(v_val_2103_);
lean_dec_ref_known(v_a_2101_, 1);
v_name_2131_ = lean_ctor_get(v_manifestEntry_2096_, 0);
lean_inc(v_name_2131_);
v___x_2132_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2132_, 0, v_name_2131_);
lean_ctor_set(v___x_2132_, 1, v_val_2103_);
lean_ctor_set_uint8(v___x_2132_, sizeof(void*)*2, v___x_2108_);
v___x_2133_ = lean_array_push(v_clashes_2105_, v___x_2132_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 2, v___x_2133_);
v___x_2135_ = v___x_2128_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_src_2104_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_tc_x3f_2102_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v___x_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*3, v_fixed_2106_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
v_a_2089_ = v___x_2135_;
goto v___jp_2088_;
}
}
else
{
lean_object* v_name_2137_; lean_object* v___x_2139_; 
lean_dec(v_src_2104_);
lean_dec_ref_known(v_tc_x3f_2102_, 1);
v_name_2137_ = lean_ctor_get(v_manifestEntry_2096_, 0);
lean_inc(v_name_2137_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_a_2101_);
lean_ctor_set(v___x_2128_, 0, v_name_2137_);
v___x_2139_ = v___x_2128_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_name_2137_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_a_2101_);
lean_ctor_set(v_reuseFailAlloc_2140_, 2, v_clashes_2105_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*3, v___x_2108_);
v_a_2089_ = v___x_2139_;
goto v___jp_2088_;
}
}
}
}
else
{
uint8_t v___x_2145_; 
lean_inc_n(v_val_2103_, 2);
lean_dec_ref_known(v_a_2101_, 1);
lean_inc(v_val_2107_);
v___x_2145_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2107_, v_val_2103_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2155_; 
lean_inc_ref(v_clashes_2105_);
lean_inc(v_src_2104_);
lean_inc_ref(v_tc_x3f_2102_);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_b_2085_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; lean_object* v_unused_2157_; lean_object* v_unused_2158_; 
v_unused_2156_ = lean_ctor_get(v_b_2085_, 2);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_b_2085_, 1);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_b_2085_, 0);
lean_dec(v_unused_2158_);
v___x_2147_ = v_b_2085_;
v_isShared_2148_ = v_isSharedCheck_2155_;
goto v_resetjp_2146_;
}
else
{
lean_dec(v_b_2085_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2155_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v_name_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
v_name_2149_ = lean_ctor_get(v_manifestEntry_2096_, 0);
lean_inc(v_name_2149_);
v___x_2150_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2150_, 0, v_name_2149_);
lean_ctor_set(v___x_2150_, 1, v_val_2103_);
lean_ctor_set_uint8(v___x_2150_, sizeof(void*)*2, v___x_2108_);
v___x_2151_ = lean_array_push(v_clashes_2105_, v___x_2150_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 2, v___x_2151_);
v___x_2153_ = v___x_2147_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_src_2104_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_tc_x3f_2102_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v___x_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*3, v_fixed_2106_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
v_a_2089_ = v___x_2153_;
goto v___jp_2088_;
}
}
}
else
{
lean_dec(v_val_2103_);
v_a_2089_ = v_b_2085_;
goto v___jp_2088_;
}
}
}
v___jp_2109_:
{
lean_object* v_name_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_name_2110_ = lean_ctor_get(v_manifestEntry_2096_, 0);
lean_inc(v_name_2110_);
v___x_2111_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2111_, 0, v_name_2110_);
lean_ctor_set(v___x_2111_, 1, v_val_2103_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*2, v___x_2108_);
v___x_2112_ = lean_array_push(v_clashes_2105_, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2113_, 0, v_src_2104_);
lean_ctor_set(v___x_2113_, 1, v_tc_x3f_2102_);
lean_ctor_set(v___x_2113_, 2, v___x_2112_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*3, v_fixed_2106_);
v_a_2089_ = v___x_2113_;
goto v___jp_2088_;
}
}
else
{
lean_object* v_clashes_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2168_; 
v_clashes_2159_ = lean_ctor_get(v_b_2085_, 2);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_b_2085_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; lean_object* v_unused_2170_; 
v_unused_2169_ = lean_ctor_get(v_b_2085_, 1);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_b_2085_, 0);
lean_dec(v_unused_2170_);
v___x_2161_ = v_b_2085_;
v_isShared_2162_ = v_isSharedCheck_2168_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_clashes_2159_);
lean_dec(v_b_2085_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2168_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_name_2163_; uint8_t v___x_2164_; lean_object* v___x_2166_; 
v_name_2163_ = lean_ctor_get(v_manifestEntry_2096_, 0);
v___x_2164_ = l_Lake_MaterializedDep_fixedToolchain(v___x_2094_);
lean_inc(v_name_2163_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v_a_2101_);
lean_ctor_set(v___x_2161_, 0, v_name_2163_);
v___x_2166_ = v___x_2161_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_name_2163_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_a_2101_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_clashes_2159_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*3, v___x_2164_);
v_a_2089_ = v___x_2166_;
goto v___jp_2088_;
}
}
}
}
else
{
lean_dec(v_a_2101_);
v_a_2089_ = v_b_2085_;
goto v___jp_2088_;
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v_b_2085_);
lean_dec_ref(v___x_2081_);
v_a_2171_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2173_ = v___x_2100_;
v_isShared_2174_ = v_isSharedCheck_2183_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2100_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2183_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2175_ = lean_io_error_to_string(v_a_2171_);
v___x_2176_ = 3;
v___x_2177_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set_uint8(v___x_2177_, sizeof(void*)*1, v___x_2176_);
lean_inc_ref(v___y_2086_);
v___x_2178_ = lean_apply_2(v___y_2086_, v___x_2177_, lean_box(0));
v___x_2179_ = lean_box(0);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2179_);
v___x_2181_ = v___x_2173_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v___x_2184_; 
lean_dec_ref(v___x_2081_);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_b_2085_);
return v___x_2184_;
}
v___jp_2088_:
{
size_t v___x_2090_; size_t v___x_2091_; 
v___x_2090_ = ((size_t)1ULL);
v___x_2091_ = lean_usize_add(v_i_2083_, v___x_2090_);
v_i_2083_ = v___x_2091_;
v_b_2085_ = v_a_2089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2185_, lean_object* v_as_2186_, lean_object* v_i_2187_, lean_object* v_stop_2188_, lean_object* v_b_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
size_t v_i_boxed_2192_; size_t v_stop_boxed_2193_; lean_object* v_res_2194_; 
v_i_boxed_2192_ = lean_unbox_usize(v_i_2187_);
lean_dec(v_i_2187_);
v_stop_boxed_2193_ = lean_unbox_usize(v_stop_2188_);
lean_dec(v_stop_2188_);
v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2185_, v_as_2186_, v_i_boxed_2192_, v_stop_boxed_2193_, v_b_2189_, v___y_2190_);
lean_dec_ref(v___y_2190_);
lean_dec_ref(v_as_2186_);
return v_res_2194_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2206_ = lean_unsigned_to_nat(4u);
v___x_2207_ = lean_mk_empty_array_with_capacity(v___x_2206_);
v___x_2208_ = lean_array_push(v___x_2207_, v___x_2205_);
return v___x_2208_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2210_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2211_ = lean_array_push(v___x_2210_, v___x_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2232_, lean_object* v_rootDeps_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v___y_2237_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2250_; uint8_t v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; uint8_t v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v_lakeEnv_2272_; lean_object* v_lakeArgs_x3f_2273_; lean_object* v_packages_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v_baseName_2277_; lean_object* v_dir_2278_; lean_object* v_config_2279_; lean_object* v___x_2280_; lean_object* v_rootToolchainFile_2281_; lean_object* v___y_2283_; uint8_t v___y_2284_; uint8_t v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2427_; uint8_t v___y_2428_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_lakeEnv_2272_ = lean_ctor_get(v_ws_2232_, 0);
lean_inc_ref(v_lakeEnv_2272_);
v_lakeArgs_x3f_2273_ = lean_ctor_get(v_ws_2232_, 3);
lean_inc(v_lakeArgs_x3f_2273_);
v_packages_2274_ = lean_ctor_get(v_ws_2232_, 4);
lean_inc_ref(v_packages_2274_);
lean_dec_ref(v_ws_2232_);
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = lean_array_fget(v_packages_2274_, v___x_2275_);
lean_dec_ref(v_packages_2274_);
v_baseName_2277_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_baseName_2277_);
v_dir_2278_ = lean_ctor_get(v___x_2276_, 4);
lean_inc_ref_n(v_dir_2278_, 3);
v_config_2279_ = lean_ctor_get(v___x_2276_, 6);
lean_inc_ref(v_config_2279_);
lean_dec(v___x_2276_);
v___x_2280_ = l_Lake_toolchainFileName;
v_rootToolchainFile_2281_ = l_Lake_joinRelative(v_dir_2278_, v___x_2280_);
v___x_2432_ = l_System_FilePath_join(v_dir_2278_, v___x_2280_);
v___x_2433_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2432_);
lean_dec_ref(v___x_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2486_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2436_ = v___x_2433_;
v_isShared_2437_ = v_isSharedCheck_2486_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2486_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v_src_2439_; lean_object* v_tc_x3f_2440_; lean_object* v_clashes_2441_; uint8_t v_fixed_2442_; uint8_t v_fixedToolchain_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; 
v_fixedToolchain_2465_ = lean_ctor_get_uint8(v_config_2279_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_2279_);
v___x_2466_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___x_2467_ = lean_array_get_size(v_rootDeps_2233_);
v___x_2468_ = lean_nat_dec_lt(v___x_2275_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_dec_ref(v_dir_2278_);
lean_inc(v_a_2434_);
v_src_2439_ = v_baseName_2277_;
v_tc_x3f_2440_ = v_a_2434_;
v_clashes_2441_ = v___x_2466_;
v_fixed_2442_ = v_fixedToolchain_2465_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2469_; size_t v___x_2470_; size_t v___x_2471_; lean_object* v___x_2472_; 
lean_inc(v_a_2434_);
v___x_2469_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2469_, 0, v_baseName_2277_);
lean_ctor_set(v___x_2469_, 1, v_a_2434_);
lean_ctor_set(v___x_2469_, 2, v___x_2466_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*3, v_fixedToolchain_2465_);
v___x_2470_ = ((size_t)0ULL);
v___x_2471_ = lean_usize_of_nat(v___x_2467_);
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2278_, v_rootDeps_2233_, v___x_2470_, v___x_2471_, v___x_2469_, v_a_2234_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v_src_2474_; lean_object* v_tc_x3f_2475_; lean_object* v_clashes_2476_; uint8_t v_fixed_2477_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
v_src_2474_ = lean_ctor_get(v_a_2473_, 0);
lean_inc(v_src_2474_);
v_tc_x3f_2475_ = lean_ctor_get(v_a_2473_, 1);
lean_inc(v_tc_x3f_2475_);
v_clashes_2476_ = lean_ctor_get(v_a_2473_, 2);
lean_inc_ref(v_clashes_2476_);
v_fixed_2477_ = lean_ctor_get_uint8(v_a_2473_, sizeof(void*)*3);
lean_dec(v_a_2473_);
v_src_2439_ = v_src_2474_;
v_tc_x3f_2440_ = v_tc_x3f_2475_;
v_clashes_2441_ = v_clashes_2476_;
v_fixed_2442_ = v_fixed_2477_;
goto v___jp_2438_;
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_del_object(v___x_2436_);
lean_dec(v_a_2434_);
lean_dec_ref(v_rootToolchainFile_2281_);
lean_dec(v_lakeArgs_x3f_2273_);
lean_dec_ref(v_lakeEnv_2272_);
v_a_2478_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2472_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2472_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
v___jp_2438_:
{
lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2443_ = lean_array_get_size(v_clashes_2441_);
v___x_2444_ = lean_nat_dec_lt(v___x_2275_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_dec_ref(v_clashes_2441_);
lean_dec(v_src_2439_);
if (lean_obj_tag(v_tc_x3f_2440_) == 1)
{
if (lean_obj_tag(v_a_2434_) == 0)
{
lean_object* v_val_2445_; 
lean_del_object(v___x_2436_);
v_val_2445_ = lean_ctor_get(v_tc_x3f_2440_, 0);
lean_inc(v_val_2445_);
lean_dec_ref_known(v_tc_x3f_2440_, 1);
v___y_2427_ = v_val_2445_;
v___y_2428_ = v___x_2444_;
goto v___jp_2426_;
}
else
{
lean_object* v_val_2446_; lean_object* v_val_2447_; uint8_t v___x_2448_; 
v_val_2446_ = lean_ctor_get(v_tc_x3f_2440_, 0);
lean_inc_n(v_val_2446_, 2);
lean_dec_ref_known(v_tc_x3f_2440_, 1);
v_val_2447_ = lean_ctor_get(v_a_2434_, 0);
lean_inc(v_val_2447_);
lean_dec_ref_known(v_a_2434_, 1);
v___x_2448_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2447_, v_val_2446_);
if (v___x_2448_ == 0)
{
lean_del_object(v___x_2436_);
v___y_2427_ = v_val_2446_;
v___y_2428_ = v___x_2448_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
lean_dec(v_val_2446_);
lean_dec_ref(v_rootToolchainFile_2281_);
lean_dec(v_lakeArgs_x3f_2273_);
lean_dec_ref(v_lakeEnv_2272_);
v___x_2449_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15));
lean_inc_ref(v_a_2234_);
v___x_2450_ = lean_apply_2(v_a_2234_, v___x_2449_, lean_box(0));
v___x_2451_ = lean_box(0);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2451_);
v___x_2453_ = v___x_2436_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2458_; 
lean_dec(v_tc_x3f_2440_);
lean_dec(v_a_2434_);
lean_dec_ref(v_rootToolchainFile_2281_);
lean_dec(v_lakeArgs_x3f_2273_);
lean_dec_ref(v_lakeEnv_2272_);
v___x_2455_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17));
lean_inc_ref(v_a_2234_);
v___x_2456_ = lean_apply_2(v_a_2234_, v___x_2455_, lean_box(0));
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2456_);
v___x_2458_ = v___x_2436_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
else
{
lean_del_object(v___x_2436_);
lean_dec(v_a_2434_);
lean_dec_ref(v_rootToolchainFile_2281_);
lean_dec(v_lakeArgs_x3f_2273_);
lean_dec_ref(v_lakeEnv_2272_);
if (lean_obj_tag(v_tc_x3f_2440_) == 1)
{
if (v_fixed_2442_ == 0)
{
lean_object* v_val_2460_; lean_object* v___x_2461_; 
v_val_2460_ = lean_ctor_get(v_tc_x3f_2440_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v_tc_x3f_2440_, 1);
v___x_2461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2264_ = v___x_2444_;
v___y_2265_ = v_src_2439_;
v___y_2266_ = v_clashes_2441_;
v___y_2267_ = v_val_2460_;
v___y_2268_ = v___x_2443_;
v___y_2269_ = v___x_2461_;
goto v___jp_2263_;
}
else
{
lean_object* v_val_2462_; lean_object* v___x_2463_; 
v_val_2462_ = lean_ctor_get(v_tc_x3f_2440_, 0);
lean_inc(v_val_2462_);
lean_dec_ref_known(v_tc_x3f_2440_, 1);
v___x_2463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2264_ = v___x_2444_;
v___y_2265_ = v_src_2439_;
v___y_2266_ = v_clashes_2441_;
v___y_2267_ = v_val_2462_;
v___y_2268_ = v___x_2443_;
v___y_2269_ = v___x_2463_;
goto v___jp_2263_;
}
}
else
{
lean_object* v___x_2464_; 
lean_dec(v_tc_x3f_2440_);
lean_dec(v_src_2439_);
v___x_2464_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
v___y_2243_ = v_clashes_2441_;
v___y_2244_ = v___x_2443_;
v___y_2245_ = v___x_2464_;
goto v___jp_2242_;
}
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2499_; 
lean_dec_ref(v_rootToolchainFile_2281_);
lean_dec_ref(v_config_2279_);
lean_dec_ref(v_dir_2278_);
lean_dec(v_baseName_2277_);
lean_dec(v_lakeArgs_x3f_2273_);
lean_dec_ref(v_lakeEnv_2272_);
v_a_2487_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2489_ = v___x_2433_;
v_isShared_2490_ = v_isSharedCheck_2499_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2433_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2499_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2491_ = lean_io_error_to_string(v_a_2487_);
v___x_2492_ = 3;
v___x_2493_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*1, v___x_2492_);
lean_inc_ref(v_a_2234_);
v___x_2494_ = lean_apply_2(v_a_2234_, v___x_2493_, lean_box(0));
v___x_2495_ = lean_box(0);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2495_);
v___x_2497_ = v___x_2489_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
v___jp_2236_:
{
uint8_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2238_ = 2;
v___x_2239_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2239_, 0, v___y_2237_);
lean_ctor_set_uint8(v___x_2239_, sizeof(void*)*1, v___x_2238_);
lean_inc_ref(v_a_2234_);
v___x_2240_ = lean_apply_2(v_a_2234_, v___x_2239_, lean_box(0));
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
return v___x_2241_;
}
v___jp_2242_:
{
size_t v___x_2246_; size_t v___x_2247_; lean_object* v___x_2248_; 
v___x_2246_ = ((size_t)0ULL);
v___x_2247_ = lean_usize_of_nat(v___y_2244_);
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2244_, v___y_2243_, v___x_2246_, v___x_2247_, v___y_2245_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2244_);
v___y_2237_ = v___x_2248_;
goto v___jp_2236_;
}
v___jp_2249_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_inc_ref(v___y_2250_);
v___x_2257_ = lean_string_append(v___y_2250_, v___y_2256_);
lean_dec_ref(v___y_2256_);
v___x_2258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2259_ = lean_string_append(v___x_2257_, v___x_2258_);
v___x_2260_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2253_, v___y_2251_);
v___x_2261_ = lean_string_append(v___x_2259_, v___x_2260_);
lean_dec_ref(v___x_2260_);
v___x_2262_ = lean_string_append(v___x_2261_, v___y_2252_);
if (v___y_2251_ == 0)
{
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
v___y_2237_ = v___x_2262_;
goto v___jp_2236_;
}
else
{
v___y_2243_ = v___y_2254_;
v___y_2244_ = v___y_2255_;
v___y_2245_ = v___x_2262_;
goto v___jp_2242_;
}
}
v___jp_2263_:
{
lean_object* v___x_2270_; lean_object* v_toString_2271_; 
v___x_2270_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_2271_ = lean_ctor_get(v___y_2267_, 0);
lean_inc_ref(v_toString_2271_);
lean_dec_ref(v___y_2267_);
v___y_2250_ = v___x_2270_;
v___y_2251_ = v___y_2264_;
v___y_2252_ = v___y_2269_;
v___y_2253_ = v___y_2265_;
v___y_2254_ = v___y_2266_;
v___y_2255_ = v___y_2268_;
v___y_2256_ = v_toString_2271_;
goto v___jp_2249_;
}
v___jp_2282_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_inc_ref(v___y_2283_);
v___x_2287_ = lean_string_append(v___y_2283_, v___y_2286_);
v___x_2288_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2289_ = lean_string_append(v___x_2287_, v___x_2288_);
v___x_2290_ = 1;
v___x_2291_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*1, v___x_2290_);
lean_inc_ref(v_a_2234_);
v___x_2292_ = lean_apply_2(v_a_2234_, v___x_2291_, lean_box(0));
v___x_2293_ = l_IO_FS_writeFile(v_rootToolchainFile_2281_, v___y_2286_);
lean_dec_ref(v_rootToolchainFile_2281_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_dec_ref_known(v___x_2293_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2273_) == 1)
{
lean_object* v_elan_x3f_2294_; 
v_elan_x3f_2294_ = lean_ctor_get(v_lakeEnv_2272_, 2);
if (lean_obj_tag(v_elan_x3f_2294_) == 1)
{
lean_object* v_val_2295_; lean_object* v_val_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v_elan_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_val_2295_ = lean_ctor_get(v_lakeArgs_x3f_2273_, 0);
lean_inc(v_val_2295_);
lean_dec_ref_known(v_lakeArgs_x3f_2273_, 1);
v_val_2296_ = lean_ctor_get(v_elan_x3f_2294_, 0);
v___x_2297_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_2234_);
v___x_2298_ = lean_apply_2(v_a_2234_, v___x_2297_, lean_box(0));
v___x_2299_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_2300_ = lean_ctor_get(v_val_2296_, 1);
lean_inc_ref(v_elan_2300_);
v___x_2301_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_2302_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_2303_ = lean_array_push(v___x_2302_, v___y_2286_);
v___x_2304_ = lean_array_push(v___x_2303_, v___x_2301_);
v___x_2305_ = l_Array_append___redArg(v___x_2304_, v_val_2295_);
lean_dec(v_val_2295_);
v___x_2306_ = lean_box(0);
v___x_2307_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2272_);
v___x_2308_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2308_, 0, v___x_2299_);
lean_ctor_set(v___x_2308_, 1, v_elan_2300_);
lean_ctor_set(v___x_2308_, 2, v___x_2305_);
lean_ctor_set(v___x_2308_, 3, v___x_2306_);
lean_ctor_set(v___x_2308_, 4, v___x_2307_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*5, v___y_2284_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*5 + 1, v___y_2285_);
v___x_2309_ = lean_io_process_spawn(v___x_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2311_ = lean_io_process_child_wait(v___x_2299_, v_a_2310_);
lean_dec(v_a_2310_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; uint32_t v___x_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = lean_unbox_uint32(v_a_2312_);
lean_dec(v_a_2312_);
v___x_2314_ = lean_uint32_to_uint8(v___x_2313_);
v___x_2315_ = lean_io_exit(v___x_2314_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2336_; 
v_a_2324_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2326_ = v___x_2315_;
v_isShared_2327_ = v_isSharedCheck_2336_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2315_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2336_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2328_ = lean_io_error_to_string(v_a_2324_);
v___x_2329_ = 3;
v___x_2330_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2330_, 0, v___x_2328_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*1, v___x_2329_);
lean_inc_ref(v_a_2234_);
v___x_2331_ = lean_apply_2(v_a_2234_, v___x_2330_, lean_box(0));
v___x_2332_ = lean_box(0);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2332_);
v___x_2334_ = v___x_2326_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2349_; 
v_a_2337_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2339_ = v___x_2311_;
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2311_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2341_ = lean_io_error_to_string(v_a_2337_);
v___x_2342_ = 3;
v___x_2343_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*1, v___x_2342_);
lean_inc_ref(v_a_2234_);
v___x_2344_ = lean_apply_2(v_a_2234_, v___x_2343_, lean_box(0));
v___x_2345_ = lean_box(0);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2345_);
v___x_2347_ = v___x_2339_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2362_; 
v_a_2350_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2352_ = v___x_2309_;
v_isShared_2353_ = v_isSharedCheck_2362_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2309_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2362_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2354_ = lean_io_error_to_string(v_a_2350_);
v___x_2355_ = 3;
v___x_2356_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*1, v___x_2355_);
lean_inc_ref(v_a_2234_);
v___x_2357_ = lean_apply_2(v_a_2234_, v___x_2356_, lean_box(0));
v___x_2358_ = lean_box(0);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2358_);
v___x_2360_ = v___x_2352_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; 
lean_dec_ref_known(v_lakeArgs_x3f_2273_, 1);
lean_dec_ref(v___y_2286_);
lean_dec_ref(v_lakeEnv_2272_);
v___x_2363_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_2234_);
v___x_2364_ = lean_apply_2(v_a_2234_, v___x_2363_, lean_box(0));
v___x_2365_ = 4;
v___x_2366_ = lean_io_exit(v___x_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2387_; 
v_a_2375_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2377_ = v___x_2366_;
v_isShared_2378_ = v_isSharedCheck_2387_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2366_);
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
lean_inc_ref(v_a_2234_);
v___x_2382_ = lean_apply_2(v_a_2234_, v___x_2381_, lean_box(0));
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
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; 
lean_dec_ref(v___y_2286_);
lean_dec(v_lakeArgs_x3f_2273_);
lean_dec_ref(v_lakeEnv_2272_);
v___x_2388_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2234_);
v___x_2389_ = lean_apply_2(v_a_2234_, v___x_2388_, lean_box(0));
v___x_2390_ = 4;
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
lean_inc_ref(v_a_2234_);
v___x_2407_ = lean_apply_2(v_a_2234_, v___x_2406_, lean_box(0));
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
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2425_; 
lean_dec_ref(v___y_2286_);
lean_dec(v_lakeArgs_x3f_2273_);
lean_dec_ref(v_lakeEnv_2272_);
v_a_2413_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2415_ = v___x_2293_;
v_isShared_2416_ = v_isSharedCheck_2425_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2293_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2425_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2417_ = lean_io_error_to_string(v_a_2413_);
v___x_2418_ = 3;
v___x_2419_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2419_, 0, v___x_2417_);
lean_ctor_set_uint8(v___x_2419_, sizeof(void*)*1, v___x_2418_);
lean_inc_ref(v_a_2234_);
v___x_2420_ = lean_apply_2(v_a_2234_, v___x_2419_, lean_box(0));
v___x_2421_ = lean_box(0);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v___x_2421_);
v___x_2423_ = v___x_2415_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
v___jp_2426_:
{
uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v_toString_2431_; 
v___x_2429_ = 1;
v___x_2430_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2431_ = lean_ctor_get(v___y_2427_, 0);
lean_inc_ref(v_toString_2431_);
lean_dec_ref(v___y_2427_);
v___y_2283_ = v___x_2430_;
v___y_2284_ = v___x_2429_;
v___y_2285_ = v___y_2428_;
v___y_2286_ = v_toString_2431_;
goto v___jp_2282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2500_, lean_object* v_rootDeps_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2500_, v_rootDeps_2501_, v_a_2502_);
lean_dec_ref(v_a_2502_);
lean_dec_ref(v_rootDeps_2501_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2505_, lean_object* v_dep_2506_, lean_object* v_ws_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2507_, v_pkg_2505_, v_dep_2506_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v_fst_2513_; lean_object* v_snd_2514_; lean_object* v___x_2515_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v_fst_2513_ = lean_ctor_get(v_a_2512_, 0);
lean_inc_n(v_fst_2513_, 2);
v_snd_2514_ = lean_ctor_get(v_a_2512_, 1);
lean_inc(v_snd_2514_);
lean_dec(v_a_2512_);
v___x_2515_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2513_, v_snd_2514_, v_a_2509_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2532_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2532_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2532_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_snd_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2530_; 
v_snd_2520_ = lean_ctor_get(v_a_2516_, 1);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_a_2516_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v_a_2516_, 0);
lean_dec(v_unused_2531_);
v___x_2522_ = v_a_2516_;
v_isShared_2523_ = v_isSharedCheck_2530_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_snd_2520_);
lean_dec(v_a_2516_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2530_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 0, v_fst_2513_);
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_fst_2513_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_snd_2520_);
v___x_2525_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
lean_object* v___x_2527_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2525_);
v___x_2527_ = v___x_2518_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_fst_2513_);
v_a_2533_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2515_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2515_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2541_, lean_object* v_dep_2542_, lean_object* v_ws_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2541_, v_dep_2542_, v_ws_2543_, v_a_2544_, v_a_2545_);
lean_dec_ref(v_a_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2548_, lean_object* v_ws_2549_, lean_object* v_pkg_2550_, lean_object* v_dep_2551_, lean_object* v_a_2552_){
_start:
{
uint8_t v___y_2555_; lean_object* v___y_2556_; lean_object* v_name_2586_; lean_object* v___x_2587_; 
v_name_2586_ = lean_ctor_get(v_dep_2551_, 0);
v___x_2587_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2552_, v_name_2586_);
if (lean_obj_tag(v___x_2587_) == 1)
{
lean_object* v_val_2588_; lean_object* v_lakeEnv_2589_; lean_object* v_packages_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v_config_2593_; lean_object* v_dir_2594_; lean_object* v_toWorkspaceConfig_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_dec_ref(v_dep_2551_);
lean_dec_ref(v_pkg_2550_);
v_val_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_val_2588_);
lean_dec_ref_known(v___x_2587_, 1);
v_lakeEnv_2589_ = lean_ctor_get(v_ws_2549_, 0);
lean_inc_ref(v_lakeEnv_2589_);
v_packages_2590_ = lean_ctor_get(v_ws_2549_, 4);
lean_inc_ref(v_packages_2590_);
lean_dec_ref(v_ws_2549_);
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = lean_array_fget(v_packages_2590_, v___x_2591_);
lean_dec_ref(v_packages_2590_);
v_config_2593_ = lean_ctor_get(v___x_2592_, 6);
lean_inc_ref(v_config_2593_);
v_dir_2594_ = lean_ctor_get(v___x_2592_, 4);
lean_inc_ref(v_dir_2594_);
lean_dec(v___x_2592_);
v_toWorkspaceConfig_2595_ = lean_ctor_get(v_config_2593_, 0);
lean_inc_ref(v_toWorkspaceConfig_2595_);
lean_dec_ref(v_config_2593_);
v___x_2596_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2595_);
v___x_2597_ = l_Lake_PackageEntry_materialize(v_val_2588_, v_lakeEnv_2589_, v_dir_2594_, v___x_2596_, v___y_2548_);
lean_dec_ref(v_lakeEnv_2589_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2606_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2606_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2606_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2602_, 0, v_a_2598_);
lean_ctor_set(v___x_2602_, 1, v_a_2552_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2602_);
v___x_2604_ = v___x_2600_;
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
lean_dec(v_a_2552_);
v_a_2607_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2597_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2597_);
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
else
{
lean_object* v_wsIdx_2615_; lean_object* v_relDir_2616_; uint8_t v___y_2618_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
lean_dec(v___x_2587_);
v_wsIdx_2615_ = lean_ctor_get(v_pkg_2550_, 0);
lean_inc(v_wsIdx_2615_);
v_relDir_2616_ = lean_ctor_get(v_pkg_2550_, 5);
lean_inc_ref(v_relDir_2616_);
lean_dec_ref(v_pkg_2550_);
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_nat_dec_eq(v_wsIdx_2615_, v___x_2622_);
lean_dec(v_wsIdx_2615_);
if (v___x_2623_ == 0)
{
uint8_t v___x_2624_; 
v___x_2624_ = 1;
v___y_2618_ = v___x_2624_;
goto v___jp_2617_;
}
else
{
uint8_t v___x_2625_; 
v___x_2625_ = 0;
v___y_2618_ = v___x_2625_;
goto v___jp_2617_;
}
v___jp_2617_:
{
lean_object* v___x_2619_; uint8_t v___x_2620_; 
v___x_2619_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2620_ = lean_string_dec_eq(v_relDir_2616_, v___x_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lake_joinRelative(v_relDir_2616_, v___x_2619_);
v___y_2555_ = v___y_2618_;
v___y_2556_ = v___x_2621_;
goto v___jp_2554_;
}
else
{
v___y_2555_ = v___y_2618_;
v___y_2556_ = v_relDir_2616_;
goto v___jp_2554_;
}
}
}
v___jp_2554_:
{
lean_object* v_lakeEnv_2557_; lean_object* v_packages_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v_config_2561_; lean_object* v_dir_2562_; lean_object* v_toWorkspaceConfig_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_lakeEnv_2557_ = lean_ctor_get(v_ws_2549_, 0);
lean_inc_ref(v_lakeEnv_2557_);
v_packages_2558_ = lean_ctor_get(v_ws_2549_, 4);
lean_inc_ref(v_packages_2558_);
lean_dec_ref(v_ws_2549_);
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = lean_array_fget(v_packages_2558_, v___x_2559_);
lean_dec_ref(v_packages_2558_);
v_config_2561_ = lean_ctor_get(v___x_2560_, 6);
lean_inc_ref(v_config_2561_);
v_dir_2562_ = lean_ctor_get(v___x_2560_, 4);
lean_inc_ref(v_dir_2562_);
lean_dec(v___x_2560_);
v_toWorkspaceConfig_2563_ = lean_ctor_get(v_config_2561_, 0);
lean_inc_ref(v_toWorkspaceConfig_2563_);
lean_dec_ref(v_config_2561_);
v___x_2564_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2563_);
v___x_2565_ = l_Lake_Dependency_materialize(v_dep_2551_, v___y_2555_, v_lakeEnv_2557_, v_dir_2562_, v___x_2564_, v___y_2556_, v___y_2548_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2577_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2577_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2577_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_manifestEntry_2570_; lean_object* v_name_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v_manifestEntry_2570_ = lean_ctor_get(v_a_2566_, 4);
v_name_2571_ = lean_ctor_get(v_manifestEntry_2570_, 0);
lean_inc_ref(v_manifestEntry_2570_);
lean_inc(v_name_2571_);
v___x_2572_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2571_, v_manifestEntry_2570_, v_a_2552_);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v_a_2566_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2573_);
v___x_2575_ = v___x_2568_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v_a_2552_);
v_a_2578_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2565_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2565_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2626_, lean_object* v_ws_2627_, lean_object* v_pkg_2628_, lean_object* v_dep_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2626_, v_ws_2627_, v_pkg_2628_, v_dep_2629_, v_a_2630_);
lean_dec_ref(v___y_2626_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2633_, lean_object* v_dep_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v_manifestEntry_2637_; lean_object* v_pkgDir_2638_; lean_object* v_name_2639_; lean_object* v_manifestFile_x3f_2640_; lean_object* v___y_2642_; lean_object* v_fst_2643_; lean_object* v_snd_2644_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v_val_2696_; lean_object* v___y_2712_; 
v_manifestEntry_2637_ = lean_ctor_get(v_dep_2634_, 4);
v_pkgDir_2638_ = lean_ctor_get(v_dep_2634_, 0);
v_name_2639_ = lean_ctor_get(v_manifestEntry_2637_, 0);
v_manifestFile_x3f_2640_ = lean_ctor_get(v_manifestEntry_2637_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2640_) == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2638_);
v___x_2733_ = l_Lake_joinRelative(v_pkgDir_2638_, v___x_2732_);
v___y_2712_ = v___x_2733_;
goto v___jp_2711_;
}
else
{
lean_object* v_val_2734_; lean_object* v___x_2735_; 
v_val_2734_ = lean_ctor_get(v_manifestFile_x3f_2640_, 0);
lean_inc(v_val_2734_);
lean_inc_ref(v_pkgDir_2638_);
v___x_2735_ = l_Lake_joinRelative(v_pkgDir_2638_, v_val_2734_);
v___y_2712_ = v___x_2735_;
goto v___jp_2711_;
}
v___jp_2641_:
{
if (lean_obj_tag(v_fst_2643_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2674_; 
lean_inc(v_name_2639_);
lean_dec_ref(v_dep_2634_);
v_a_2645_ = lean_ctor_get(v_fst_2643_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_fst_2643_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2647_ = v_fst_2643_;
v_isShared_2648_ = v_isSharedCheck_2674_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v_fst_2643_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2674_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
if (lean_obj_tag(v_a_2645_) == 11)
{
uint8_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2659_; 
lean_dec_ref_known(v_a_2645_, 2);
v___x_2649_ = 0;
v___x_2650_ = l_Lean_Name_toString(v_name_2639_, v___x_2649_);
v___x_2651_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2652_ = lean_string_append(v___x_2650_, v___x_2651_);
v___x_2653_ = lean_string_append(v___x_2652_, v___y_2642_);
lean_dec_ref(v___y_2642_);
v___x_2654_ = 2;
v___x_2655_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set_uint8(v___x_2655_, sizeof(void*)*1, v___x_2654_);
v___x_2656_ = lean_apply_2(v___y_2633_, v___x_2655_, lean_box(0));
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
lean_ctor_set(v___x_2657_, 1, v_snd_2644_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2657_);
v___x_2659_ = v___x_2647_;
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
else
{
uint8_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
lean_dec_ref(v___y_2642_);
v___x_2661_ = 0;
v___x_2662_ = l_Lean_Name_toString(v_name_2639_, v___x_2661_);
v___x_2663_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2664_ = lean_string_append(v___x_2662_, v___x_2663_);
v___x_2665_ = lean_io_error_to_string(v_a_2645_);
v___x_2666_ = lean_string_append(v___x_2664_, v___x_2665_);
lean_dec_ref(v___x_2665_);
v___x_2667_ = 2;
v___x_2668_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*1, v___x_2667_);
v___x_2669_ = lean_apply_2(v___y_2633_, v___x_2668_, lean_box(0));
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v_snd_2644_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2670_);
v___x_2672_ = v___x_2647_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref(v___y_2642_);
lean_dec_ref(v___y_2633_);
v_a_2675_ = lean_ctor_get(v_fst_2643_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_fst_2643_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2677_ = v_fst_2643_;
v_isShared_2678_ = v_isSharedCheck_2691_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v_fst_2643_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2691_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v_packages_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v_packages_2679_ = lean_ctor_get(v_a_2675_, 3);
lean_inc_ref(v_packages_2679_);
lean_dec(v_a_2675_);
v___x_2680_ = lean_unsigned_to_nat(0u);
v___x_2681_ = lean_array_get_size(v_packages_2679_);
v___x_2682_ = lean_box(0);
v___x_2683_ = lean_nat_dec_lt(v___x_2680_, v___x_2681_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_dec_ref(v_packages_2679_);
lean_dec_ref(v_dep_2634_);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v_snd_2644_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2684_);
v___x_2686_ = v___x_2677_;
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
size_t v___x_2688_; size_t v___x_2689_; lean_object* v___x_2690_; 
lean_del_object(v___x_2677_);
v___x_2688_ = ((size_t)0ULL);
v___x_2689_ = lean_usize_of_nat(v___x_2681_);
v___x_2690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2634_, v_packages_2679_, v___x_2688_, v___x_2689_, v___x_2682_, v_snd_2644_);
lean_dec_ref(v_packages_2679_);
return v___x_2690_;
}
}
}
}
v___jp_2692_:
{
lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2697_ = lean_array_get_size(v___y_2693_);
v___x_2698_ = lean_nat_dec_lt(v___y_2694_, v___x_2697_);
if (v___x_2698_ == 0)
{
v___y_2642_ = v___y_2695_;
v_fst_2643_ = v_val_2696_;
v_snd_2644_ = v_a_2635_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2699_; size_t v___x_2700_; size_t v___x_2701_; lean_object* v___x_2702_; 
v___x_2699_ = lean_box(0);
v___x_2700_ = ((size_t)0ULL);
v___x_2701_ = lean_usize_of_nat(v___x_2697_);
v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2693_, v___x_2700_, v___x_2701_, v___x_2699_, v___y_2633_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_dec_ref_known(v___x_2702_, 1);
v___y_2642_ = v___y_2695_;
v_fst_2643_ = v_val_2696_;
v_snd_2644_ = v_a_2635_;
goto v___jp_2641_;
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref(v_val_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v_a_2635_);
lean_dec_ref(v_dep_2634_);
lean_dec_ref(v___y_2633_);
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2702_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
v___jp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2712_);
v___x_2715_ = l_Lake_Manifest_load(v___y_2712_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set_tag(v___x_2718_, 1);
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
v___y_2693_ = v___x_2714_;
v___y_2694_ = v___x_2713_;
v___y_2695_ = v___y_2712_;
v_val_2696_ = v___x_2721_;
goto v___jp_2692_;
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
v_a_2724_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2715_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2715_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set_tag(v___x_2726_, 0);
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
v___y_2693_ = v___x_2714_;
v___y_2694_ = v___x_2713_;
v___y_2695_ = v___y_2712_;
v_val_2696_ = v___x_2729_;
goto v___jp_2692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2736_, lean_object* v_dep_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2736_, v_dep_2737_, v_a_2738_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2745_, v___y_2743_, v___y_2741_, v___y_2742_, v___y_2744_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v_fst_2749_; lean_object* v_snd_2750_; lean_object* v___x_2751_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2747_, 1);
v_fst_2749_ = lean_ctor_get(v_a_2748_, 0);
lean_inc_n(v_fst_2749_, 2);
v_snd_2750_ = lean_ctor_get(v_a_2748_, 1);
lean_inc(v_snd_2750_);
lean_dec(v_a_2748_);
v___x_2751_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2745_, v_fst_2749_, v_snd_2750_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2768_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2768_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2768_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_snd_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2766_; 
v_snd_2756_ = lean_ctor_get(v_a_2752_, 1);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_a_2752_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; 
v_unused_2767_ = lean_ctor_get(v_a_2752_, 0);
lean_dec(v_unused_2767_);
v___x_2758_ = v_a_2752_;
v_isShared_2759_ = v_isSharedCheck_2766_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_snd_2756_);
lean_dec(v_a_2752_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2766_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v_fst_2749_);
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_fst_2749_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_snd_2756_);
v___x_2761_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
lean_object* v___x_2763_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2761_);
v___x_2763_ = v___x_2754_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_fst_2749_);
v_a_2769_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2751_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2751_);
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
else
{
lean_dec_ref(v___y_2745_);
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2784_, lean_object* v_ws_2785_, lean_object* v_toUpdate_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v___y_2790_; lean_object* v___y_2795_; lean_object* v_fst_2796_; lean_object* v_snd_2797_; lean_object* v_packages_2816_; lean_object* v___x_2817_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v_val_2822_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v_a_2841_; lean_object* v___x_2843_; lean_object* v_baseName_2844_; lean_object* v_dir_2845_; lean_object* v_config_2846_; lean_object* v_relManifestFile_2847_; lean_object* v_depConfigs_2848_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; uint8_t v_fst_2853_; lean_object* v_snd_2854_; lean_object* v_packagesDir_x3f_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; uint8_t v___x_2908_; lean_object* v_rootName_2909_; lean_object* v_fst_2911_; lean_object* v_snd_2912_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v_val_2979_; lean_object* v___x_2993_; 
v_packages_2816_ = lean_ctor_get(v_ws_2785_, 4);
v___x_2817_ = lean_unsigned_to_nat(0u);
v___x_2843_ = lean_array_fget_borrowed(v_packages_2816_, v___x_2817_);
v_baseName_2844_ = lean_ctor_get(v___x_2843_, 1);
v_dir_2845_ = lean_ctor_get(v___x_2843_, 4);
v_config_2846_ = lean_ctor_get(v___x_2843_, 6);
v_relManifestFile_2847_ = lean_ctor_get(v___x_2843_, 9);
v_depConfigs_2848_ = lean_ctor_get(v___x_2843_, 12);
v___x_2908_ = 0;
lean_inc(v_baseName_2844_);
v_rootName_2909_ = l_Lean_Name_toString(v_baseName_2844_, v___x_2908_);
lean_inc_ref(v_relManifestFile_2847_);
lean_inc_ref(v_dir_2845_);
v___x_2976_ = l_Lake_joinRelative(v_dir_2845_, v_relManifestFile_2847_);
v___x_2977_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2993_ = l_Lake_Manifest_load(v___x_2976_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set_tag(v___x_2996_, 1);
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
v_val_2979_ = v___x_2999_;
goto v___jp_2978_;
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
v_a_3002_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2993_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2993_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
lean_ctor_set_tag(v___x_3004_, 0);
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
v_val_2979_ = v___x_3007_;
goto v___jp_2978_;
}
}
}
v___jp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_box(0);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v___y_2790_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
v___jp_2794_:
{
if (lean_obj_tag(v_fst_2796_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2812_; 
lean_dec(v_snd_2797_);
v_a_2798_ = lean_ctor_get(v_fst_2796_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_fst_2796_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2800_ = v_fst_2796_;
v_isShared_2801_ = v_isSharedCheck_2812_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v_fst_2796_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2812_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2802_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2803_ = lean_io_error_to_string(v_a_2798_);
v___x_2804_ = lean_string_append(v___x_2802_, v___x_2803_);
lean_dec_ref(v___x_2803_);
v___x_2805_ = 3;
v___x_2806_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*1, v___x_2805_);
lean_inc_ref(v___y_2795_);
v___x_2807_ = lean_apply_2(v___y_2795_, v___x_2806_, lean_box(0));
v___x_2808_ = lean_box(0);
if (v_isShared_2801_ == 0)
{
lean_ctor_set_tag(v___x_2800_, 1);
lean_ctor_set(v___x_2800_, 0, v___x_2808_);
v___x_2810_ = v___x_2800_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
else
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_dec_ref(v_fst_2796_);
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v_snd_2797_);
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
return v___x_2815_;
}
}
v___jp_2818_:
{
lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = lean_array_get_size(v___y_2820_);
v___x_2824_ = lean_nat_dec_lt(v___x_2817_, v___x_2823_);
if (v___x_2824_ == 0)
{
v___y_2795_ = v___y_2821_;
v_fst_2796_ = v_val_2822_;
v_snd_2797_ = v___y_2819_;
goto v___jp_2794_;
}
else
{
lean_object* v___x_2825_; size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2825_ = lean_box(0);
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = lean_usize_of_nat(v___x_2823_);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___y_2820_, v___x_2826_, v___x_2827_, v___x_2825_, v___y_2821_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_dec_ref_known(v___x_2828_, 1);
v___y_2795_ = v___y_2821_;
v_fst_2796_ = v_val_2822_;
v_snd_2797_ = v___y_2819_;
goto v___jp_2794_;
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v_val_2822_);
lean_dec(v___y_2819_);
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2828_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
v___jp_2837_:
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_a_2841_);
v___y_2819_ = v___y_2839_;
v___y_2820_ = v___y_2838_;
v___y_2821_ = v___y_2840_;
v_val_2822_ = v___x_2842_;
goto v___jp_2818_;
}
v___jp_2849_:
{
lean_object* v_toWorkspaceConfig_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_toWorkspaceConfig_2855_ = lean_ctor_get(v_config_2846_, 0);
v___x_2856_ = l_System_FilePath_normalize(v___y_2850_);
lean_inc_ref(v_toWorkspaceConfig_2855_);
v___x_2857_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2855_);
lean_inc_ref(v___x_2857_);
v___x_2858_ = l_System_FilePath_normalize(v___x_2857_);
v___x_2859_ = lean_string_dec_eq(v___x_2856_, v___x_2858_);
lean_dec_ref(v___x_2858_);
lean_dec_ref(v___x_2856_);
if (v___x_2859_ == 0)
{
if (v_fst_2853_ == 0)
{
lean_dec_ref(v___x_2857_);
lean_dec_ref(v___y_2852_);
v___y_2790_ = v_snd_2854_;
goto v___jp_2789_;
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2860_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2861_ = lean_string_append(v___x_2860_, v___y_2852_);
v___x_2862_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2863_ = lean_string_append(v___x_2861_, v___x_2862_);
lean_inc_ref(v_dir_2845_);
v___x_2864_ = l_Lake_joinRelative(v_dir_2845_, v___x_2857_);
v___x_2865_ = lean_string_append(v___x_2863_, v___x_2864_);
v___x_2866_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2867_ = lean_string_append(v___x_2865_, v___x_2866_);
v___x_2868_ = 1;
v___x_2869_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set_uint8(v___x_2869_, sizeof(void*)*1, v___x_2868_);
lean_inc_ref(v___y_2851_);
v___x_2870_ = lean_apply_2(v___y_2851_, v___x_2869_, lean_box(0));
v___x_2871_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2864_);
v___x_2872_ = l_Lake_createParentDirs(v___x_2864_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v___x_2873_; 
lean_dec_ref_known(v___x_2872_, 1);
v___x_2873_ = lean_io_rename(v___y_2852_, v___x_2864_);
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___y_2852_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set_tag(v___x_2876_, 1);
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
v___y_2819_ = v_snd_2854_;
v___y_2820_ = v___x_2871_;
v___y_2821_ = v___y_2851_;
v_val_2822_ = v___x_2879_;
goto v___jp_2818_;
}
}
}
else
{
lean_object* v_a_2882_; 
v_a_2882_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2873_, 1);
v___y_2838_ = v___x_2871_;
v___y_2839_ = v_snd_2854_;
v___y_2840_ = v___y_2851_;
v_a_2841_ = v_a_2882_;
goto v___jp_2837_;
}
}
else
{
lean_object* v_a_2883_; 
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___y_2852_);
v_a_2883_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2872_, 1);
v___y_2838_ = v___x_2871_;
v___y_2839_ = v_snd_2854_;
v___y_2840_ = v___y_2851_;
v_a_2841_ = v_a_2883_;
goto v___jp_2837_;
}
}
}
else
{
lean_dec_ref(v___x_2857_);
lean_dec_ref(v___y_2852_);
v___y_2790_ = v_snd_2854_;
goto v___jp_2789_;
}
}
v___jp_2884_:
{
if (lean_obj_tag(v_packagesDir_x3f_2885_) == 1)
{
lean_object* v_val_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; uint8_t v___x_2892_; 
v_val_2888_ = lean_ctor_get(v_packagesDir_x3f_2885_, 0);
lean_inc_n(v_val_2888_, 2);
lean_dec_ref_known(v_packagesDir_x3f_2885_, 1);
lean_inc_ref(v_dir_2845_);
v___x_2889_ = l_Lake_joinRelative(v_dir_2845_, v_val_2888_);
v___x_2890_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2891_ = l_System_FilePath_pathExists(v___x_2889_);
v___x_2892_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2892_ == 0)
{
v___y_2850_ = v_val_2888_;
v___y_2851_ = v___y_2887_;
v___y_2852_ = v___x_2889_;
v_fst_2853_ = v___x_2891_;
v_snd_2854_ = v___y_2886_;
goto v___jp_2849_;
}
else
{
lean_object* v___x_2893_; size_t v___x_2894_; size_t v___x_2895_; lean_object* v___x_2896_; 
v___x_2893_ = lean_box(0);
v___x_2894_ = ((size_t)0ULL);
v___x_2895_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_2890_, v___x_2894_, v___x_2895_, v___x_2893_, v___y_2887_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_dec_ref_known(v___x_2896_, 1);
v___y_2850_ = v_val_2888_;
v___y_2851_ = v___y_2887_;
v___y_2852_ = v___x_2889_;
v_fst_2853_ = v___x_2891_;
v_snd_2854_ = v___y_2886_;
goto v___jp_2849_;
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v___x_2889_);
lean_dec(v_val_2888_);
lean_dec(v___y_2886_);
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec(v_packagesDir_x3f_2885_);
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
lean_ctor_set(v___x_2906_, 1, v___y_2886_);
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
return v___x_2907_;
}
}
v___jp_2910_:
{
if (lean_obj_tag(v_fst_2911_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2960_; 
v_a_2913_ = lean_ctor_get(v_fst_2911_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_fst_2911_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2915_ = v_fst_2911_;
v_isShared_2916_ = v_isSharedCheck_2960_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v_fst_2911_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2960_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
if (lean_obj_tag(v_a_2913_) == 11)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
lean_dec_ref_known(v_a_2913_, 2);
lean_del_object(v___x_2915_);
v___x_2917_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_2918_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_2786_, v_depConfigs_2848_, v___x_2817_, v___x_2917_, v_snd_2912_, v_a_2784_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2940_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2921_ = v___x_2918_;
v_isShared_2922_ = v_isSharedCheck_2940_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2918_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2940_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v_snd_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2938_; 
v_snd_2923_ = lean_ctor_get(v_a_2919_, 1);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_a_2919_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; 
v_unused_2939_ = lean_ctor_get(v_a_2919_, 0);
lean_dec(v_unused_2939_);
v___x_2925_ = v_a_2919_;
v_isShared_2926_ = v_isSharedCheck_2938_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_snd_2923_);
lean_dec(v_a_2919_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2938_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2927_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8));
v___x_2928_ = lean_string_append(v_rootName_2909_, v___x_2927_);
v___x_2929_ = 1;
v___x_2930_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set_uint8(v___x_2930_, sizeof(void*)*1, v___x_2929_);
lean_inc_ref(v_a_2784_);
v___x_2931_ = lean_apply_2(v_a_2784_, v___x_2930_, lean_box(0));
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2931_);
v___x_2933_ = v___x_2925_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2931_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_snd_2923_);
v___x_2933_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2935_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 0, v___x_2933_);
v___x_2935_ = v___x_2921_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2933_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_2909_);
return v___x_2918_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2786_) == 0)
{
lean_object* v___x_2941_; uint8_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2947_; 
lean_dec_ref_known(v_toUpdate_2786_, 5);
lean_dec(v_snd_2912_);
lean_dec_ref(v_rootName_2909_);
v___x_2941_ = lean_io_error_to_string(v_a_2913_);
v___x_2942_ = 3;
v___x_2943_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set_uint8(v___x_2943_, sizeof(void*)*1, v___x_2942_);
lean_inc_ref(v_a_2784_);
v___x_2944_ = lean_apply_2(v_a_2784_, v___x_2943_, lean_box(0));
v___x_2945_ = lean_box(0);
if (v_isShared_2916_ == 0)
{
lean_ctor_set_tag(v___x_2915_, 1);
lean_ctor_set(v___x_2915_, 0, v___x_2945_);
v___x_2947_ = v___x_2915_;
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
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2949_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_2950_ = lean_string_append(v_rootName_2909_, v___x_2949_);
v___x_2951_ = lean_io_error_to_string(v_a_2913_);
v___x_2952_ = lean_string_append(v___x_2950_, v___x_2951_);
lean_dec_ref(v___x_2951_);
v___x_2953_ = 2;
v___x_2954_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set_uint8(v___x_2954_, sizeof(void*)*1, v___x_2953_);
lean_inc_ref(v_a_2784_);
v___x_2955_ = lean_apply_2(v_a_2784_, v___x_2954_, lean_box(0));
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
lean_ctor_set(v___x_2956_, 1, v_snd_2912_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v___x_2956_);
v___x_2958_ = v___x_2915_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v_packagesDir_x3f_2962_; lean_object* v_packages_2963_; lean_object* v___x_2964_; 
lean_dec_ref(v_rootName_2909_);
v_a_2961_ = lean_ctor_get(v_fst_2911_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v_fst_2911_, 1);
v_packagesDir_x3f_2962_ = lean_ctor_get(v_a_2961_, 2);
lean_inc(v_packagesDir_x3f_2962_);
v_packages_2963_ = lean_ctor_get(v_a_2961_, 3);
lean_inc_ref(v_packages_2963_);
lean_dec(v_a_2961_);
lean_inc(v_toUpdate_2786_);
v___x_2964_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___lam__0(v_toUpdate_2786_, v_depConfigs_2848_, v___x_2817_, v_packages_2963_, v_snd_2912_, v_a_2784_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
if (lean_obj_tag(v_toUpdate_2786_) == 0)
{
lean_object* v_snd_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v_snd_2966_ = lean_ctor_get(v_a_2965_, 1);
lean_inc(v_snd_2966_);
lean_dec(v_a_2965_);
v___x_2967_ = lean_array_get_size(v_packages_2963_);
v___x_2968_ = lean_nat_dec_lt(v___x_2817_, v___x_2967_);
if (v___x_2968_ == 0)
{
lean_dec_ref_known(v_toUpdate_2786_, 5);
lean_dec_ref(v_packages_2963_);
v_packagesDir_x3f_2885_ = v_packagesDir_x3f_2962_;
v___y_2886_ = v_snd_2966_;
v___y_2887_ = v_a_2784_;
goto v___jp_2884_;
}
else
{
lean_object* v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; lean_object* v___x_2972_; 
v___x_2969_ = lean_box(0);
v___x_2970_ = ((size_t)0ULL);
v___x_2971_ = lean_usize_of_nat(v___x_2967_);
v___x_2972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__4___redArg(v_toUpdate_2786_, v_packages_2963_, v___x_2970_, v___x_2971_, v___x_2969_, v_snd_2966_);
lean_dec_ref(v_packages_2963_);
lean_dec_ref_known(v_toUpdate_2786_, 5);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v_snd_2974_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v_snd_2974_ = lean_ctor_get(v_a_2973_, 1);
lean_inc(v_snd_2974_);
lean_dec(v_a_2973_);
v_packagesDir_x3f_2885_ = v_packagesDir_x3f_2962_;
v___y_2886_ = v_snd_2974_;
v___y_2887_ = v_a_2784_;
goto v___jp_2884_;
}
else
{
lean_dec(v_packagesDir_x3f_2962_);
return v___x_2972_;
}
}
}
else
{
lean_object* v_snd_2975_; 
lean_dec_ref(v_packages_2963_);
v_snd_2975_ = lean_ctor_get(v_a_2965_, 1);
lean_inc(v_snd_2975_);
lean_dec(v_a_2965_);
v_packagesDir_x3f_2885_ = v_packagesDir_x3f_2962_;
v___y_2886_ = v_snd_2975_;
v___y_2887_ = v_a_2784_;
goto v___jp_2884_;
}
}
else
{
lean_dec_ref(v_packages_2963_);
lean_dec(v_packagesDir_x3f_2962_);
lean_dec(v_toUpdate_2786_);
return v___x_2964_;
}
}
}
v___jp_2978_:
{
uint8_t v___x_2980_; 
v___x_2980_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2980_ == 0)
{
v_fst_2911_ = v_val_2979_;
v_snd_2912_ = v_a_2787_;
goto v___jp_2910_;
}
else
{
lean_object* v___x_2981_; size_t v___x_2982_; size_t v___x_2983_; lean_object* v___x_2984_; 
v___x_2981_ = lean_box(0);
v___x_2982_ = ((size_t)0ULL);
v___x_2983_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
v___x_2984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v___x_2977_, v___x_2982_, v___x_2983_, v___x_2981_, v_a_2784_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_dec_ref_known(v___x_2984_, 1);
v_fst_2911_ = v_val_2979_;
v_snd_2912_ = v_a_2787_;
goto v___jp_2910_;
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec_ref(v_val_2979_);
lean_dec_ref(v_rootName_2909_);
lean_dec(v_a_2787_);
lean_dec(v_toUpdate_2786_);
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2984_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_3010_, lean_object* v_ws_3011_, lean_object* v_toUpdate_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_3010_, v_ws_3011_, v_toUpdate_3012_, v_a_3013_);
lean_dec_ref(v_ws_3011_);
lean_dec_ref(v_a_3010_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_a_3016_, lean_object* v_ws_3017_, lean_object* v_rootDeps_3018_){
_start:
{
lean_object* v___y_3021_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; uint8_t v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; uint8_t v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v_lakeEnv_3056_; lean_object* v_lakeArgs_x3f_3057_; lean_object* v_packages_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v_baseName_3061_; lean_object* v_dir_3062_; lean_object* v_config_3063_; lean_object* v___x_3064_; lean_object* v_rootToolchainFile_3065_; lean_object* v___y_3067_; uint8_t v___y_3068_; uint8_t v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3213_; uint8_t v___y_3214_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v_lakeEnv_3056_ = lean_ctor_get(v_ws_3017_, 0);
lean_inc_ref(v_lakeEnv_3056_);
v_lakeArgs_x3f_3057_ = lean_ctor_get(v_ws_3017_, 3);
lean_inc(v_lakeArgs_x3f_3057_);
v_packages_3058_ = lean_ctor_get(v_ws_3017_, 4);
lean_inc_ref(v_packages_3058_);
lean_dec_ref(v_ws_3017_);
v___x_3059_ = lean_unsigned_to_nat(0u);
v___x_3060_ = lean_array_fget(v_packages_3058_, v___x_3059_);
lean_dec_ref(v_packages_3058_);
v_baseName_3061_ = lean_ctor_get(v___x_3060_, 1);
lean_inc(v_baseName_3061_);
v_dir_3062_ = lean_ctor_get(v___x_3060_, 4);
lean_inc_ref_n(v_dir_3062_, 3);
v_config_3063_ = lean_ctor_get(v___x_3060_, 6);
lean_inc_ref(v_config_3063_);
lean_dec(v___x_3060_);
v___x_3064_ = l_Lake_toolchainFileName;
v_rootToolchainFile_3065_ = l_Lake_joinRelative(v_dir_3062_, v___x_3064_);
v___x_3218_ = l_System_FilePath_join(v_dir_3062_, v___x_3064_);
v___x_3219_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3218_);
lean_dec_ref(v___x_3218_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3272_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3272_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3272_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v_src_3225_; lean_object* v_tc_x3f_3226_; lean_object* v_clashes_3227_; uint8_t v_fixed_3228_; uint8_t v_fixedToolchain_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
v_fixedToolchain_3251_ = lean_ctor_get_uint8(v_config_3063_, sizeof(void*)*28 + 6);
lean_dec_ref(v_config_3063_);
v___x_3252_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___x_3253_ = lean_array_get_size(v_rootDeps_3018_);
v___x_3254_ = lean_nat_dec_lt(v___x_3059_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_dec_ref(v_dir_3062_);
lean_inc(v_a_3220_);
v_src_3225_ = v_baseName_3061_;
v_tc_x3f_3226_ = v_a_3220_;
v_clashes_3227_ = v___x_3252_;
v_fixed_3228_ = v_fixedToolchain_3251_;
goto v___jp_3224_;
}
else
{
lean_object* v___x_3255_; size_t v___x_3256_; size_t v___x_3257_; lean_object* v___x_3258_; 
lean_inc(v_a_3220_);
v___x_3255_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3255_, 0, v_baseName_3061_);
lean_ctor_set(v___x_3255_, 1, v_a_3220_);
lean_ctor_set(v___x_3255_, 2, v___x_3252_);
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*3, v_fixedToolchain_3251_);
v___x_3256_ = ((size_t)0ULL);
v___x_3257_ = lean_usize_of_nat(v___x_3253_);
v___x_3258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3062_, v_rootDeps_3018_, v___x_3256_, v___x_3257_, v___x_3255_, v_a_3016_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v_src_3260_; lean_object* v_tc_x3f_3261_; lean_object* v_clashes_3262_; uint8_t v_fixed_3263_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v_src_3260_ = lean_ctor_get(v_a_3259_, 0);
lean_inc(v_src_3260_);
v_tc_x3f_3261_ = lean_ctor_get(v_a_3259_, 1);
lean_inc(v_tc_x3f_3261_);
v_clashes_3262_ = lean_ctor_get(v_a_3259_, 2);
lean_inc_ref(v_clashes_3262_);
v_fixed_3263_ = lean_ctor_get_uint8(v_a_3259_, sizeof(void*)*3);
lean_dec(v_a_3259_);
v_src_3225_ = v_src_3260_;
v_tc_x3f_3226_ = v_tc_x3f_3261_;
v_clashes_3227_ = v_clashes_3262_;
v_fixed_3228_ = v_fixed_3263_;
goto v___jp_3224_;
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_del_object(v___x_3222_);
lean_dec(v_a_3220_);
lean_dec_ref(v_rootToolchainFile_3065_);
lean_dec(v_lakeArgs_x3f_3057_);
lean_dec_ref(v_lakeEnv_3056_);
v_a_3264_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3258_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3258_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
v___jp_3224_:
{
lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3229_ = lean_array_get_size(v_clashes_3227_);
v___x_3230_ = lean_nat_dec_lt(v___x_3059_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_dec_ref(v_clashes_3227_);
lean_dec(v_src_3225_);
if (lean_obj_tag(v_tc_x3f_3226_) == 1)
{
if (lean_obj_tag(v_a_3220_) == 0)
{
lean_object* v_val_3231_; 
lean_del_object(v___x_3222_);
v_val_3231_ = lean_ctor_get(v_tc_x3f_3226_, 0);
lean_inc(v_val_3231_);
lean_dec_ref_known(v_tc_x3f_3226_, 1);
v___y_3213_ = v_val_3231_;
v___y_3214_ = v___x_3230_;
goto v___jp_3212_;
}
else
{
lean_object* v_val_3232_; lean_object* v_val_3233_; uint8_t v___x_3234_; 
v_val_3232_ = lean_ctor_get(v_tc_x3f_3226_, 0);
lean_inc_n(v_val_3232_, 2);
lean_dec_ref_known(v_tc_x3f_3226_, 1);
v_val_3233_ = lean_ctor_get(v_a_3220_, 0);
lean_inc(v_val_3233_);
lean_dec_ref_known(v_a_3220_, 1);
v___x_3234_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3233_, v_val_3232_);
if (v___x_3234_ == 0)
{
lean_del_object(v___x_3222_);
v___y_3213_ = v_val_3232_;
v___y_3214_ = v___x_3234_;
goto v___jp_3212_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3239_; 
lean_dec(v_val_3232_);
lean_dec_ref(v_rootToolchainFile_3065_);
lean_dec(v_lakeArgs_x3f_3057_);
lean_dec_ref(v_lakeEnv_3056_);
v___x_3235_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__15));
lean_inc_ref(v_a_3016_);
v___x_3236_ = lean_apply_2(v_a_3016_, v___x_3235_, lean_box(0));
v___x_3237_ = lean_box(0);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3237_);
v___x_3239_ = v___x_3222_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_dec(v_tc_x3f_3226_);
lean_dec(v_a_3220_);
lean_dec_ref(v_rootToolchainFile_3065_);
lean_dec(v_lakeArgs_x3f_3057_);
lean_dec_ref(v_lakeEnv_3056_);
v___x_3241_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__17));
lean_inc_ref(v_a_3016_);
v___x_3242_ = lean_apply_2(v_a_3016_, v___x_3241_, lean_box(0));
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3242_);
v___x_3244_ = v___x_3222_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
else
{
lean_del_object(v___x_3222_);
lean_dec(v_a_3220_);
lean_dec_ref(v_rootToolchainFile_3065_);
lean_dec(v_lakeArgs_x3f_3057_);
lean_dec_ref(v_lakeEnv_3056_);
if (lean_obj_tag(v_tc_x3f_3226_) == 1)
{
if (v_fixed_3228_ == 0)
{
lean_object* v_val_3246_; lean_object* v___x_3247_; 
v_val_3246_ = lean_ctor_get(v_tc_x3f_3226_, 0);
lean_inc(v_val_3246_);
lean_dec_ref_known(v_tc_x3f_3226_, 1);
v___x_3247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3048_ = v___x_3229_;
v___y_3049_ = v_val_3246_;
v___y_3050_ = v_clashes_3227_;
v___y_3051_ = v___x_3230_;
v___y_3052_ = v_src_3225_;
v___y_3053_ = v___x_3247_;
goto v___jp_3047_;
}
else
{
lean_object* v_val_3248_; lean_object* v___x_3249_; 
v_val_3248_ = lean_ctor_get(v_tc_x3f_3226_, 0);
lean_inc(v_val_3248_);
lean_dec_ref_known(v_tc_x3f_3226_, 1);
v___x_3249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3048_ = v___x_3229_;
v___y_3049_ = v_val_3248_;
v___y_3050_ = v_clashes_3227_;
v___y_3051_ = v___x_3230_;
v___y_3052_ = v_src_3225_;
v___y_3053_ = v___x_3249_;
goto v___jp_3047_;
}
}
else
{
lean_object* v___x_3250_; 
lean_dec(v_tc_x3f_3226_);
lean_dec(v_src_3225_);
v___x_3250_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
v___y_3027_ = v___x_3229_;
v___y_3028_ = v_clashes_3227_;
v___y_3029_ = v___x_3250_;
goto v___jp_3026_;
}
}
}
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3285_; 
lean_dec_ref(v_rootToolchainFile_3065_);
lean_dec_ref(v_config_3063_);
lean_dec_ref(v_dir_3062_);
lean_dec(v_baseName_3061_);
lean_dec(v_lakeArgs_x3f_3057_);
lean_dec_ref(v_lakeEnv_3056_);
v_a_3273_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3275_ = v___x_3219_;
v_isShared_3276_ = v_isSharedCheck_3285_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3219_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3285_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3277_; uint8_t v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3277_ = lean_io_error_to_string(v_a_3273_);
v___x_3278_ = 3;
v___x_3279_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*1, v___x_3278_);
lean_inc_ref(v_a_3016_);
v___x_3280_ = lean_apply_2(v_a_3016_, v___x_3279_, lean_box(0));
v___x_3281_ = lean_box(0);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v___x_3281_);
v___x_3283_ = v___x_3275_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
v___jp_3020_:
{
uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3022_ = 2;
v___x_3023_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3023_, 0, v___y_3021_);
lean_ctor_set_uint8(v___x_3023_, sizeof(void*)*1, v___x_3022_);
lean_inc_ref(v_a_3016_);
v___x_3024_ = lean_apply_2(v_a_3016_, v___x_3023_, lean_box(0));
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
return v___x_3025_;
}
v___jp_3026_:
{
size_t v___x_3030_; size_t v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = ((size_t)0ULL);
v___x_3031_ = lean_usize_of_nat(v___y_3027_);
v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3027_, v___y_3028_, v___x_3030_, v___x_3031_, v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
v___y_3021_ = v___x_3032_;
goto v___jp_3020_;
}
v___jp_3033_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_inc_ref(v___y_3039_);
v___x_3041_ = lean_string_append(v___y_3039_, v___y_3040_);
lean_dec_ref(v___y_3040_);
v___x_3042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3043_ = lean_string_append(v___x_3041_, v___x_3042_);
v___x_3044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3038_, v___y_3037_);
v___x_3045_ = lean_string_append(v___x_3043_, v___x_3044_);
lean_dec_ref(v___x_3044_);
v___x_3046_ = lean_string_append(v___x_3045_, v___y_3036_);
if (v___y_3037_ == 0)
{
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
v___y_3021_ = v___x_3046_;
goto v___jp_3020_;
}
else
{
v___y_3027_ = v___y_3034_;
v___y_3028_ = v___y_3035_;
v___y_3029_ = v___x_3046_;
goto v___jp_3026_;
}
}
v___jp_3047_:
{
lean_object* v___x_3054_; lean_object* v_toString_3055_; 
v___x_3054_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__0));
v_toString_3055_ = lean_ctor_get(v___y_3049_, 0);
lean_inc_ref(v_toString_3055_);
lean_dec_ref(v___y_3049_);
v___y_3034_ = v___y_3048_;
v___y_3035_ = v___y_3050_;
v___y_3036_ = v___y_3053_;
v___y_3037_ = v___y_3051_;
v___y_3038_ = v___y_3052_;
v___y_3039_ = v___x_3054_;
v___y_3040_ = v_toString_3055_;
goto v___jp_3033_;
}
v___jp_3066_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_inc_ref(v___y_3067_);
v___x_3071_ = lean_string_append(v___y_3067_, v___y_3070_);
v___x_3072_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_3073_ = lean_string_append(v___x_3071_, v___x_3072_);
v___x_3074_ = 1;
v___x_3075_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set_uint8(v___x_3075_, sizeof(void*)*1, v___x_3074_);
lean_inc_ref(v_a_3016_);
v___x_3076_ = lean_apply_2(v_a_3016_, v___x_3075_, lean_box(0));
v___x_3077_ = l_IO_FS_writeFile(v_rootToolchainFile_3065_, v___y_3070_);
lean_dec_ref(v_rootToolchainFile_3065_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_dec_ref_known(v___x_3077_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_3057_) == 1)
{
lean_object* v_elan_x3f_3078_; 
v_elan_x3f_3078_ = lean_ctor_get(v_lakeEnv_3056_, 2);
if (lean_obj_tag(v_elan_x3f_3078_) == 1)
{
lean_object* v_val_3079_; lean_object* v_val_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v_elan_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_val_3079_ = lean_ctor_get(v_lakeArgs_x3f_3057_, 0);
lean_inc(v_val_3079_);
lean_dec_ref_known(v_lakeArgs_x3f_3057_, 1);
v_val_3080_ = lean_ctor_get(v_elan_x3f_3078_, 0);
v___x_3081_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
lean_inc_ref(v_a_3016_);
v___x_3082_ = lean_apply_2(v_a_3016_, v___x_3081_, lean_box(0));
v___x_3083_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v_elan_3084_ = lean_ctor_get(v_val_3080_, 1);
lean_inc_ref(v_elan_3084_);
v___x_3085_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6));
v___x_3086_ = lean_unsigned_to_nat(4u);
v___x_3087_ = lean_mk_empty_array_with_capacity(v___x_3086_);
lean_dec_ref(v___x_3087_);
v___x_3088_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__8);
v___x_3089_ = lean_array_push(v___x_3088_, v___y_3070_);
v___x_3090_ = lean_array_push(v___x_3089_, v___x_3085_);
v___x_3091_ = l_Array_append___redArg(v___x_3090_, v_val_3079_);
lean_dec(v_val_3079_);
v___x_3092_ = lean_box(0);
v___x_3093_ = l_Lake_Env_noToolchainVars(v_lakeEnv_3056_);
v___x_3094_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3094_, 0, v___x_3083_);
lean_ctor_set(v___x_3094_, 1, v_elan_3084_);
lean_ctor_set(v___x_3094_, 2, v___x_3091_);
lean_ctor_set(v___x_3094_, 3, v___x_3092_);
lean_ctor_set(v___x_3094_, 4, v___x_3093_);
lean_ctor_set_uint8(v___x_3094_, sizeof(void*)*5, v___y_3068_);
lean_ctor_set_uint8(v___x_3094_, sizeof(void*)*5 + 1, v___y_3069_);
v___x_3095_ = lean_io_process_spawn(v___x_3094_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = lean_io_process_child_wait(v___x_3083_, v_a_3096_);
lean_dec(v_a_3096_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; uint32_t v___x_3099_; uint8_t v___x_3100_; lean_object* v___x_3101_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v___x_3099_ = lean_unbox_uint32(v_a_3098_);
lean_dec(v_a_3098_);
v___x_3100_ = lean_uint32_to_uint8(v___x_3099_);
v___x_3101_ = lean_io_exit(v___x_3100_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3122_; 
v_a_3110_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3112_ = v___x_3101_;
v_isShared_3113_ = v_isSharedCheck_3122_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3101_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3122_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3114_ = lean_io_error_to_string(v_a_3110_);
v___x_3115_ = 3;
v___x_3116_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set_uint8(v___x_3116_, sizeof(void*)*1, v___x_3115_);
lean_inc_ref(v_a_3016_);
v___x_3117_ = lean_apply_2(v_a_3016_, v___x_3116_, lean_box(0));
v___x_3118_ = lean_box(0);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3118_);
v___x_3120_ = v___x_3112_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3135_; 
v_a_3123_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3125_ = v___x_3097_;
v_isShared_3126_ = v_isSharedCheck_3135_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3097_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3135_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; uint8_t v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3127_ = lean_io_error_to_string(v_a_3123_);
v___x_3128_ = 3;
v___x_3129_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set_uint8(v___x_3129_, sizeof(void*)*1, v___x_3128_);
lean_inc_ref(v_a_3016_);
v___x_3130_ = lean_apply_2(v_a_3016_, v___x_3129_, lean_box(0));
v___x_3131_ = lean_box(0);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v___x_3131_);
v___x_3133_ = v___x_3125_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3148_; 
v_a_3136_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3138_ = v___x_3095_;
v_isShared_3139_ = v_isSharedCheck_3148_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3095_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3148_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; uint8_t v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3140_ = lean_io_error_to_string(v_a_3136_);
v___x_3141_ = 3;
v___x_3142_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*1, v___x_3141_);
lean_inc_ref(v_a_3016_);
v___x_3143_ = lean_apply_2(v_a_3016_, v___x_3142_, lean_box(0));
v___x_3144_ = lean_box(0);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3144_);
v___x_3146_ = v___x_3138_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; lean_object* v___x_3152_; 
lean_dec_ref_known(v_lakeArgs_x3f_3057_, 1);
lean_dec_ref(v___y_3070_);
lean_dec_ref(v_lakeEnv_3056_);
v___x_3149_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10));
lean_inc_ref(v_a_3016_);
v___x_3150_ = lean_apply_2(v_a_3016_, v___x_3149_, lean_box(0));
v___x_3151_ = 4;
v___x_3152_ = lean_io_exit(v___x_3151_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3173_; 
v_a_3161_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3163_ = v___x_3152_;
v_isShared_3164_ = v_isSharedCheck_3173_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3152_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3173_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; uint8_t v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3165_ = lean_io_error_to_string(v_a_3161_);
v___x_3166_ = 3;
v___x_3167_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set_uint8(v___x_3167_, sizeof(void*)*1, v___x_3166_);
lean_inc_ref(v_a_3016_);
v___x_3168_ = lean_apply_2(v_a_3016_, v___x_3167_, lean_box(0));
v___x_3169_ = lean_box(0);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3169_);
v___x_3171_ = v___x_3163_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
else
{
lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; lean_object* v___x_3177_; 
lean_dec_ref(v___y_3070_);
lean_dec(v_lakeArgs_x3f_3057_);
lean_dec_ref(v_lakeEnv_3056_);
v___x_3174_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_3016_);
v___x_3175_ = lean_apply_2(v_a_3016_, v___x_3174_, lean_box(0));
v___x_3176_ = 4;
v___x_3177_ = lean_io_exit(v___x_3176_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3198_; 
v_a_3186_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3188_ = v___x_3177_;
v_isShared_3189_ = v_isSharedCheck_3198_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3177_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3198_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; uint8_t v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3190_ = lean_io_error_to_string(v_a_3186_);
v___x_3191_ = 3;
v___x_3192_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*1, v___x_3191_);
lean_inc_ref(v_a_3016_);
v___x_3193_ = lean_apply_2(v_a_3016_, v___x_3192_, lean_box(0));
v___x_3194_ = lean_box(0);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3194_);
v___x_3196_ = v___x_3188_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3211_; 
lean_dec_ref(v___y_3070_);
lean_dec(v_lakeArgs_x3f_3057_);
lean_dec_ref(v_lakeEnv_3056_);
v_a_3199_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3201_ = v___x_3077_;
v_isShared_3202_ = v_isSharedCheck_3211_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3077_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3211_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; uint8_t v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3203_ = lean_io_error_to_string(v_a_3199_);
v___x_3204_ = 3;
v___x_3205_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set_uint8(v___x_3205_, sizeof(void*)*1, v___x_3204_);
lean_inc_ref(v_a_3016_);
v___x_3206_ = lean_apply_2(v_a_3016_, v___x_3205_, lean_box(0));
v___x_3207_ = lean_box(0);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3207_);
v___x_3209_ = v___x_3201_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
v___jp_3212_:
{
uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v_toString_3217_; 
v___x_3215_ = 1;
v___x_3216_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_3217_ = lean_ctor_get(v___y_3213_, 0);
lean_inc_ref(v_toString_3217_);
lean_dec_ref(v___y_3213_);
v___y_3067_ = v___x_3216_;
v___y_3068_ = v___x_3215_;
v___y_3069_ = v___y_3214_;
v___y_3070_ = v_toString_3217_;
goto v___jp_3066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_a_3286_, lean_object* v_ws_3287_, lean_object* v_rootDeps_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3286_, v_ws_3287_, v_rootDeps_3288_);
lean_dec_ref(v_rootDeps_3288_);
lean_dec_ref(v_a_3286_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(lean_object* v_msg_3291_){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_box(1);
v___x_3293_ = lean_panic_fn_borrowed(v___x_3292_, v_msg_3291_);
return v___x_3293_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3297_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3298_ = lean_unsigned_to_nat(35u);
v___x_3299_ = lean_unsigned_to_nat(182u);
v___x_3300_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3301_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3302_ = l_mkPanicMessageWithDecl(v___x_3301_, v___x_3300_, v___x_3299_, v___x_3298_, v___x_3297_);
return v___x_3302_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3303_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3304_ = lean_unsigned_to_nat(21u);
v___x_3305_ = lean_unsigned_to_nat(183u);
v___x_3306_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3307_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3308_ = l_mkPanicMessageWithDecl(v___x_3307_, v___x_3306_, v___x_3305_, v___x_3304_, v___x_3303_);
return v___x_3308_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3311_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3312_ = lean_unsigned_to_nat(35u);
v___x_3313_ = lean_unsigned_to_nat(276u);
v___x_3314_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3315_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3316_ = l_mkPanicMessageWithDecl(v___x_3315_, v___x_3314_, v___x_3313_, v___x_3312_, v___x_3311_);
return v___x_3316_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3317_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3318_ = lean_unsigned_to_nat(21u);
v___x_3319_ = lean_unsigned_to_nat(277u);
v___x_3320_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3321_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3322_ = l_mkPanicMessageWithDecl(v___x_3321_, v___x_3320_, v___x_3319_, v___x_3318_, v___x_3317_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(lean_object* v_k_3323_, lean_object* v_v_3324_, lean_object* v_t_3325_){
_start:
{
if (lean_obj_tag(v_t_3325_) == 0)
{
lean_object* v_size_3326_; lean_object* v_k_3327_; lean_object* v_v_3328_; lean_object* v_l_3329_; lean_object* v_r_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3686_; 
v_size_3326_ = lean_ctor_get(v_t_3325_, 0);
v_k_3327_ = lean_ctor_get(v_t_3325_, 1);
v_v_3328_ = lean_ctor_get(v_t_3325_, 2);
v_l_3329_ = lean_ctor_get(v_t_3325_, 3);
v_r_3330_ = lean_ctor_get(v_t_3325_, 4);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_t_3325_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3332_ = v_t_3325_;
v_isShared_3333_ = v_isSharedCheck_3686_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_r_3330_);
lean_inc(v_l_3329_);
lean_inc(v_v_3328_);
lean_inc(v_k_3327_);
lean_inc(v_size_3326_);
lean_dec(v_t_3325_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3686_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
uint8_t v___x_3334_; 
v___x_3334_ = lean_string_compare(v_k_3323_, v_k_3327_);
switch(v___x_3334_)
{
case 0:
{
lean_object* v___x_3335_; 
lean_dec(v_size_3326_);
v___x_3335_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3323_, v_v_3324_, v_l_3329_);
if (lean_obj_tag(v_r_3330_) == 0)
{
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_size_3336_; lean_object* v_size_3337_; lean_object* v_k_3338_; lean_object* v_v_3339_; lean_object* v_l_3340_; lean_object* v_r_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v_size_3336_ = lean_ctor_get(v_r_3330_, 0);
v_size_3337_ = lean_ctor_get(v___x_3335_, 0);
v_k_3338_ = lean_ctor_get(v___x_3335_, 1);
v_v_3339_ = lean_ctor_get(v___x_3335_, 2);
v_l_3340_ = lean_ctor_get(v___x_3335_, 3);
v_r_3341_ = lean_ctor_get(v___x_3335_, 4);
lean_inc(v_r_3341_);
v___x_3342_ = lean_unsigned_to_nat(3u);
v___x_3343_ = lean_nat_mul(v___x_3342_, v_size_3336_);
v___x_3344_ = lean_nat_dec_lt(v___x_3343_, v_size_3337_);
lean_dec(v___x_3343_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3349_; 
lean_dec(v_r_3341_);
v___x_3345_ = lean_unsigned_to_nat(1u);
v___x_3346_ = lean_nat_add(v___x_3345_, v_size_3337_);
v___x_3347_ = lean_nat_add(v___x_3346_, v_size_3336_);
lean_dec(v___x_3346_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 3, v___x_3335_);
lean_ctor_set(v___x_3332_, 0, v___x_3347_);
v___x_3349_ = v___x_3332_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v_r_3330_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
else
{
lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3422_; 
lean_inc(v_l_3340_);
lean_inc(v_v_3339_);
lean_inc(v_k_3338_);
lean_inc(v_size_3337_);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; lean_object* v_unused_3424_; lean_object* v_unused_3425_; lean_object* v_unused_3426_; lean_object* v_unused_3427_; 
v_unused_3423_ = lean_ctor_get(v___x_3335_, 4);
lean_dec(v_unused_3423_);
v_unused_3424_ = lean_ctor_get(v___x_3335_, 3);
lean_dec(v_unused_3424_);
v_unused_3425_ = lean_ctor_get(v___x_3335_, 2);
lean_dec(v_unused_3425_);
v_unused_3426_ = lean_ctor_get(v___x_3335_, 1);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v___x_3335_, 0);
lean_dec(v_unused_3427_);
v___x_3352_ = v___x_3335_;
v_isShared_3353_ = v_isSharedCheck_3422_;
goto v_resetjp_3351_;
}
else
{
lean_dec(v___x_3335_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3422_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
if (lean_obj_tag(v_l_3340_) == 0)
{
if (lean_obj_tag(v_r_3341_) == 0)
{
lean_object* v_size_3354_; lean_object* v_size_3355_; lean_object* v_k_3356_; lean_object* v_v_3357_; lean_object* v_l_3358_; lean_object* v_r_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v_size_3354_ = lean_ctor_get(v_l_3340_, 0);
v_size_3355_ = lean_ctor_get(v_r_3341_, 0);
v_k_3356_ = lean_ctor_get(v_r_3341_, 1);
v_v_3357_ = lean_ctor_get(v_r_3341_, 2);
v_l_3358_ = lean_ctor_get(v_r_3341_, 3);
v_r_3359_ = lean_ctor_get(v_r_3341_, 4);
v___x_3360_ = lean_unsigned_to_nat(2u);
v___x_3361_ = lean_nat_mul(v___x_3360_, v_size_3354_);
v___x_3362_ = lean_nat_dec_lt(v_size_3355_, v___x_3361_);
lean_dec(v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3392_; 
lean_inc(v_r_3359_);
lean_inc(v_l_3358_);
lean_inc(v_v_3357_);
lean_inc(v_k_3356_);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_r_3341_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; lean_object* v_unused_3394_; lean_object* v_unused_3395_; lean_object* v_unused_3396_; lean_object* v_unused_3397_; 
v_unused_3393_ = lean_ctor_get(v_r_3341_, 4);
lean_dec(v_unused_3393_);
v_unused_3394_ = lean_ctor_get(v_r_3341_, 3);
lean_dec(v_unused_3394_);
v_unused_3395_ = lean_ctor_get(v_r_3341_, 2);
lean_dec(v_unused_3395_);
v_unused_3396_ = lean_ctor_get(v_r_3341_, 1);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_r_3341_, 0);
lean_dec(v_unused_3397_);
v___x_3364_ = v_r_3341_;
v_isShared_3365_ = v_isSharedCheck_3392_;
goto v_resetjp_3363_;
}
else
{
lean_dec(v_r_3341_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3392_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___x_3380_; lean_object* v___y_3382_; 
v___x_3366_ = lean_unsigned_to_nat(1u);
v___x_3367_ = lean_nat_add(v___x_3366_, v_size_3337_);
lean_dec(v_size_3337_);
v___x_3368_ = lean_nat_add(v___x_3367_, v_size_3336_);
lean_dec(v___x_3367_);
v___x_3380_ = lean_nat_add(v___x_3366_, v_size_3354_);
if (lean_obj_tag(v_l_3358_) == 0)
{
lean_object* v_size_3390_; 
v_size_3390_ = lean_ctor_get(v_l_3358_, 0);
lean_inc(v_size_3390_);
v___y_3382_ = v_size_3390_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3391_; 
v___x_3391_ = lean_unsigned_to_nat(0u);
v___y_3382_ = v___x_3391_;
goto v___jp_3381_;
}
v___jp_3369_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = lean_nat_add(v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 4, v_r_3330_);
lean_ctor_set(v___x_3364_, 3, v_r_3359_);
lean_ctor_set(v___x_3364_, 2, v_v_3328_);
lean_ctor_set(v___x_3364_, 1, v_k_3327_);
lean_ctor_set(v___x_3364_, 0, v___x_3373_);
v___x_3375_ = v___x_3364_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v_r_3359_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v_r_3330_);
v___x_3375_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 4, v___x_3375_);
lean_ctor_set(v___x_3352_, 3, v___y_3370_);
lean_ctor_set(v___x_3352_, 2, v_v_3357_);
lean_ctor_set(v___x_3352_, 1, v_k_3356_);
lean_ctor_set(v___x_3352_, 0, v___x_3368_);
v___x_3377_ = v___x_3352_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_k_3356_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_v_3357_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v___y_3370_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
v___jp_3381_:
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3383_ = lean_nat_add(v___x_3380_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec(v___x_3380_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_l_3358_);
lean_ctor_set(v___x_3332_, 3, v_l_3340_);
lean_ctor_set(v___x_3332_, 2, v_v_3339_);
lean_ctor_set(v___x_3332_, 1, v_k_3338_);
lean_ctor_set(v___x_3332_, 0, v___x_3383_);
v___x_3385_ = v___x_3332_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3389_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3389_, 3, v_l_3340_);
lean_ctor_set(v_reuseFailAlloc_3389_, 4, v_l_3358_);
v___x_3385_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_nat_add(v___x_3366_, v_size_3336_);
if (lean_obj_tag(v_r_3359_) == 0)
{
lean_object* v_size_3387_; 
v_size_3387_ = lean_ctor_get(v_r_3359_, 0);
lean_inc(v_size_3387_);
v___y_3370_ = v___x_3385_;
v___y_3371_ = v___x_3386_;
v___y_3372_ = v_size_3387_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3388_; 
v___x_3388_ = lean_unsigned_to_nat(0u);
v___y_3370_ = v___x_3385_;
v___y_3371_ = v___x_3386_;
v___y_3372_ = v___x_3388_;
goto v___jp_3369_;
}
}
}
}
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; 
lean_del_object(v___x_3332_);
v___x_3398_ = lean_unsigned_to_nat(1u);
v___x_3399_ = lean_nat_add(v___x_3398_, v_size_3337_);
lean_dec(v_size_3337_);
v___x_3400_ = lean_nat_add(v___x_3399_, v_size_3336_);
lean_dec(v___x_3399_);
v___x_3401_ = lean_nat_add(v___x_3398_, v_size_3336_);
v___x_3402_ = lean_nat_add(v___x_3401_, v_size_3355_);
lean_dec(v___x_3401_);
lean_inc_ref(v_r_3330_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 4, v_r_3330_);
lean_ctor_set(v___x_3352_, 3, v_r_3341_);
lean_ctor_set(v___x_3352_, 2, v_v_3328_);
lean_ctor_set(v___x_3352_, 1, v_k_3327_);
lean_ctor_set(v___x_3352_, 0, v___x_3402_);
v___x_3404_ = v___x_3352_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3417_, 3, v_r_3341_);
lean_ctor_set(v_reuseFailAlloc_3417_, 4, v_r_3330_);
v___x_3404_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
v_isSharedCheck_3411_ = !lean_is_exclusive(v_r_3330_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; lean_object* v_unused_3413_; lean_object* v_unused_3414_; lean_object* v_unused_3415_; lean_object* v_unused_3416_; 
v_unused_3412_ = lean_ctor_get(v_r_3330_, 4);
lean_dec(v_unused_3412_);
v_unused_3413_ = lean_ctor_get(v_r_3330_, 3);
lean_dec(v_unused_3413_);
v_unused_3414_ = lean_ctor_get(v_r_3330_, 2);
lean_dec(v_unused_3414_);
v_unused_3415_ = lean_ctor_get(v_r_3330_, 1);
lean_dec(v_unused_3415_);
v_unused_3416_ = lean_ctor_get(v_r_3330_, 0);
lean_dec(v_unused_3416_);
v___x_3406_ = v_r_3330_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_dec(v_r_3330_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 4, v___x_3404_);
lean_ctor_set(v___x_3406_, 3, v_l_3340_);
lean_ctor_set(v___x_3406_, 2, v_v_3339_);
lean_ctor_set(v___x_3406_, 1, v_k_3338_);
lean_ctor_set(v___x_3406_, 0, v___x_3400_);
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3410_, 3, v_l_3340_);
lean_ctor_set(v_reuseFailAlloc_3410_, 4, v___x_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec_ref_known(v_l_3340_, 5);
lean_del_object(v___x_3352_);
lean_dec(v_v_3339_);
lean_dec(v_k_3338_);
lean_dec(v_size_3337_);
lean_dec_ref_known(v_r_3330_, 5);
lean_del_object(v___x_3332_);
lean_dec(v_v_3328_);
lean_dec(v_k_3327_);
v___x_3418_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3);
v___x_3419_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3418_);
return v___x_3419_;
}
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_del_object(v___x_3352_);
lean_dec(v_r_3341_);
lean_dec(v_v_3339_);
lean_dec(v_k_3338_);
lean_dec(v_size_3337_);
lean_dec_ref_known(v_r_3330_, 5);
lean_del_object(v___x_3332_);
lean_dec(v_v_3328_);
lean_dec(v_k_3327_);
v___x_3420_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4);
v___x_3421_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3420_);
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_size_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3432_; 
v_size_3428_ = lean_ctor_get(v_r_3330_, 0);
v___x_3429_ = lean_unsigned_to_nat(1u);
v___x_3430_ = lean_nat_add(v___x_3429_, v_size_3428_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 3, v___x_3335_);
lean_ctor_set(v___x_3332_, 0, v___x_3430_);
v___x_3432_ = v___x_3332_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3430_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3433_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3433_, 3, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3433_, 4, v_r_3330_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
else
{
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_l_3434_; 
v_l_3434_ = lean_ctor_get(v___x_3335_, 3);
if (lean_obj_tag(v_l_3434_) == 0)
{
lean_object* v_r_3435_; 
lean_inc_ref(v_l_3434_);
v_r_3435_ = lean_ctor_get(v___x_3335_, 4);
lean_inc(v_r_3435_);
if (lean_obj_tag(v_r_3435_) == 0)
{
lean_object* v_size_3436_; lean_object* v_k_3437_; lean_object* v_v_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3452_; 
v_size_3436_ = lean_ctor_get(v___x_3335_, 0);
v_k_3437_ = lean_ctor_get(v___x_3335_, 1);
v_v_3438_ = lean_ctor_get(v___x_3335_, 2);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; lean_object* v_unused_3454_; 
v_unused_3453_ = lean_ctor_get(v___x_3335_, 4);
lean_dec(v_unused_3453_);
v_unused_3454_ = lean_ctor_get(v___x_3335_, 3);
lean_dec(v_unused_3454_);
v___x_3440_ = v___x_3335_;
v_isShared_3441_ = v_isSharedCheck_3452_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_v_3438_);
lean_inc(v_k_3437_);
lean_inc(v_size_3436_);
lean_dec(v___x_3335_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3452_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v_size_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
v_size_3442_ = lean_ctor_get(v_r_3435_, 0);
v___x_3443_ = lean_unsigned_to_nat(1u);
v___x_3444_ = lean_nat_add(v___x_3443_, v_size_3436_);
lean_dec(v_size_3436_);
v___x_3445_ = lean_nat_add(v___x_3443_, v_size_3442_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 4, v_r_3330_);
lean_ctor_set(v___x_3440_, 3, v_r_3435_);
lean_ctor_set(v___x_3440_, 2, v_v_3328_);
lean_ctor_set(v___x_3440_, 1, v_k_3327_);
lean_ctor_set(v___x_3440_, 0, v___x_3445_);
v___x_3447_ = v___x_3440_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3451_, 3, v_r_3435_);
lean_ctor_set(v_reuseFailAlloc_3451_, 4, v_r_3330_);
v___x_3447_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3449_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3447_);
lean_ctor_set(v___x_3332_, 3, v_l_3434_);
lean_ctor_set(v___x_3332_, 2, v_v_3438_);
lean_ctor_set(v___x_3332_, 1, v_k_3437_);
lean_ctor_set(v___x_3332_, 0, v___x_3444_);
v___x_3449_ = v___x_3332_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_k_3437_);
lean_ctor_set(v_reuseFailAlloc_3450_, 2, v_v_3438_);
lean_ctor_set(v_reuseFailAlloc_3450_, 3, v_l_3434_);
lean_ctor_set(v_reuseFailAlloc_3450_, 4, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
lean_object* v_k_3455_; lean_object* v_v_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3468_; 
v_k_3455_ = lean_ctor_get(v___x_3335_, 1);
v_v_3456_ = lean_ctor_get(v___x_3335_, 2);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; lean_object* v_unused_3470_; lean_object* v_unused_3471_; 
v_unused_3469_ = lean_ctor_get(v___x_3335_, 4);
lean_dec(v_unused_3469_);
v_unused_3470_ = lean_ctor_get(v___x_3335_, 3);
lean_dec(v_unused_3470_);
v_unused_3471_ = lean_ctor_get(v___x_3335_, 0);
lean_dec(v_unused_3471_);
v___x_3458_ = v___x_3335_;
v_isShared_3459_ = v_isSharedCheck_3468_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_v_3456_);
lean_inc(v_k_3455_);
lean_dec(v___x_3335_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3468_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3460_ = lean_unsigned_to_nat(3u);
v___x_3461_ = lean_unsigned_to_nat(1u);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 3, v_r_3435_);
lean_ctor_set(v___x_3458_, 2, v_v_3328_);
lean_ctor_set(v___x_3458_, 1, v_k_3327_);
lean_ctor_set(v___x_3458_, 0, v___x_3461_);
v___x_3463_ = v___x_3458_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3467_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3467_, 3, v_r_3435_);
lean_ctor_set(v_reuseFailAlloc_3467_, 4, v_r_3435_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3465_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3463_);
lean_ctor_set(v___x_3332_, 3, v_l_3434_);
lean_ctor_set(v___x_3332_, 2, v_v_3456_);
lean_ctor_set(v___x_3332_, 1, v_k_3455_);
lean_ctor_set(v___x_3332_, 0, v___x_3460_);
v___x_3465_ = v___x_3332_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3460_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_k_3455_);
lean_ctor_set(v_reuseFailAlloc_3466_, 2, v_v_3456_);
lean_ctor_set(v_reuseFailAlloc_3466_, 3, v_l_3434_);
lean_ctor_set(v_reuseFailAlloc_3466_, 4, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
else
{
lean_object* v_r_3472_; 
v_r_3472_ = lean_ctor_get(v___x_3335_, 4);
lean_inc(v_r_3472_);
if (lean_obj_tag(v_r_3472_) == 0)
{
lean_object* v_k_3473_; lean_object* v_v_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3498_; 
lean_inc(v_l_3434_);
v_k_3473_ = lean_ctor_get(v___x_3335_, 1);
v_v_3474_ = lean_ctor_get(v___x_3335_, 2);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; lean_object* v_unused_3500_; lean_object* v_unused_3501_; 
v_unused_3499_ = lean_ctor_get(v___x_3335_, 4);
lean_dec(v_unused_3499_);
v_unused_3500_ = lean_ctor_get(v___x_3335_, 3);
lean_dec(v_unused_3500_);
v_unused_3501_ = lean_ctor_get(v___x_3335_, 0);
lean_dec(v_unused_3501_);
v___x_3476_ = v___x_3335_;
v_isShared_3477_ = v_isSharedCheck_3498_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_v_3474_);
lean_inc(v_k_3473_);
lean_dec(v___x_3335_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3498_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v_k_3478_; lean_object* v_v_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3494_; 
v_k_3478_ = lean_ctor_get(v_r_3472_, 1);
v_v_3479_ = lean_ctor_get(v_r_3472_, 2);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_r_3472_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; lean_object* v_unused_3496_; lean_object* v_unused_3497_; 
v_unused_3495_ = lean_ctor_get(v_r_3472_, 4);
lean_dec(v_unused_3495_);
v_unused_3496_ = lean_ctor_get(v_r_3472_, 3);
lean_dec(v_unused_3496_);
v_unused_3497_ = lean_ctor_get(v_r_3472_, 0);
lean_dec(v_unused_3497_);
v___x_3481_ = v_r_3472_;
v_isShared_3482_ = v_isSharedCheck_3494_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_v_3479_);
lean_inc(v_k_3478_);
lean_dec(v_r_3472_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3494_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3483_ = lean_unsigned_to_nat(3u);
v___x_3484_ = lean_unsigned_to_nat(1u);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v_l_3434_);
lean_ctor_set(v___x_3481_, 3, v_l_3434_);
lean_ctor_set(v___x_3481_, 2, v_v_3474_);
lean_ctor_set(v___x_3481_, 1, v_k_3473_);
lean_ctor_set(v___x_3481_, 0, v___x_3484_);
v___x_3486_ = v___x_3481_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_k_3473_);
lean_ctor_set(v_reuseFailAlloc_3493_, 2, v_v_3474_);
lean_ctor_set(v_reuseFailAlloc_3493_, 3, v_l_3434_);
lean_ctor_set(v_reuseFailAlloc_3493_, 4, v_l_3434_);
v___x_3486_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3488_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v_l_3434_);
lean_ctor_set(v___x_3476_, 2, v_v_3328_);
lean_ctor_set(v___x_3476_, 1, v_k_3327_);
lean_ctor_set(v___x_3476_, 0, v___x_3484_);
v___x_3488_ = v___x_3476_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3492_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3492_, 3, v_l_3434_);
lean_ctor_set(v_reuseFailAlloc_3492_, 4, v_l_3434_);
v___x_3488_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3490_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3488_);
lean_ctor_set(v___x_3332_, 3, v___x_3486_);
lean_ctor_set(v___x_3332_, 2, v_v_3479_);
lean_ctor_set(v___x_3332_, 1, v_k_3478_);
lean_ctor_set(v___x_3332_, 0, v___x_3483_);
v___x_3490_ = v___x_3332_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_k_3478_);
lean_ctor_set(v_reuseFailAlloc_3491_, 2, v_v_3479_);
lean_ctor_set(v_reuseFailAlloc_3491_, 3, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3491_, 4, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3502_ = lean_unsigned_to_nat(2u);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_r_3472_);
lean_ctor_set(v___x_3332_, 3, v___x_3335_);
lean_ctor_set(v___x_3332_, 0, v___x_3502_);
v___x_3504_ = v___x_3332_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3505_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3505_, 3, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3505_, 4, v_r_3472_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
v___x_3506_ = lean_unsigned_to_nat(1u);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3335_);
lean_ctor_set(v___x_3332_, 3, v___x_3335_);
lean_ctor_set(v___x_3332_, 0, v___x_3506_);
v___x_3508_ = v___x_3332_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3509_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3509_, 3, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3509_, 4, v___x_3335_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
case 1:
{
lean_object* v___x_3511_; 
lean_dec(v_v_3328_);
lean_dec(v_k_3327_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 2, v_v_3324_);
lean_ctor_set(v___x_3332_, 1, v_k_3323_);
v___x_3511_ = v___x_3332_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_size_3326_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_k_3323_);
lean_ctor_set(v_reuseFailAlloc_3512_, 2, v_v_3324_);
lean_ctor_set(v_reuseFailAlloc_3512_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3512_, 4, v_r_3330_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
default: 
{
lean_object* v___x_3513_; 
lean_dec(v_size_3326_);
v___x_3513_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3323_, v_v_3324_, v_r_3330_);
if (lean_obj_tag(v_l_3329_) == 0)
{
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_size_3514_; lean_object* v_size_3515_; lean_object* v_k_3516_; lean_object* v_v_3517_; lean_object* v_l_3518_; lean_object* v_r_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v_size_3514_ = lean_ctor_get(v_l_3329_, 0);
v_size_3515_ = lean_ctor_get(v___x_3513_, 0);
v_k_3516_ = lean_ctor_get(v___x_3513_, 1);
v_v_3517_ = lean_ctor_get(v___x_3513_, 2);
v_l_3518_ = lean_ctor_get(v___x_3513_, 3);
lean_inc(v_l_3518_);
v_r_3519_ = lean_ctor_get(v___x_3513_, 4);
v___x_3520_ = lean_unsigned_to_nat(3u);
v___x_3521_ = lean_nat_mul(v___x_3520_, v_size_3514_);
v___x_3522_ = lean_nat_dec_lt(v___x_3521_, v_size_3515_);
lean_dec(v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
lean_dec(v_l_3518_);
v___x_3523_ = lean_unsigned_to_nat(1u);
v___x_3524_ = lean_nat_add(v___x_3523_, v_size_3514_);
v___x_3525_ = lean_nat_add(v___x_3524_, v_size_3515_);
lean_dec(v___x_3524_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3513_);
lean_ctor_set(v___x_3332_, 0, v___x_3525_);
v___x_3527_ = v___x_3332_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3528_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3528_, 4, v___x_3513_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
else
{
lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3598_; 
lean_inc(v_r_3519_);
lean_inc(v_v_3517_);
lean_inc(v_k_3516_);
lean_inc(v_size_3515_);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; lean_object* v_unused_3600_; lean_object* v_unused_3601_; lean_object* v_unused_3602_; lean_object* v_unused_3603_; 
v_unused_3599_ = lean_ctor_get(v___x_3513_, 4);
lean_dec(v_unused_3599_);
v_unused_3600_ = lean_ctor_get(v___x_3513_, 3);
lean_dec(v_unused_3600_);
v_unused_3601_ = lean_ctor_get(v___x_3513_, 2);
lean_dec(v_unused_3601_);
v_unused_3602_ = lean_ctor_get(v___x_3513_, 1);
lean_dec(v_unused_3602_);
v_unused_3603_ = lean_ctor_get(v___x_3513_, 0);
lean_dec(v_unused_3603_);
v___x_3530_ = v___x_3513_;
v_isShared_3531_ = v_isSharedCheck_3598_;
goto v_resetjp_3529_;
}
else
{
lean_dec(v___x_3513_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3598_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
if (lean_obj_tag(v_l_3518_) == 0)
{
if (lean_obj_tag(v_r_3519_) == 0)
{
lean_object* v_size_3532_; lean_object* v_k_3533_; lean_object* v_v_3534_; lean_object* v_l_3535_; lean_object* v_r_3536_; lean_object* v_size_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v_size_3532_ = lean_ctor_get(v_l_3518_, 0);
v_k_3533_ = lean_ctor_get(v_l_3518_, 1);
v_v_3534_ = lean_ctor_get(v_l_3518_, 2);
v_l_3535_ = lean_ctor_get(v_l_3518_, 3);
v_r_3536_ = lean_ctor_get(v_l_3518_, 4);
v_size_3537_ = lean_ctor_get(v_r_3519_, 0);
v___x_3538_ = lean_unsigned_to_nat(2u);
v___x_3539_ = lean_nat_mul(v___x_3538_, v_size_3537_);
v___x_3540_ = lean_nat_dec_lt(v_size_3532_, v___x_3539_);
lean_dec(v___x_3539_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3569_; 
lean_inc(v_r_3536_);
lean_inc(v_l_3535_);
lean_inc(v_v_3534_);
lean_inc(v_k_3533_);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_l_3518_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; lean_object* v_unused_3571_; lean_object* v_unused_3572_; lean_object* v_unused_3573_; lean_object* v_unused_3574_; 
v_unused_3570_ = lean_ctor_get(v_l_3518_, 4);
lean_dec(v_unused_3570_);
v_unused_3571_ = lean_ctor_get(v_l_3518_, 3);
lean_dec(v_unused_3571_);
v_unused_3572_ = lean_ctor_get(v_l_3518_, 2);
lean_dec(v_unused_3572_);
v_unused_3573_ = lean_ctor_get(v_l_3518_, 1);
lean_dec(v_unused_3573_);
v_unused_3574_ = lean_ctor_get(v_l_3518_, 0);
lean_dec(v_unused_3574_);
v___x_3542_ = v_l_3518_;
v_isShared_3543_ = v_isSharedCheck_3569_;
goto v_resetjp_3541_;
}
else
{
lean_dec(v_l_3518_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3569_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3559_; 
v___x_3544_ = lean_unsigned_to_nat(1u);
v___x_3545_ = lean_nat_add(v___x_3544_, v_size_3514_);
v___x_3546_ = lean_nat_add(v___x_3545_, v_size_3515_);
lean_dec(v_size_3515_);
if (lean_obj_tag(v_l_3535_) == 0)
{
lean_object* v_size_3567_; 
v_size_3567_ = lean_ctor_get(v_l_3535_, 0);
lean_inc(v_size_3567_);
v___y_3559_ = v_size_3567_;
goto v___jp_3558_;
}
else
{
lean_object* v___x_3568_; 
v___x_3568_ = lean_unsigned_to_nat(0u);
v___y_3559_ = v___x_3568_;
goto v___jp_3558_;
}
v___jp_3547_:
{
lean_object* v___x_3551_; lean_object* v___x_3553_; 
v___x_3551_ = lean_nat_add(v___y_3549_, v___y_3550_);
lean_dec(v___y_3550_);
lean_dec(v___y_3549_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v_r_3519_);
lean_ctor_set(v___x_3542_, 3, v_r_3536_);
lean_ctor_set(v___x_3542_, 2, v_v_3517_);
lean_ctor_set(v___x_3542_, 1, v_k_3516_);
lean_ctor_set(v___x_3542_, 0, v___x_3551_);
v___x_3553_ = v___x_3542_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_r_3536_);
lean_ctor_set(v_reuseFailAlloc_3557_, 4, v_r_3519_);
v___x_3553_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3555_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 4, v___x_3553_);
lean_ctor_set(v___x_3530_, 3, v___y_3548_);
lean_ctor_set(v___x_3530_, 2, v_v_3534_);
lean_ctor_set(v___x_3530_, 1, v_k_3533_);
lean_ctor_set(v___x_3530_, 0, v___x_3546_);
v___x_3555_ = v___x_3530_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v_k_3533_);
lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_v_3534_);
lean_ctor_set(v_reuseFailAlloc_3556_, 3, v___y_3548_);
lean_ctor_set(v_reuseFailAlloc_3556_, 4, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
v___jp_3558_:
{
lean_object* v___x_3560_; lean_object* v___x_3562_; 
v___x_3560_ = lean_nat_add(v___x_3545_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec(v___x_3545_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_l_3535_);
lean_ctor_set(v___x_3332_, 0, v___x_3560_);
v___x_3562_ = v___x_3332_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3566_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3566_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3566_, 4, v_l_3535_);
v___x_3562_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_nat_add(v___x_3544_, v_size_3537_);
if (lean_obj_tag(v_r_3536_) == 0)
{
lean_object* v_size_3564_; 
v_size_3564_ = lean_ctor_get(v_r_3536_, 0);
lean_inc(v_size_3564_);
v___y_3548_ = v___x_3562_;
v___y_3549_ = v___x_3563_;
v___y_3550_ = v_size_3564_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3565_; 
v___x_3565_ = lean_unsigned_to_nat(0u);
v___y_3548_ = v___x_3562_;
v___y_3549_ = v___x_3563_;
v___y_3550_ = v___x_3565_;
goto v___jp_3547_;
}
}
}
}
}
else
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
lean_del_object(v___x_3332_);
v___x_3575_ = lean_unsigned_to_nat(1u);
v___x_3576_ = lean_nat_add(v___x_3575_, v_size_3514_);
v___x_3577_ = lean_nat_add(v___x_3576_, v_size_3515_);
lean_dec(v_size_3515_);
v___x_3578_ = lean_nat_add(v___x_3576_, v_size_3532_);
lean_dec(v___x_3576_);
lean_inc_ref(v_l_3329_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 4, v_l_3518_);
lean_ctor_set(v___x_3530_, 3, v_l_3329_);
lean_ctor_set(v___x_3530_, 2, v_v_3328_);
lean_ctor_set(v___x_3530_, 1, v_k_3327_);
lean_ctor_set(v___x_3530_, 0, v___x_3578_);
v___x_3580_ = v___x_3530_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3593_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3593_, 4, v_l_3518_);
v___x_3580_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
v_isSharedCheck_3587_ = !lean_is_exclusive(v_l_3329_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; lean_object* v_unused_3589_; lean_object* v_unused_3590_; lean_object* v_unused_3591_; lean_object* v_unused_3592_; 
v_unused_3588_ = lean_ctor_get(v_l_3329_, 4);
lean_dec(v_unused_3588_);
v_unused_3589_ = lean_ctor_get(v_l_3329_, 3);
lean_dec(v_unused_3589_);
v_unused_3590_ = lean_ctor_get(v_l_3329_, 2);
lean_dec(v_unused_3590_);
v_unused_3591_ = lean_ctor_get(v_l_3329_, 1);
lean_dec(v_unused_3591_);
v_unused_3592_ = lean_ctor_get(v_l_3329_, 0);
lean_dec(v_unused_3592_);
v___x_3582_ = v_l_3329_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_dec(v_l_3329_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 4, v_r_3519_);
lean_ctor_set(v___x_3582_, 3, v___x_3580_);
lean_ctor_set(v___x_3582_, 2, v_v_3517_);
lean_ctor_set(v___x_3582_, 1, v_k_3516_);
lean_ctor_set(v___x_3582_, 0, v___x_3577_);
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3586_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3586_, 3, v___x_3580_);
lean_ctor_set(v_reuseFailAlloc_3586_, 4, v_r_3519_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
lean_dec_ref_known(v_l_3518_, 5);
lean_del_object(v___x_3530_);
lean_dec(v_v_3517_);
lean_dec(v_k_3516_);
lean_dec(v_size_3515_);
lean_dec_ref_known(v_l_3329_, 5);
lean_del_object(v___x_3332_);
lean_dec(v_v_3328_);
lean_dec(v_k_3327_);
v___x_3594_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7);
v___x_3595_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3594_);
return v___x_3595_;
}
}
else
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
lean_del_object(v___x_3530_);
lean_dec(v_r_3519_);
lean_dec(v_v_3517_);
lean_dec(v_k_3516_);
lean_dec(v_size_3515_);
lean_dec_ref_known(v_l_3329_, 5);
lean_del_object(v___x_3332_);
lean_dec(v_v_3328_);
lean_dec(v_k_3327_);
v___x_3596_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8);
v___x_3597_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3596_);
return v___x_3597_;
}
}
}
}
else
{
lean_object* v_size_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v_size_3604_ = lean_ctor_get(v_l_3329_, 0);
v___x_3605_ = lean_unsigned_to_nat(1u);
v___x_3606_ = lean_nat_add(v___x_3605_, v_size_3604_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3513_);
lean_ctor_set(v___x_3332_, 0, v___x_3606_);
v___x_3608_ = v___x_3332_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3609_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3609_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3609_, 4, v___x_3513_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
else
{
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_l_3610_; 
v_l_3610_ = lean_ctor_get(v___x_3513_, 3);
lean_inc(v_l_3610_);
if (lean_obj_tag(v_l_3610_) == 0)
{
lean_object* v_r_3611_; 
v_r_3611_ = lean_ctor_get(v___x_3513_, 4);
lean_inc(v_r_3611_);
if (lean_obj_tag(v_r_3611_) == 0)
{
lean_object* v_size_3612_; lean_object* v_k_3613_; lean_object* v_v_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3628_; 
v_size_3612_ = lean_ctor_get(v___x_3513_, 0);
v_k_3613_ = lean_ctor_get(v___x_3513_, 1);
v_v_3614_ = lean_ctor_get(v___x_3513_, 2);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; lean_object* v_unused_3630_; 
v_unused_3629_ = lean_ctor_get(v___x_3513_, 4);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v___x_3513_, 3);
lean_dec(v_unused_3630_);
v___x_3616_ = v___x_3513_;
v_isShared_3617_ = v_isSharedCheck_3628_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_v_3614_);
lean_inc(v_k_3613_);
lean_inc(v_size_3612_);
lean_dec(v___x_3513_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3628_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v_size_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3623_; 
v_size_3618_ = lean_ctor_get(v_l_3610_, 0);
v___x_3619_ = lean_unsigned_to_nat(1u);
v___x_3620_ = lean_nat_add(v___x_3619_, v_size_3612_);
lean_dec(v_size_3612_);
v___x_3621_ = lean_nat_add(v___x_3619_, v_size_3618_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 4, v_l_3610_);
lean_ctor_set(v___x_3616_, 3, v_l_3329_);
lean_ctor_set(v___x_3616_, 2, v_v_3328_);
lean_ctor_set(v___x_3616_, 1, v_k_3327_);
lean_ctor_set(v___x_3616_, 0, v___x_3621_);
v___x_3623_ = v___x_3616_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3627_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3627_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3627_, 4, v_l_3610_);
v___x_3623_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3625_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_r_3611_);
lean_ctor_set(v___x_3332_, 3, v___x_3623_);
lean_ctor_set(v___x_3332_, 2, v_v_3614_);
lean_ctor_set(v___x_3332_, 1, v_k_3613_);
lean_ctor_set(v___x_3332_, 0, v___x_3620_);
v___x_3625_ = v___x_3332_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_k_3613_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_v_3614_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_r_3611_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
else
{
lean_object* v_k_3631_; lean_object* v_v_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3656_; 
v_k_3631_ = lean_ctor_get(v___x_3513_, 1);
v_v_3632_ = lean_ctor_get(v___x_3513_, 2);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3656_ == 0)
{
lean_object* v_unused_3657_; lean_object* v_unused_3658_; lean_object* v_unused_3659_; 
v_unused_3657_ = lean_ctor_get(v___x_3513_, 4);
lean_dec(v_unused_3657_);
v_unused_3658_ = lean_ctor_get(v___x_3513_, 3);
lean_dec(v_unused_3658_);
v_unused_3659_ = lean_ctor_get(v___x_3513_, 0);
lean_dec(v_unused_3659_);
v___x_3634_ = v___x_3513_;
v_isShared_3635_ = v_isSharedCheck_3656_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_v_3632_);
lean_inc(v_k_3631_);
lean_dec(v___x_3513_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3656_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v_k_3636_; lean_object* v_v_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3652_; 
v_k_3636_ = lean_ctor_get(v_l_3610_, 1);
v_v_3637_ = lean_ctor_get(v_l_3610_, 2);
v_isSharedCheck_3652_ = !lean_is_exclusive(v_l_3610_);
if (v_isSharedCheck_3652_ == 0)
{
lean_object* v_unused_3653_; lean_object* v_unused_3654_; lean_object* v_unused_3655_; 
v_unused_3653_ = lean_ctor_get(v_l_3610_, 4);
lean_dec(v_unused_3653_);
v_unused_3654_ = lean_ctor_get(v_l_3610_, 3);
lean_dec(v_unused_3654_);
v_unused_3655_ = lean_ctor_get(v_l_3610_, 0);
lean_dec(v_unused_3655_);
v___x_3639_ = v_l_3610_;
v_isShared_3640_ = v_isSharedCheck_3652_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_v_3637_);
lean_inc(v_k_3636_);
lean_dec(v_l_3610_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3652_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3644_; 
v___x_3641_ = lean_unsigned_to_nat(3u);
v___x_3642_ = lean_unsigned_to_nat(1u);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 4, v_r_3611_);
lean_ctor_set(v___x_3639_, 3, v_r_3611_);
lean_ctor_set(v___x_3639_, 2, v_v_3328_);
lean_ctor_set(v___x_3639_, 1, v_k_3327_);
lean_ctor_set(v___x_3639_, 0, v___x_3642_);
v___x_3644_ = v___x_3639_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_r_3611_);
lean_ctor_set(v_reuseFailAlloc_3651_, 4, v_r_3611_);
v___x_3644_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3646_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 3, v_r_3611_);
lean_ctor_set(v___x_3634_, 0, v___x_3642_);
v___x_3646_ = v___x_3634_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_k_3631_);
lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_v_3632_);
lean_ctor_set(v_reuseFailAlloc_3650_, 3, v_r_3611_);
lean_ctor_set(v_reuseFailAlloc_3650_, 4, v_r_3611_);
v___x_3646_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3648_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3646_);
lean_ctor_set(v___x_3332_, 3, v___x_3644_);
lean_ctor_set(v___x_3332_, 2, v_v_3637_);
lean_ctor_set(v___x_3332_, 1, v_k_3636_);
lean_ctor_set(v___x_3332_, 0, v___x_3641_);
v___x_3648_ = v___x_3332_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_k_3636_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v_v_3637_);
lean_ctor_set(v_reuseFailAlloc_3649_, 3, v___x_3644_);
lean_ctor_set(v_reuseFailAlloc_3649_, 4, v___x_3646_);
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
}
}
}
else
{
lean_object* v_r_3660_; 
v_r_3660_ = lean_ctor_get(v___x_3513_, 4);
lean_inc(v_r_3660_);
if (lean_obj_tag(v_r_3660_) == 0)
{
lean_object* v_k_3661_; lean_object* v_v_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3674_; 
v_k_3661_ = lean_ctor_get(v___x_3513_, 1);
v_v_3662_ = lean_ctor_get(v___x_3513_, 2);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3674_ == 0)
{
lean_object* v_unused_3675_; lean_object* v_unused_3676_; lean_object* v_unused_3677_; 
v_unused_3675_ = lean_ctor_get(v___x_3513_, 4);
lean_dec(v_unused_3675_);
v_unused_3676_ = lean_ctor_get(v___x_3513_, 3);
lean_dec(v_unused_3676_);
v_unused_3677_ = lean_ctor_get(v___x_3513_, 0);
lean_dec(v_unused_3677_);
v___x_3664_ = v___x_3513_;
v_isShared_3665_ = v_isSharedCheck_3674_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_v_3662_);
lean_inc(v_k_3661_);
lean_dec(v___x_3513_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3674_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3666_ = lean_unsigned_to_nat(3u);
v___x_3667_ = lean_unsigned_to_nat(1u);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v_l_3610_);
lean_ctor_set(v___x_3664_, 2, v_v_3328_);
lean_ctor_set(v___x_3664_, 1, v_k_3327_);
lean_ctor_set(v___x_3664_, 0, v___x_3667_);
v___x_3669_ = v___x_3664_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3673_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3673_, 3, v_l_3610_);
lean_ctor_set(v_reuseFailAlloc_3673_, 4, v_l_3610_);
v___x_3669_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_r_3660_);
lean_ctor_set(v___x_3332_, 3, v___x_3669_);
lean_ctor_set(v___x_3332_, 2, v_v_3662_);
lean_ctor_set(v___x_3332_, 1, v_k_3661_);
lean_ctor_set(v___x_3332_, 0, v___x_3666_);
v___x_3671_ = v___x_3332_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_k_3661_);
lean_ctor_set(v_reuseFailAlloc_3672_, 2, v_v_3662_);
lean_ctor_set(v_reuseFailAlloc_3672_, 3, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3672_, 4, v_r_3660_);
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
else
{
lean_object* v___x_3678_; lean_object* v___x_3680_; 
v___x_3678_ = lean_unsigned_to_nat(2u);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3513_);
lean_ctor_set(v___x_3332_, 3, v_r_3660_);
lean_ctor_set(v___x_3332_, 0, v___x_3678_);
v___x_3680_ = v___x_3332_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3681_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3681_, 3, v_r_3660_);
lean_ctor_set(v_reuseFailAlloc_3681_, 4, v___x_3513_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3682_ = lean_unsigned_to_nat(1u);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3513_);
lean_ctor_set(v___x_3332_, 3, v___x_3513_);
lean_ctor_set(v___x_3332_, 0, v___x_3682_);
v___x_3684_ = v___x_3332_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3685_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3685_, 3, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3685_, 4, v___x_3513_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = lean_unsigned_to_nat(1u);
v___x_3688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
lean_ctor_set(v___x_3688_, 1, v_k_3323_);
lean_ctor_set(v___x_3688_, 2, v_v_3324_);
lean_ctor_set(v___x_3688_, 3, v_t_3325_);
lean_ctor_set(v___x_3688_, 4, v_t_3325_);
return v___x_3688_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(lean_object* v_init_3689_, lean_object* v_x_3690_){
_start:
{
if (lean_obj_tag(v_x_3690_) == 0)
{
lean_object* v_k_3691_; lean_object* v_v_3692_; lean_object* v_l_3693_; lean_object* v_r_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v_k_3691_ = lean_ctor_get(v_x_3690_, 1);
lean_inc(v_k_3691_);
v_v_3692_ = lean_ctor_get(v_x_3690_, 2);
lean_inc(v_v_3692_);
v_l_3693_ = lean_ctor_get(v_x_3690_, 3);
lean_inc(v_l_3693_);
v_r_3694_ = lean_ctor_get(v_x_3690_, 4);
lean_inc(v_r_3694_);
lean_dec_ref_known(v_x_3690_, 5);
v___x_3695_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_3689_, v_l_3693_);
v___x_3696_ = 1;
v___x_3697_ = l_Lean_Name_toString(v_k_3691_, v___x_3696_);
v___x_3698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3698_, 0, v_v_3692_);
v___x_3699_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v___x_3697_, v___x_3698_, v___x_3695_);
v_init_3689_ = v___x_3699_;
v_x_3690_ = v_r_3694_;
goto _start;
}
else
{
return v_init_3689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_m_3701_){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3702_ = lean_box(1);
v___x_3703_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v___x_3702_, v_m_3701_);
v___x_3704_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v_baseName_3707_, uint8_t v_updateToolchain_3708_, lean_object* v_ws_3709_, lean_object* v___x_3710_, lean_object* v_dep_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v_name_3715_; lean_object* v_opts_3716_; uint8_t v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v_name_3715_ = lean_ctor_get(v_dep_3711_, 0);
v_opts_3716_ = lean_ctor_get(v_dep_3711_, 4);
v___x_3717_ = 0;
v___x_3718_ = l_Lean_Name_toString(v_baseName_3707_, v___x_3717_);
v___x_3719_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3720_ = lean_string_append(v___x_3718_, v___x_3719_);
lean_inc(v_name_3715_);
v___x_3721_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3715_, v_updateToolchain_3708_);
v___x_3722_ = lean_string_append(v___x_3720_, v___x_3721_);
lean_dec_ref(v___x_3721_);
v___x_3723_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3724_ = lean_string_append(v___x_3722_, v___x_3723_);
lean_inc(v_opts_3716_);
v___x_3725_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_opts_3716_);
v___x_3726_ = lean_unsigned_to_nat(80u);
v___x_3727_ = l_Lean_Json_pretty(v___x_3725_, v___x_3726_);
v___x_3728_ = lean_string_append(v___x_3724_, v___x_3727_);
lean_dec_ref(v___x_3727_);
v___x_3729_ = 0;
v___x_3730_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set_uint8(v___x_3730_, sizeof(void*)*1, v___x_3729_);
lean_inc_ref(v___y_3713_);
v___x_3731_ = lean_apply_2(v___y_3713_, v___x_3730_, lean_box(0));
v___x_3732_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3709_, v___x_3710_, v_dep_3711_, v___y_3712_, v___y_3713_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v_baseName_3733_, lean_object* v_updateToolchain_3734_, lean_object* v_ws_3735_, lean_object* v___x_3736_, lean_object* v_dep_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
uint8_t v_updateToolchain_boxed_3741_; lean_object* v_res_3742_; 
v_updateToolchain_boxed_3741_ = lean_unbox(v_updateToolchain_3734_);
v_res_3742_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v_baseName_3733_, v_updateToolchain_boxed_3741_, v_ws_3735_, v___x_3736_, v_dep_3737_, v___y_3738_, v___y_3739_);
lean_dec_ref(v___y_3739_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_a_3743_, lean_object* v_b_3744_){
_start:
{
lean_object* v_next_3745_; 
v_next_3745_ = lean_ctor_get(v_a_3743_, 0);
lean_inc(v_next_3745_);
if (lean_obj_tag(v_next_3745_) == 0)
{
lean_dec_ref(v_a_3743_);
return v_b_3744_;
}
else
{
lean_object* v_upperBound_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3766_; 
v_upperBound_3746_ = lean_ctor_get(v_a_3743_, 1);
v_isSharedCheck_3766_ = !lean_is_exclusive(v_a_3743_);
if (v_isSharedCheck_3766_ == 0)
{
lean_object* v_unused_3767_; 
v_unused_3767_ = lean_ctor_get(v_a_3743_, 0);
lean_dec(v_unused_3767_);
v___x_3748_ = v_a_3743_;
v_isShared_3749_ = v_isSharedCheck_3766_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_upperBound_3746_);
lean_dec(v_a_3743_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3766_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v_val_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3765_; 
v_val_3750_ = lean_ctor_get(v_next_3745_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_next_3745_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3752_ = v_next_3745_;
v_isShared_3753_ = v_isSharedCheck_3765_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_val_3750_);
lean_dec(v_next_3745_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3765_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
uint8_t v___x_3754_; 
v___x_3754_ = lean_nat_dec_lt(v_val_3750_, v_upperBound_3746_);
if (v___x_3754_ == 0)
{
lean_del_object(v___x_3752_);
lean_dec(v_val_3750_);
lean_del_object(v___x_3748_);
lean_dec(v_upperBound_3746_);
return v_b_3744_;
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3758_; 
v___x_3755_ = lean_unsigned_to_nat(1u);
v___x_3756_ = lean_nat_add(v_val_3750_, v___x_3755_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3756_);
v___x_3758_ = v___x_3752_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3760_; 
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3758_);
v___x_3760_ = v___x_3748_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_upperBound_3746_);
v___x_3760_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3761_; 
v___x_3761_ = lean_array_push(v_b_3744_, v_val_3750_);
v_a_3743_ = v___x_3760_;
v_b_3744_ = v___x_3761_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_n_3768_, lean_object* v_f_3769_, lean_object* v_xs_3770_, lean_object* v_k_3771_, lean_object* v_acc_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
uint8_t v___x_3776_; 
v___x_3776_ = lean_nat_dec_lt(v_k_3771_, v_n_3768_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
lean_dec(v_k_3771_);
lean_dec_ref(v_f_3769_);
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v_acc_3772_);
lean_ctor_set(v___x_3777_, 1, v___y_3773_);
v___x_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
return v___x_3778_;
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3779_ = lean_array_fget_borrowed(v_xs_3770_, v_k_3771_);
lean_inc_ref(v_f_3769_);
lean_inc_ref(v___y_3774_);
lean_inc(v___x_3779_);
v___x_3780_ = lean_apply_4(v_f_3769_, v___x_3779_, v___y_3773_, v___y_3774_, lean_box(0));
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v_fst_3782_; lean_object* v_snd_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___x_3780_, 1);
v_fst_3782_ = lean_ctor_get(v_a_3781_, 0);
lean_inc(v_fst_3782_);
v_snd_3783_ = lean_ctor_get(v_a_3781_, 1);
lean_inc(v_snd_3783_);
lean_dec(v_a_3781_);
v___x_3784_ = lean_unsigned_to_nat(1u);
v___x_3785_ = lean_nat_add(v_k_3771_, v___x_3784_);
lean_dec(v_k_3771_);
v___x_3786_ = lean_array_push(v_acc_3772_, v_fst_3782_);
v_k_3771_ = v___x_3785_;
v_acc_3772_ = v___x_3786_;
v___y_3773_ = v_snd_3783_;
goto _start;
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref(v_acc_3772_);
lean_dec(v_k_3771_);
lean_dec_ref(v_f_3769_);
v_a_3788_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3780_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3780_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object* v_n_3796_, lean_object* v_f_3797_, lean_object* v_xs_3798_, lean_object* v_k_3799_, lean_object* v_acc_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_3796_, v_f_3797_, v_xs_3798_, v_k_3799_, v_acc_3800_, v___y_3801_, v___y_3802_);
lean_dec_ref(v___y_3802_);
lean_dec_ref(v_xs_3798_);
lean_dec(v_n_3796_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object* v_upperBound_3805_, lean_object* v_fst_3806_, lean_object* v___x_3807_, lean_object* v_leanOpts_3808_, lean_object* v_a_3809_, lean_object* v_b_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v_fst_3815_; lean_object* v_snd_3816_; uint8_t v___x_3820_; 
v___x_3820_ = lean_nat_dec_lt(v_a_3809_, v_upperBound_3805_);
if (v___x_3820_ == 0)
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
lean_dec(v_a_3809_);
lean_dec_ref(v_leanOpts_3808_);
v___x_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3821_, 0, v_b_3810_);
lean_ctor_set(v___x_3821_, 1, v___y_3811_);
v___x_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
return v___x_3822_;
}
else
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = lean_array_fget_borrowed(v_fst_3806_, v_a_3809_);
lean_inc(v___x_3823_);
v___x_3824_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_3823_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3878_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3878_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3878_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v_snd_3829_; lean_object* v___x_3830_; lean_object* v_opts_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v_snd_3829_ = lean_ctor_get(v_a_3825_, 1);
lean_inc(v_snd_3829_);
lean_dec(v_a_3825_);
v___x_3830_ = lean_array_fget_borrowed(v___x_3807_, v_a_3809_);
v_opts_3831_ = lean_ctor_get(v___x_3830_, 4);
v___x_3832_ = lean_unsigned_to_nat(0u);
v___x_3833_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3808_);
lean_inc(v_opts_3831_);
lean_inc(v___x_3823_);
v___x_3834_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_3810_, v___x_3823_, v_opts_3831_, v_leanOpts_3808_, v___x_3820_, v___x_3833_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v_a_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
lean_del_object(v___x_3827_);
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
v_a_3836_ = lean_ctor_get(v___x_3834_, 1);
lean_inc(v_a_3836_);
lean_dec_ref_known(v___x_3834_, 2);
v___x_3837_ = lean_array_get_size(v_a_3836_);
v___x_3838_ = lean_nat_dec_lt(v___x_3832_, v___x_3837_);
if (v___x_3838_ == 0)
{
lean_dec(v_a_3836_);
v_fst_3815_ = v_a_3835_;
v_snd_3816_ = v_snd_3829_;
goto v___jp_3814_;
}
else
{
lean_object* v___x_3839_; size_t v___x_3840_; size_t v___x_3841_; lean_object* v___x_3842_; 
v___x_3839_ = lean_box(0);
v___x_3840_ = ((size_t)0ULL);
v___x_3841_ = lean_usize_of_nat(v___x_3837_);
v___x_3842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3836_, v___x_3840_, v___x_3841_, v___x_3839_, v___y_3812_);
lean_dec(v_a_3836_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_dec_ref_known(v___x_3842_, 1);
v_fst_3815_ = v_a_3835_;
v_snd_3816_ = v_snd_3829_;
goto v___jp_3814_;
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec(v_a_3835_);
lean_dec(v_snd_3829_);
lean_dec(v_a_3809_);
lean_dec_ref(v_leanOpts_3808_);
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; 
lean_dec(v_snd_3829_);
lean_dec(v_a_3809_);
lean_dec_ref(v_leanOpts_3808_);
v_a_3851_ = lean_ctor_get(v___x_3834_, 1);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3834_, 2);
v___x_3852_ = lean_array_get_size(v_a_3851_);
v___x_3853_ = lean_nat_dec_lt(v___x_3832_, v___x_3852_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; lean_object* v___x_3856_; 
lean_dec(v_a_3851_);
v___x_3854_ = lean_box(0);
if (v_isShared_3828_ == 0)
{
lean_ctor_set_tag(v___x_3827_, 1);
lean_ctor_set(v___x_3827_, 0, v___x_3854_);
v___x_3856_ = v___x_3827_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
else
{
lean_object* v___x_3858_; size_t v___x_3859_; size_t v___x_3860_; lean_object* v___x_3861_; 
lean_del_object(v___x_3827_);
v___x_3858_ = lean_box(0);
v___x_3859_ = ((size_t)0ULL);
v___x_3860_ = lean_usize_of_nat(v___x_3852_);
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3851_, v___x_3859_, v___x_3860_, v___x_3858_, v___y_3812_);
lean_dec(v_a_3851_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3868_ == 0)
{
lean_object* v_unused_3869_; 
v_unused_3869_ = lean_ctor_get(v___x_3861_, 0);
lean_dec(v_unused_3869_);
v___x_3863_ = v___x_3861_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_dec(v___x_3861_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set_tag(v___x_3863_, 1);
lean_ctor_set(v___x_3863_, 0, v___x_3858_);
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3858_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
v_a_3870_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3861_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3861_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec_ref(v_b_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_leanOpts_3808_);
v_a_3879_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3824_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3824_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
v___jp_3814_:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = lean_unsigned_to_nat(1u);
v___x_3818_ = lean_nat_add(v_a_3809_, v___x_3817_);
lean_dec(v_a_3809_);
v_a_3809_ = v___x_3818_;
v_b_3810_ = v_fst_3815_;
v___y_3811_ = v_snd_3816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object* v_upperBound_3887_, lean_object* v_fst_3888_, lean_object* v___x_3889_, lean_object* v_leanOpts_3890_, lean_object* v_a_3891_, lean_object* v_b_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_3887_, v_fst_3888_, v___x_3889_, v_leanOpts_3890_, v_a_3891_, v_b_3892_, v___y_3893_, v___y_3894_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v___x_3889_);
lean_dec_ref(v_fst_3888_);
lean_dec(v_upperBound_3887_);
return v_res_3896_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(lean_object* v___x_3897_, lean_object* v_x_3898_){
_start:
{
lean_object* v_baseName_3899_; lean_object* v_name_3900_; uint8_t v___x_3901_; 
v_baseName_3899_ = lean_ctor_get(v_x_3898_, 1);
v_name_3900_ = lean_ctor_get(v___x_3897_, 0);
v___x_3901_ = lean_name_eq(v_baseName_3899_, v_name_3900_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___x_3902_, lean_object* v_x_3903_){
_start:
{
uint8_t v_res_3904_; lean_object* v_r_3905_; 
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(v___x_3902_, v_x_3903_);
lean_dec_ref(v_x_3903_);
lean_dec_ref(v___x_3902_);
v_r_3905_ = lean_box(v_res_3904_);
return v_r_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object* v_pkg_3906_, lean_object* v_leanOpts_3907_, uint8_t v_reconfigure_3908_, lean_object* v_as_3909_, size_t v_i_3910_, size_t v_stop_3911_, lean_object* v_b_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
uint8_t v___x_3916_; 
v___x_3916_ = lean_usize_dec_eq(v_i_3910_, v_stop_3911_);
if (v___x_3916_ == 0)
{
lean_object* v_ws_3917_; lean_object* v_depIdxs_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_4015_; 
v_ws_3917_ = lean_ctor_get(v_b_3912_, 0);
v_depIdxs_3918_ = lean_ctor_get(v_b_3912_, 1);
v_isSharedCheck_4015_ = !lean_is_exclusive(v_b_3912_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_3920_ = v_b_3912_;
v_isShared_3921_ = v_isSharedCheck_4015_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_depIdxs_3918_);
lean_inc(v_ws_3917_);
lean_dec(v_b_3912_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_4015_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v_packages_3922_; size_t v___x_3923_; size_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___f_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v_packages_3922_ = lean_ctor_get(v_ws_3917_, 4);
v___x_3923_ = ((size_t)1ULL);
v___x_3924_ = lean_usize_sub(v_i_3910_, v___x_3923_);
v___x_3925_ = lean_array_uget_borrowed(v_as_3909_, v___x_3924_);
lean_inc(v___x_3925_);
v___f_3926_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3926_, 0, v___x_3925_);
v___x_3927_ = lean_unsigned_to_nat(0u);
v___x_3928_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3926_, v_packages_3922_, v___x_3927_);
if (lean_obj_tag(v___x_3928_) == 1)
{
lean_object* v_val_3929_; lean_object* v___x_3930_; lean_object* v___x_3932_; 
v_val_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_val_3929_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3930_ = lean_array_push(v_depIdxs_3918_, v_val_3929_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 1, v___x_3930_);
v___x_3932_ = v___x_3920_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_ws_3917_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3930_);
v___x_3932_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
v_i_3910_ = v___x_3924_;
v_b_3912_ = v___x_3932_;
goto _start;
}
}
else
{
lean_object* v_baseName_3935_; lean_object* v_name_3936_; lean_object* v_opts_3937_; uint8_t v___x_3938_; 
lean_dec(v___x_3928_);
v_baseName_3935_ = lean_ctor_get(v_pkg_3906_, 1);
v_name_3936_ = lean_ctor_get(v___x_3925_, 0);
v_opts_3937_ = lean_ctor_get(v___x_3925_, 4);
v___x_3938_ = lean_name_eq(v_baseName_3935_, v_name_3936_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; 
lean_inc_ref(v___y_3914_);
lean_inc_ref(v_ws_3917_);
lean_inc(v___x_3925_);
lean_inc_ref(v_pkg_3906_);
v___x_3939_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_3906_, v___x_3925_, v_ws_3917_, v___y_3913_, v___y_3914_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3998_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3942_ = v___x_3939_;
v_isShared_3943_ = v_isSharedCheck_3998_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3939_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3998_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v_fst_3944_; lean_object* v_snd_3945_; lean_object* v___x_3946_; lean_object* v_wsIdx_3947_; lean_object* v___x_3948_; 
v_fst_3944_ = lean_ctor_get(v_a_3940_, 0);
lean_inc(v_fst_3944_);
v_snd_3945_ = lean_ctor_get(v_a_3940_, 1);
lean_inc(v_snd_3945_);
lean_dec(v_a_3940_);
v___x_3946_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_3947_ = lean_array_get_size(v_packages_3922_);
lean_inc_ref(v_leanOpts_3907_);
lean_inc(v_opts_3937_);
v___x_3948_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_3917_, v_fst_3944_, v_opts_3937_, v_leanOpts_3907_, v_reconfigure_3908_, v___x_3946_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_object* v_a_3949_; lean_object* v_a_3950_; lean_object* v___x_3951_; lean_object* v___x_3953_; 
lean_del_object(v___x_3942_);
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc(v_a_3949_);
v_a_3950_ = lean_ctor_get(v___x_3948_, 1);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3948_, 2);
v___x_3951_ = lean_array_push(v_depIdxs_3918_, v_wsIdx_3947_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 1, v___x_3951_);
lean_ctor_set(v___x_3920_, 0, v_a_3949_);
v___x_3953_ = v___x_3920_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3949_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3954_ = lean_array_get_size(v_a_3950_);
v___x_3955_ = lean_nat_dec_lt(v___x_3927_, v___x_3954_);
if (v___x_3955_ == 0)
{
lean_dec(v_a_3950_);
v_i_3910_ = v___x_3924_;
v_b_3912_ = v___x_3953_;
v___y_3913_ = v_snd_3945_;
goto _start;
}
else
{
lean_object* v___x_3957_; size_t v___x_3958_; size_t v___x_3959_; lean_object* v___x_3960_; 
v___x_3957_ = lean_box(0);
v___x_3958_ = ((size_t)0ULL);
v___x_3959_ = lean_usize_of_nat(v___x_3954_);
v___x_3960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3950_, v___x_3958_, v___x_3959_, v___x_3957_, v___y_3914_);
lean_dec(v_a_3950_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_dec_ref_known(v___x_3960_, 1);
v_i_3910_ = v___x_3924_;
v_b_3912_ = v___x_3953_;
v___y_3913_ = v_snd_3945_;
goto _start;
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec_ref(v___x_3953_);
lean_dec(v_snd_3945_);
lean_dec_ref(v_leanOpts_3907_);
lean_dec_ref(v_pkg_3906_);
v_a_3962_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3960_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3960_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
lean_dec(v_snd_3945_);
lean_del_object(v___x_3920_);
lean_dec_ref(v_depIdxs_3918_);
lean_dec_ref(v_leanOpts_3907_);
lean_dec_ref(v_pkg_3906_);
v_a_3971_ = lean_ctor_get(v___x_3948_, 1);
lean_inc(v_a_3971_);
lean_dec_ref_known(v___x_3948_, 2);
v___x_3972_ = lean_array_get_size(v_a_3971_);
v___x_3973_ = lean_nat_dec_lt(v___x_3927_, v___x_3972_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
lean_dec(v_a_3971_);
v___x_3974_ = lean_box(0);
if (v_isShared_3943_ == 0)
{
lean_ctor_set_tag(v___x_3942_, 1);
lean_ctor_set(v___x_3942_, 0, v___x_3974_);
v___x_3976_ = v___x_3942_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
else
{
lean_object* v___x_3978_; size_t v___x_3979_; size_t v___x_3980_; lean_object* v___x_3981_; 
lean_del_object(v___x_3942_);
v___x_3978_ = lean_box(0);
v___x_3979_ = ((size_t)0ULL);
v___x_3980_ = lean_usize_of_nat(v___x_3972_);
v___x_3981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_3971_, v___x_3979_, v___x_3980_, v___x_3978_, v___y_3914_);
lean_dec(v_a_3971_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v___x_3981_, 0);
lean_dec(v_unused_3989_);
v___x_3983_ = v___x_3981_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_dec(v___x_3981_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
lean_ctor_set_tag(v___x_3983_, 1);
lean_ctor_set(v___x_3983_, 0, v___x_3978_);
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3978_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
v_a_3990_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3981_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3981_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_del_object(v___x_3920_);
lean_dec_ref(v_depIdxs_3918_);
lean_dec_ref(v_ws_3917_);
lean_dec_ref(v_leanOpts_3907_);
lean_dec_ref(v_pkg_3906_);
v_a_3999_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3939_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3939_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; uint8_t v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
lean_inc(v_baseName_3935_);
lean_del_object(v___x_3920_);
lean_dec_ref(v_depIdxs_3918_);
lean_dec_ref(v_ws_3917_);
lean_dec(v___y_3913_);
lean_dec_ref(v_leanOpts_3907_);
lean_dec_ref(v_pkg_3906_);
v___x_4007_ = l_Lean_Name_toString(v_baseName_3935_, v___x_3916_);
v___x_4008_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_4009_ = lean_string_append(v___x_4007_, v___x_4008_);
v___x_4010_ = 3;
v___x_4011_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4011_, 0, v___x_4009_);
lean_ctor_set_uint8(v___x_4011_, sizeof(void*)*1, v___x_4010_);
lean_inc_ref(v___y_3914_);
v___x_4012_ = lean_apply_2(v___y_3914_, v___x_4011_, lean_box(0));
v___x_4013_ = lean_box(0);
v___x_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
return v___x_4014_;
}
}
}
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_dec_ref(v_leanOpts_3907_);
lean_dec_ref(v_pkg_3906_);
v___x_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4016_, 0, v_b_3912_);
lean_ctor_set(v___x_4016_, 1, v___y_3913_);
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
return v___x_4017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___boxed(lean_object* v_pkg_4018_, lean_object* v_leanOpts_4019_, lean_object* v_reconfigure_4020_, lean_object* v_as_4021_, lean_object* v_i_4022_, lean_object* v_stop_4023_, lean_object* v_b_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
uint8_t v_reconfigure_boxed_4028_; size_t v_i_boxed_4029_; size_t v_stop_boxed_4030_; lean_object* v_res_4031_; 
v_reconfigure_boxed_4028_ = lean_unbox(v_reconfigure_4020_);
v_i_boxed_4029_ = lean_unbox_usize(v_i_4022_);
lean_dec(v_i_4022_);
v_stop_boxed_4030_ = lean_unbox_usize(v_stop_4023_);
lean_dec(v_stop_4023_);
v_res_4031_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4018_, v_leanOpts_4019_, v_reconfigure_boxed_4028_, v_as_4021_, v_i_boxed_4029_, v_stop_boxed_4030_, v_b_4024_, v___y_4025_, v___y_4026_);
lean_dec_ref(v___y_4026_);
lean_dec_ref(v_as_4021_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object* v_leanOpts_4032_, uint8_t v_reconfigure_4033_, lean_object* v_ws_4034_, lean_object* v_i_4035_, lean_object* v_next_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_packages_4040_; lean_object* v_pkg_4041_; lean_object* v_ws_4043_; lean_object* v_depIdxs_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v_____x_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v_depConfigs_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v_s_4065_; lean_object* v___x_4066_; uint8_t v___x_4067_; 
v_packages_4040_ = lean_ctor_get(v_ws_4034_, 4);
v_pkg_4041_ = lean_array_fget(v_packages_4040_, v_i_4035_);
lean_dec(v_i_4035_);
v_depConfigs_4062_ = lean_ctor_get(v_pkg_4041_, 12);
v___x_4063_ = lean_array_get_size(v_depConfigs_4062_);
v___x_4064_ = lean_mk_empty_array_with_capacity(v___x_4063_);
lean_inc_ref(v___x_4064_);
lean_inc_ref(v_ws_4034_);
v_s_4065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_4065_, 0, v_ws_4034_);
lean_ctor_set(v_s_4065_, 1, v___x_4064_);
v___x_4066_ = lean_unsigned_to_nat(0u);
v___x_4067_ = lean_nat_dec_le(v___x_4063_, v___x_4063_);
if (v___x_4067_ == 0)
{
uint8_t v___x_4068_; 
v___x_4068_ = lean_nat_dec_lt(v___x_4066_, v___x_4063_);
if (v___x_4068_ == 0)
{
lean_object* v_ws_4069_; lean_object* v_packages_4070_; lean_object* v___x_4071_; uint8_t v___x_4072_; 
lean_dec_ref_known(v_s_4065_, 2);
v_ws_4069_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4034_, v_pkg_4041_, v___x_4064_);
v_packages_4070_ = lean_ctor_get(v_ws_4069_, 4);
v___x_4071_ = lean_array_get_size(v_packages_4070_);
v___x_4072_ = lean_nat_dec_lt(v_next_4036_, v___x_4071_);
if (v___x_4072_ == 0)
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
lean_dec(v_next_4036_);
lean_dec_ref(v_leanOpts_4032_);
v___x_4073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4073_, 0, v_ws_4069_);
lean_ctor_set(v___x_4073_, 1, v___y_4037_);
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = lean_unsigned_to_nat(1u);
v___x_4076_ = lean_nat_add(v_next_4036_, v___x_4075_);
v_ws_4034_ = v_ws_4069_;
v_i_4035_ = v_next_4036_;
v_next_4036_ = v___x_4076_;
goto _start;
}
}
else
{
size_t v___x_4078_; size_t v___x_4079_; lean_object* v___x_4080_; 
lean_dec_ref(v___x_4064_);
lean_dec_ref(v_ws_4034_);
v___x_4078_ = lean_usize_of_nat(v___x_4063_);
v___x_4079_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4032_);
lean_inc(v_pkg_4041_);
v___x_4080_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4041_, v_leanOpts_4032_, v_reconfigure_4033_, v_depConfigs_4062_, v___x_4078_, v___x_4079_, v_s_4065_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v_fst_4082_; lean_object* v_snd_4083_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4080_, 1);
v_fst_4082_ = lean_ctor_get(v_a_4081_, 0);
lean_inc(v_fst_4082_);
v_snd_4083_ = lean_ctor_get(v_a_4081_, 1);
lean_inc(v_snd_4083_);
lean_dec(v_a_4081_);
v_____x_4057_ = v_fst_4082_;
v___y_4058_ = v_snd_4083_;
v___y_4059_ = v___y_4038_;
goto v___jp_4056_;
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v_pkg_4041_);
lean_dec(v_next_4036_);
lean_dec_ref(v_leanOpts_4032_);
v_a_4084_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4080_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4080_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
else
{
uint8_t v___x_4092_; 
v___x_4092_ = lean_nat_dec_lt(v___x_4066_, v___x_4063_);
if (v___x_4092_ == 0)
{
lean_dec_ref_known(v_s_4065_, 2);
v_ws_4043_ = v_ws_4034_;
v_depIdxs_4044_ = v___x_4064_;
v___y_4045_ = v___y_4037_;
v___y_4046_ = v___y_4038_;
goto v___jp_4042_;
}
else
{
size_t v___x_4093_; size_t v___x_4094_; lean_object* v___x_4095_; 
lean_dec_ref(v___x_4064_);
lean_dec_ref(v_ws_4034_);
v___x_4093_ = lean_usize_of_nat(v___x_4063_);
v___x_4094_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4032_);
lean_inc(v_pkg_4041_);
v___x_4095_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4041_, v_leanOpts_4032_, v_reconfigure_4033_, v_depConfigs_4062_, v___x_4093_, v___x_4094_, v_s_4065_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v_fst_4097_; lean_object* v_snd_4098_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v___x_4095_, 1);
v_fst_4097_ = lean_ctor_get(v_a_4096_, 0);
lean_inc(v_fst_4097_);
v_snd_4098_ = lean_ctor_get(v_a_4096_, 1);
lean_inc(v_snd_4098_);
lean_dec(v_a_4096_);
v_____x_4057_ = v_fst_4097_;
v___y_4058_ = v_snd_4098_;
v___y_4059_ = v___y_4038_;
goto v___jp_4056_;
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec(v_pkg_4041_);
lean_dec(v_next_4036_);
lean_dec_ref(v_leanOpts_4032_);
v_a_4099_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4095_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4095_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
v___jp_4042_:
{
lean_object* v_ws_4047_; lean_object* v_packages_4048_; lean_object* v___x_4049_; uint8_t v___x_4050_; 
v_ws_4047_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4043_, v_pkg_4041_, v_depIdxs_4044_);
v_packages_4048_ = lean_ctor_get(v_ws_4047_, 4);
v___x_4049_ = lean_array_get_size(v_packages_4048_);
v___x_4050_ = lean_nat_dec_lt(v_next_4036_, v___x_4049_);
if (v___x_4050_ == 0)
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
lean_dec(v_next_4036_);
lean_dec_ref(v_leanOpts_4032_);
v___x_4051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4051_, 0, v_ws_4047_);
lean_ctor_set(v___x_4051_, 1, v___y_4045_);
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
return v___x_4052_;
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = lean_unsigned_to_nat(1u);
v___x_4054_ = lean_nat_add(v_next_4036_, v___x_4053_);
v_ws_4034_ = v_ws_4047_;
v_i_4035_ = v_next_4036_;
v_next_4036_ = v___x_4054_;
v___y_4037_ = v___y_4045_;
v___y_4038_ = v___y_4046_;
goto _start;
}
}
v___jp_4056_:
{
lean_object* v_ws_4060_; lean_object* v_depIdxs_4061_; 
v_ws_4060_ = lean_ctor_get(v_____x_4057_, 0);
lean_inc_ref(v_ws_4060_);
v_depIdxs_4061_ = lean_ctor_get(v_____x_4057_, 1);
lean_inc_ref(v_depIdxs_4061_);
lean_dec_ref(v_____x_4057_);
v_ws_4043_ = v_ws_4060_;
v_depIdxs_4044_ = v_depIdxs_4061_;
v___y_4045_ = v___y_4058_;
v___y_4046_ = v___y_4059_;
goto v___jp_4042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object* v_leanOpts_4107_, lean_object* v_reconfigure_4108_, lean_object* v_ws_4109_, lean_object* v_i_4110_, lean_object* v_next_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
uint8_t v_reconfigure_boxed_4115_; lean_object* v_res_4116_; 
v_reconfigure_boxed_4115_ = lean_unbox(v_reconfigure_4108_);
v_res_4116_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4107_, v_reconfigure_boxed_4115_, v_ws_4109_, v_i_4110_, v_next_4111_, v___y_4112_, v___y_4113_);
lean_dec_ref(v___y_4113_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4119_, lean_object* v_toUpdate_4120_, lean_object* v_leanOpts_4121_, uint8_t v_updateToolchain_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4125_ = lean_box(1);
v___x_4126_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4123_, v_ws_4119_, v_toUpdate_4120_, v___x_4125_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v_snd_4128_; uint8_t v___x_4129_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4126_, 1);
v_snd_4128_ = lean_ctor_get(v_a_4127_, 1);
lean_inc(v_snd_4128_);
lean_dec(v_a_4127_);
v___x_4129_ = 1;
if (v_updateToolchain_4122_ == 0)
{
lean_object* v_packages_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v_wsIdx_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v_packages_4130_ = lean_ctor_get(v_ws_4119_, 4);
v___x_4131_ = lean_unsigned_to_nat(0u);
v___x_4132_ = lean_array_fget_borrowed(v_packages_4130_, v___x_4131_);
v_wsIdx_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_wsIdx_4133_);
v___x_4134_ = lean_array_get_size(v_packages_4130_);
v___x_4135_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4121_, v___x_4129_, v_ws_4119_, v_wsIdx_4133_, v___x_4134_, v_snd_4128_, v_a_4123_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4153_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4153_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4153_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v_fst_4140_; lean_object* v_snd_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4152_; 
v_fst_4140_ = lean_ctor_get(v_a_4136_, 0);
v_snd_4141_ = lean_ctor_get(v_a_4136_, 1);
v_isSharedCheck_4152_ = !lean_is_exclusive(v_a_4136_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4143_ = v_a_4136_;
v_isShared_4144_ = v_isSharedCheck_4152_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_snd_4141_);
lean_inc(v_fst_4140_);
lean_dec(v_a_4136_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4152_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4145_; lean_object* v___x_4147_; 
v___x_4145_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4140_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v___x_4145_);
v___x_4147_ = v___x_4143_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v___x_4145_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v_snd_4141_);
v___x_4147_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
lean_object* v___x_4149_; 
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 0, v___x_4147_);
v___x_4149_ = v___x_4138_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v___x_4147_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
}
else
{
return v___x_4135_;
}
}
else
{
lean_object* v_packages_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v_baseName_4157_; lean_object* v_depConfigs_4158_; lean_object* v___x_4159_; lean_object* v___f_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_packages_4154_ = lean_ctor_get(v_ws_4119_, 4);
v___x_4155_ = lean_unsigned_to_nat(0u);
v___x_4156_ = lean_array_fget_borrowed(v_packages_4154_, v___x_4155_);
v_baseName_4157_ = lean_ctor_get(v___x_4156_, 1);
v_depConfigs_4158_ = lean_ctor_get(v___x_4156_, 12);
v___x_4159_ = lean_box(v_updateToolchain_4122_);
lean_inc(v___x_4156_);
lean_inc_ref(v_ws_4119_);
lean_inc(v_baseName_4157_);
v___f_4160_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 8, 4);
lean_closure_set(v___f_4160_, 0, v_baseName_4157_);
lean_closure_set(v___f_4160_, 1, v___x_4159_);
lean_closure_set(v___f_4160_, 2, v_ws_4119_);
lean_closure_set(v___f_4160_, 3, v___x_4156_);
v___x_4161_ = lean_array_get_size(v_depConfigs_4158_);
lean_inc_ref(v_depConfigs_4158_);
v___x_4162_ = l_Array_reverse___redArg(v_depConfigs_4158_);
v___x_4163_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4164_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4161_, v___f_4160_, v___x_4162_, v___x_4155_, v___x_4163_, v_snd_4128_, v_a_4123_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v_fst_4166_; lean_object* v_snd_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4239_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v_fst_4166_ = lean_ctor_get(v_a_4165_, 0);
v_snd_4167_ = lean_ctor_get(v_a_4165_, 1);
v_isSharedCheck_4239_ = !lean_is_exclusive(v_a_4165_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4169_ = v_a_4165_;
v_isShared_4170_ = v_isSharedCheck_4239_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_snd_4167_);
lean_inc(v_fst_4166_);
lean_dec(v_a_4165_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4239_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; 
lean_inc_ref(v_ws_4119_);
v___x_4171_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4123_, v_ws_4119_, v_fst_4166_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
lean_dec_ref_known(v___x_4171_, 1);
v___x_4172_ = lean_array_get_size(v_packages_4154_);
lean_inc_ref(v_leanOpts_4121_);
v___x_4173_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4161_, v_fst_4166_, v___x_4162_, v_leanOpts_4121_, v___x_4155_, v_ws_4119_, v_snd_4167_, v_a_4123_);
lean_dec_ref(v___x_4162_);
lean_dec(v_fst_4166_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4222_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4176_ = v___x_4173_;
v_isShared_4177_ = v_isSharedCheck_4222_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4222_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v_fst_4178_; lean_object* v_snd_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4221_; 
v_fst_4178_ = lean_ctor_get(v_a_4174_, 0);
v_snd_4179_ = lean_ctor_get(v_a_4174_, 1);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_a_4174_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4181_ = v_a_4174_;
v_isShared_4182_ = v_isSharedCheck_4221_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_snd_4179_);
lean_inc(v_fst_4178_);
lean_dec(v_a_4174_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4221_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v_packages_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4188_; 
v_packages_4183_ = lean_ctor_get(v_fst_4178_, 4);
v___x_4184_ = lean_array_get_size(v_packages_4183_);
v___x_4185_ = lean_array_fget(v_packages_4183_, v___x_4155_);
v___x_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4172_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 1, v___x_4184_);
lean_ctor_set(v___x_4169_, 0, v___x_4186_);
v___x_4188_ = v___x_4169_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4186_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___x_4184_);
v___x_4188_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; uint8_t v___x_4191_; 
v___x_4189_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4188_, v___x_4163_);
v___x_4190_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4178_, v___x_4185_, v___x_4189_);
v___x_4191_ = lean_nat_dec_eq(v___x_4172_, v___x_4184_);
if (v___x_4191_ == 0)
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_del_object(v___x_4181_);
lean_del_object(v___x_4176_);
v___x_4192_ = lean_unsigned_to_nat(1u);
v___x_4193_ = lean_nat_add(v___x_4172_, v___x_4192_);
v___x_4194_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4121_, v___x_4129_, v___x_4190_, v___x_4172_, v___x_4193_, v_snd_4179_, v_a_4123_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4212_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4197_ = v___x_4194_;
v_isShared_4198_ = v_isSharedCheck_4212_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4194_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4212_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v_fst_4199_; lean_object* v_snd_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4211_; 
v_fst_4199_ = lean_ctor_get(v_a_4195_, 0);
v_snd_4200_ = lean_ctor_get(v_a_4195_, 1);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_a_4195_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4202_ = v_a_4195_;
v_isShared_4203_ = v_isSharedCheck_4211_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_snd_4200_);
lean_inc(v_fst_4199_);
lean_dec(v_a_4195_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4211_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4204_; lean_object* v___x_4206_; 
v___x_4204_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4199_);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 0, v___x_4204_);
v___x_4206_ = v___x_4202_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4204_);
lean_ctor_set(v_reuseFailAlloc_4210_, 1, v_snd_4200_);
v___x_4206_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
lean_object* v___x_4208_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 0, v___x_4206_);
v___x_4208_ = v___x_4197_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
}
else
{
return v___x_4194_;
}
}
else
{
lean_object* v___x_4213_; lean_object* v___x_4215_; 
lean_dec_ref(v_leanOpts_4121_);
v___x_4213_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4190_);
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 0, v___x_4213_);
v___x_4215_ = v___x_4181_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4213_);
lean_ctor_set(v_reuseFailAlloc_4219_, 1, v_snd_4179_);
v___x_4215_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
lean_object* v___x_4217_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4215_);
v___x_4217_ = v___x_4176_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_del_object(v___x_4169_);
lean_dec_ref(v_leanOpts_4121_);
v_a_4223_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4173_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4173_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_del_object(v___x_4169_);
lean_dec(v_snd_4167_);
lean_dec(v_fst_4166_);
lean_dec_ref(v___x_4162_);
lean_dec_ref(v_leanOpts_4121_);
lean_dec_ref(v_ws_4119_);
v_a_4231_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4171_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4171_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_dec_ref(v___x_4162_);
lean_dec_ref(v_leanOpts_4121_);
lean_dec_ref(v_ws_4119_);
v_a_4240_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4164_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4164_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec_ref(v_leanOpts_4121_);
lean_dec_ref(v_ws_4119_);
v_a_4248_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4126_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4126_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4256_, lean_object* v_toUpdate_4257_, lean_object* v_leanOpts_4258_, lean_object* v_updateToolchain_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_){
_start:
{
uint8_t v_updateToolchain_boxed_4262_; lean_object* v_res_4263_; 
v_updateToolchain_boxed_4262_ = lean_unbox(v_updateToolchain_4259_);
v_res_4263_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4256_, v_toUpdate_4257_, v_leanOpts_4258_, v_updateToolchain_boxed_4262_, v_a_4260_);
lean_dec_ref(v_a_4260_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_leanOpts_4264_, uint8_t v_reconfigure_4265_, lean_object* v_ws_4266_, lean_object* v_i_4267_, lean_object* v_i__lt_4268_, lean_object* v_next_4269_, lean_object* v_lt__next_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4264_, v_reconfigure_4265_, v_ws_4266_, v_i_4267_, v_next_4269_, v___y_4271_, v___y_4272_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_leanOpts_4275_, lean_object* v_reconfigure_4276_, lean_object* v_ws_4277_, lean_object* v_i_4278_, lean_object* v_i__lt_4279_, lean_object* v_next_4280_, lean_object* v_lt__next_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
uint8_t v_reconfigure_boxed_4285_; lean_object* v_res_4286_; 
v_reconfigure_boxed_4285_ = lean_unbox(v_reconfigure_4276_);
v_res_4286_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4275_, v_reconfigure_boxed_4285_, v_ws_4277_, v_i_4278_, v_i__lt_4279_, v_next_4280_, v_lt__next_4281_, v___y_4282_, v___y_4283_);
lean_dec_ref(v___y_4283_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_00_u03b1_4287_, lean_object* v_00_u03b2_4288_, lean_object* v_n_4289_, lean_object* v_f_4290_, lean_object* v_xs_4291_, lean_object* v_k_4292_, lean_object* v_h_4293_, lean_object* v_acc_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4289_, v_f_4290_, v_xs_4291_, v_k_4292_, v_acc_4294_, v___y_4295_, v___y_4296_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_00_u03b1_4299_, lean_object* v_00_u03b2_4300_, lean_object* v_n_4301_, lean_object* v_f_4302_, lean_object* v_xs_4303_, lean_object* v_k_4304_, lean_object* v_h_4305_, lean_object* v_acc_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_00_u03b1_4299_, v_00_u03b2_4300_, v_n_4301_, v_f_4302_, v_xs_4303_, v_k_4304_, v_h_4305_, v_acc_4306_, v___y_4307_, v___y_4308_);
lean_dec_ref(v___y_4308_);
lean_dec_ref(v_xs_4303_);
lean_dec(v_n_4301_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_inst_4311_, lean_object* v_R_4312_, lean_object* v_a_4313_, lean_object* v_b_4314_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_a_4313_, v_b_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_upperBound_4316_, lean_object* v_fst_4317_, lean_object* v___x_4318_, lean_object* v_leanOpts_4319_, lean_object* v_inst_4320_, lean_object* v_R_4321_, lean_object* v_a_4322_, lean_object* v_b_4323_, lean_object* v_c_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4316_, v_fst_4317_, v___x_4318_, v_leanOpts_4319_, v_a_4322_, v_b_4323_, v___y_4325_, v___y_4326_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_upperBound_4329_, lean_object* v_fst_4330_, lean_object* v___x_4331_, lean_object* v_leanOpts_4332_, lean_object* v_inst_4333_, lean_object* v_R_4334_, lean_object* v_a_4335_, lean_object* v_b_4336_, lean_object* v_c_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4329_, v_fst_4330_, v___x_4331_, v_leanOpts_4332_, v_inst_4333_, v_R_4334_, v_a_4335_, v_b_4336_, v_c_4337_, v___y_4338_, v___y_4339_);
lean_dec_ref(v___y_4339_);
lean_dec_ref(v___x_4331_);
lean_dec_ref(v_fst_4330_);
lean_dec(v_upperBound_4329_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_start_4342_, lean_object* v_pkg_4343_, lean_object* v_leanOpts_4344_, uint8_t v_reconfigure_4345_, lean_object* v_as_4346_, size_t v_i_4347_, size_t v_stop_4348_, lean_object* v_b_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4343_, v_leanOpts_4344_, v_reconfigure_4345_, v_as_4346_, v_i_4347_, v_stop_4348_, v_b_4349_, v___y_4350_, v___y_4351_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_start_4354_, lean_object* v_pkg_4355_, lean_object* v_leanOpts_4356_, lean_object* v_reconfigure_4357_, lean_object* v_as_4358_, lean_object* v_i_4359_, lean_object* v_stop_4360_, lean_object* v_b_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
uint8_t v_reconfigure_boxed_4365_; size_t v_i_boxed_4366_; size_t v_stop_boxed_4367_; lean_object* v_res_4368_; 
v_reconfigure_boxed_4365_ = lean_unbox(v_reconfigure_4357_);
v_i_boxed_4366_ = lean_unbox_usize(v_i_4359_);
lean_dec(v_i_4359_);
v_stop_boxed_4367_ = lean_unbox_usize(v_stop_4360_);
lean_dec(v_stop_4360_);
v_res_4368_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_start_4354_, v_pkg_4355_, v_leanOpts_4356_, v_reconfigure_boxed_4365_, v_as_4358_, v_i_boxed_4366_, v_stop_boxed_4367_, v_b_4361_, v___y_4362_, v___y_4363_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_as_4358_);
lean_dec(v_start_4354_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_4369_, lean_object* v_msg_4370_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v_msg_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object* v_00_u03b2_4372_, lean_object* v_k_4373_, lean_object* v_v_4374_, lean_object* v_t_4375_){
_start:
{
lean_object* v___x_4376_; 
v___x_4376_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_4373_, v_v_4374_, v_t_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object* v_init_4377_, lean_object* v_t_4378_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_4377_, v_t_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4380_, lean_object* v_as_4381_, size_t v_i_4382_, size_t v_stop_4383_, lean_object* v_b_4384_){
_start:
{
lean_object* v___y_4386_; uint8_t v___x_4390_; 
v___x_4390_ = lean_usize_dec_eq(v_i_4382_, v_stop_4383_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; lean_object* v_baseName_4392_; lean_object* v_relConfigFile_4393_; lean_object* v_relManifestFile_4394_; lean_object* v___x_4395_; 
v___x_4391_ = lean_array_uget_borrowed(v_as_4381_, v_i_4382_);
v_baseName_4392_ = lean_ctor_get(v___x_4391_, 1);
v_relConfigFile_4393_ = lean_ctor_get(v___x_4391_, 8);
v_relManifestFile_4394_ = lean_ctor_get(v___x_4391_, 9);
v___x_4395_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4380_, v_baseName_4392_);
if (lean_obj_tag(v___x_4395_) == 0)
{
v___y_4386_ = v_b_4384_;
goto v___jp_4385_;
}
else
{
lean_object* v_val_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4417_; 
v_val_4396_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4398_ = v___x_4395_;
v_isShared_4399_ = v_isSharedCheck_4417_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_val_4396_);
lean_dec(v___x_4395_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4417_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v_name_4400_; lean_object* v_scope_4401_; uint8_t v_inherited_4402_; lean_object* v_src_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4414_; 
v_name_4400_ = lean_ctor_get(v_val_4396_, 0);
v_scope_4401_ = lean_ctor_get(v_val_4396_, 1);
v_inherited_4402_ = lean_ctor_get_uint8(v_val_4396_, sizeof(void*)*5);
v_src_4403_ = lean_ctor_get(v_val_4396_, 4);
v_isSharedCheck_4414_ = !lean_is_exclusive(v_val_4396_);
if (v_isSharedCheck_4414_ == 0)
{
lean_object* v_unused_4415_; lean_object* v_unused_4416_; 
v_unused_4415_ = lean_ctor_get(v_val_4396_, 3);
lean_dec(v_unused_4415_);
v_unused_4416_ = lean_ctor_get(v_val_4396_, 2);
lean_dec(v_unused_4416_);
v___x_4405_ = v_val_4396_;
v_isShared_4406_ = v_isSharedCheck_4414_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_src_4403_);
lean_inc(v_scope_4401_);
lean_inc(v_name_4400_);
lean_dec(v_val_4396_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4414_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
lean_inc_ref(v_relManifestFile_4394_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 0, v_relManifestFile_4394_);
v___x_4408_ = v___x_4398_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_relManifestFile_4394_);
v___x_4408_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
lean_object* v___x_4410_; 
lean_inc_ref(v_relConfigFile_4393_);
if (v_isShared_4406_ == 0)
{
lean_ctor_set(v___x_4405_, 3, v___x_4408_);
lean_ctor_set(v___x_4405_, 2, v_relConfigFile_4393_);
v___x_4410_ = v___x_4405_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_name_4400_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_scope_4401_);
lean_ctor_set(v_reuseFailAlloc_4412_, 2, v_relConfigFile_4393_);
lean_ctor_set(v_reuseFailAlloc_4412_, 3, v___x_4408_);
lean_ctor_set(v_reuseFailAlloc_4412_, 4, v_src_4403_);
lean_ctor_set_uint8(v_reuseFailAlloc_4412_, sizeof(void*)*5, v_inherited_4402_);
v___x_4410_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
lean_object* v___x_4411_; 
v___x_4411_ = lean_array_push(v_b_4384_, v___x_4410_);
v___y_4386_ = v___x_4411_;
goto v___jp_4385_;
}
}
}
}
}
}
else
{
return v_b_4384_;
}
v___jp_4385_:
{
size_t v___x_4387_; size_t v___x_4388_; 
v___x_4387_ = ((size_t)1ULL);
v___x_4388_ = lean_usize_add(v_i_4382_, v___x_4387_);
v_i_4382_ = v___x_4388_;
v_b_4384_ = v___y_4386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4418_, lean_object* v_as_4419_, lean_object* v_i_4420_, lean_object* v_stop_4421_, lean_object* v_b_4422_){
_start:
{
size_t v_i_boxed_4423_; size_t v_stop_boxed_4424_; lean_object* v_res_4425_; 
v_i_boxed_4423_ = lean_unbox_usize(v_i_4420_);
lean_dec(v_i_4420_);
v_stop_boxed_4424_ = lean_unbox_usize(v_stop_4421_);
lean_dec(v_stop_4421_);
v_res_4425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4418_, v_as_4419_, v_i_boxed_4423_, v_stop_boxed_4424_, v_b_4422_);
lean_dec_ref(v_as_4419_);
lean_dec(v_entries_4418_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4426_, lean_object* v_entries_4427_){
_start:
{
lean_object* v_packages_4429_; lean_object* v___y_4431_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; uint8_t v___x_4449_; 
v_packages_4429_ = lean_ctor_get(v_ws_4426_, 4);
v___x_4446_ = lean_unsigned_to_nat(0u);
v___x_4447_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4448_ = lean_array_get_size(v_packages_4429_);
v___x_4449_ = lean_nat_dec_lt(v___x_4446_, v___x_4448_);
if (v___x_4449_ == 0)
{
v___y_4431_ = v___x_4447_;
goto v___jp_4430_;
}
else
{
size_t v___x_4450_; size_t v___x_4451_; lean_object* v___x_4452_; 
v___x_4450_ = ((size_t)0ULL);
v___x_4451_ = lean_usize_of_nat(v___x_4448_);
v___x_4452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4427_, v_packages_4429_, v___x_4450_, v___x_4451_, v___x_4447_);
v___y_4431_ = v___x_4452_;
goto v___jp_4430_;
}
v___jp_4430_:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v_config_4434_; lean_object* v_baseName_4435_; lean_object* v_dir_4436_; lean_object* v_relManifestFile_4437_; lean_object* v_toWorkspaceConfig_4438_; uint8_t v_fixedToolchain_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v_manifest_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4432_ = lean_unsigned_to_nat(0u);
v___x_4433_ = lean_array_fget_borrowed(v_packages_4429_, v___x_4432_);
v_config_4434_ = lean_ctor_get(v___x_4433_, 6);
v_baseName_4435_ = lean_ctor_get(v___x_4433_, 1);
v_dir_4436_ = lean_ctor_get(v___x_4433_, 4);
v_relManifestFile_4437_ = lean_ctor_get(v___x_4433_, 9);
v_toWorkspaceConfig_4438_ = lean_ctor_get(v_config_4434_, 0);
v_fixedToolchain_4439_ = lean_ctor_get_uint8(v_config_4434_, sizeof(void*)*28 + 6);
v___x_4440_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4438_);
v___x_4441_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4438_);
v___x_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
lean_inc(v_baseName_4435_);
v_manifest_4443_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4443_, 0, v_baseName_4435_);
lean_ctor_set(v_manifest_4443_, 1, v___x_4440_);
lean_ctor_set(v_manifest_4443_, 2, v___x_4442_);
lean_ctor_set(v_manifest_4443_, 3, v___y_4431_);
lean_ctor_set_uint8(v_manifest_4443_, sizeof(void*)*4, v_fixedToolchain_4439_);
lean_inc_ref(v_relManifestFile_4437_);
lean_inc_ref(v_dir_4436_);
v___x_4444_ = l_Lake_joinRelative(v_dir_4436_, v_relManifestFile_4437_);
v___x_4445_ = l_Lake_Manifest_save(v_manifest_4443_, v___x_4444_);
lean_dec_ref(v___x_4444_);
return v___x_4445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4453_, lean_object* v_entries_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4453_, v_entries_4454_);
lean_dec(v_entries_4454_);
lean_dec_ref(v_ws_4453_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4457_, lean_object* v_as_4458_, size_t v_i_4459_, size_t v_stop_4460_, lean_object* v_b_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_a_4466_; uint8_t v___x_4470_; 
v___x_4470_ = lean_usize_dec_eq(v_i_4459_, v_stop_4460_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_6568__overap_4473_; lean_object* v___x_4474_; 
v___x_4471_ = lean_unsigned_to_nat(0u);
v___x_4472_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_6568__overap_4473_ = lean_array_uget_borrowed(v_as_4458_, v_i_4459_);
lean_inc(v___x_6568__overap_4473_);
lean_inc(v___y_4462_);
lean_inc_ref(v_pkg_4457_);
v___x_4474_ = lean_apply_4(v___x_6568__overap_4473_, v_pkg_4457_, v___y_4462_, v___x_4472_, lean_box(0));
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v_a_4476_; lean_object* v___x_4477_; uint8_t v___x_4478_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
v_a_4476_ = lean_ctor_get(v___x_4474_, 1);
lean_inc(v_a_4476_);
lean_dec_ref_known(v___x_4474_, 2);
v___x_4477_ = lean_array_get_size(v_a_4476_);
v___x_4478_ = lean_nat_dec_lt(v___x_4471_, v___x_4477_);
if (v___x_4478_ == 0)
{
lean_dec(v_a_4476_);
v_a_4466_ = v_a_4475_;
goto v___jp_4465_;
}
else
{
lean_object* v___x_4479_; size_t v___x_4480_; size_t v___x_4481_; lean_object* v___x_4482_; 
v___x_4479_ = lean_box(0);
v___x_4480_ = ((size_t)0ULL);
v___x_4481_ = lean_usize_of_nat(v___x_4477_);
v___x_4482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4476_, v___x_4480_, v___x_4481_, v___x_4479_, v___y_4463_);
lean_dec(v_a_4476_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_dec_ref_known(v___x_4482_, 1);
v_a_4466_ = v_a_4475_;
goto v___jp_4465_;
}
else
{
lean_dec(v_a_4475_);
lean_dec_ref(v_pkg_4457_);
return v___x_4482_;
}
}
}
else
{
lean_object* v_a_4483_; lean_object* v___x_4484_; uint8_t v___x_4485_; 
lean_dec_ref(v_pkg_4457_);
v_a_4483_ = lean_ctor_get(v___x_4474_, 1);
lean_inc(v_a_4483_);
lean_dec_ref_known(v___x_4474_, 2);
v___x_4484_ = lean_array_get_size(v_a_4483_);
v___x_4485_ = lean_nat_dec_lt(v___x_4471_, v___x_4484_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
lean_dec(v_a_4483_);
v___x_4486_ = lean_box(0);
v___x_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4486_);
return v___x_4487_;
}
else
{
lean_object* v___x_4488_; size_t v___x_4489_; size_t v___x_4490_; lean_object* v___x_4491_; 
v___x_4488_ = lean_box(0);
v___x_4489_ = ((size_t)0ULL);
v___x_4490_ = lean_usize_of_nat(v___x_4484_);
v___x_4491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4483_, v___x_4489_, v___x_4490_, v___x_4488_, v___y_4463_);
lean_dec(v_a_4483_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; 
v_unused_4499_ = lean_ctor_get(v___x_4491_, 0);
lean_dec(v_unused_4499_);
v___x_4493_ = v___x_4491_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_dec(v___x_4491_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
lean_ctor_set_tag(v___x_4493_, 1);
lean_ctor_set(v___x_4493_, 0, v___x_4488_);
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4488_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
else
{
return v___x_4491_;
}
}
}
}
else
{
lean_object* v___x_4500_; 
lean_dec_ref(v_pkg_4457_);
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v_b_4461_);
return v___x_4500_;
}
v___jp_4465_:
{
size_t v___x_4467_; size_t v___x_4468_; 
v___x_4467_ = ((size_t)1ULL);
v___x_4468_ = lean_usize_add(v_i_4459_, v___x_4467_);
v_i_4459_ = v___x_4468_;
v_b_4461_ = v_a_4466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4501_, lean_object* v_as_4502_, lean_object* v_i_4503_, lean_object* v_stop_4504_, lean_object* v_b_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
size_t v_i_boxed_4509_; size_t v_stop_boxed_4510_; lean_object* v_res_4511_; 
v_i_boxed_4509_ = lean_unbox_usize(v_i_4503_);
lean_dec(v_i_4503_);
v_stop_boxed_4510_ = lean_unbox_usize(v_stop_4504_);
lean_dec(v_stop_4504_);
v_res_4511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4501_, v_as_4502_, v_i_boxed_4509_, v_stop_boxed_4510_, v_b_4505_, v___y_4506_, v___y_4507_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec_ref(v_as_4502_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v_baseName_4517_; lean_object* v_postUpdateHooks_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; uint8_t v___x_4521_; 
v_baseName_4517_ = lean_ctor_get(v_pkg_4513_, 1);
v_postUpdateHooks_4518_ = lean_ctor_get(v_pkg_4513_, 20);
lean_inc_ref(v_postUpdateHooks_4518_);
v___x_4519_ = lean_array_get_size(v_postUpdateHooks_4518_);
v___x_4520_ = lean_unsigned_to_nat(0u);
v___x_4521_ = lean_nat_dec_eq(v___x_4519_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; uint8_t v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; 
lean_inc(v_baseName_4517_);
v___x_4522_ = l_Lean_Name_toString(v_baseName_4517_, v___x_4521_);
v___x_4523_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4524_ = lean_string_append(v___x_4522_, v___x_4523_);
v___x_4525_ = 1;
v___x_4526_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4526_, 0, v___x_4524_);
lean_ctor_set_uint8(v___x_4526_, sizeof(void*)*1, v___x_4525_);
lean_inc_ref(v_a_4515_);
v___x_4527_ = lean_apply_2(v_a_4515_, v___x_4526_, lean_box(0));
v___x_4528_ = lean_box(0);
v___x_4529_ = lean_nat_dec_lt(v___x_4520_, v___x_4519_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; 
lean_dec_ref(v_postUpdateHooks_4518_);
lean_dec_ref(v_pkg_4513_);
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4528_);
return v___x_4530_;
}
else
{
size_t v___x_4531_; size_t v___x_4532_; lean_object* v___x_4533_; 
v___x_4531_ = ((size_t)0ULL);
v___x_4532_ = lean_usize_of_nat(v___x_4519_);
v___x_4533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4513_, v_postUpdateHooks_4518_, v___x_4531_, v___x_4532_, v___x_4528_, v_a_4514_, v_a_4515_);
lean_dec_ref(v_postUpdateHooks_4518_);
return v___x_4533_;
}
}
else
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
lean_dec_ref(v_postUpdateHooks_4518_);
lean_dec_ref(v_pkg_4513_);
v___x_4534_ = lean_box(0);
v___x_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4534_);
return v___x_4535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4536_, v_a_4537_, v_a_4538_);
lean_dec_ref(v_a_4538_);
lean_dec(v_a_4537_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4541_, lean_object* v_ws_4542_, lean_object* v_toUpdate_4543_, lean_object* v_leanOpts_4544_, uint8_t v_updateToolchain_4545_){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4547_ = lean_box(1);
v___x_4548_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4541_, v_ws_4542_, v_toUpdate_4543_, v___x_4547_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v_snd_4550_; uint8_t v___x_4551_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
lean_inc(v_a_4549_);
lean_dec_ref_known(v___x_4548_, 1);
v_snd_4550_ = lean_ctor_get(v_a_4549_, 1);
lean_inc(v_snd_4550_);
lean_dec(v_a_4549_);
v___x_4551_ = 1;
if (v_updateToolchain_4545_ == 0)
{
lean_object* v_packages_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v_wsIdx_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v_packages_4552_ = lean_ctor_get(v_ws_4542_, 4);
v___x_4553_ = lean_unsigned_to_nat(0u);
v___x_4554_ = lean_array_fget_borrowed(v_packages_4552_, v___x_4553_);
v_wsIdx_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_wsIdx_4555_);
v___x_4556_ = lean_array_get_size(v_packages_4552_);
v___x_4557_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4544_, v___x_4551_, v_ws_4542_, v_wsIdx_4555_, v___x_4556_, v_snd_4550_, v_a_4541_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4575_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4560_ = v___x_4557_;
v_isShared_4561_ = v_isSharedCheck_4575_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4557_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4575_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v_fst_4562_; lean_object* v_snd_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4574_; 
v_fst_4562_ = lean_ctor_get(v_a_4558_, 0);
v_snd_4563_ = lean_ctor_get(v_a_4558_, 1);
v_isSharedCheck_4574_ = !lean_is_exclusive(v_a_4558_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4565_ = v_a_4558_;
v_isShared_4566_ = v_isSharedCheck_4574_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_snd_4563_);
lean_inc(v_fst_4562_);
lean_dec(v_a_4558_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4574_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4567_; lean_object* v___x_4569_; 
v___x_4567_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4562_);
if (v_isShared_4566_ == 0)
{
lean_ctor_set(v___x_4565_, 0, v___x_4567_);
v___x_4569_ = v___x_4565_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4573_, 1, v_snd_4563_);
v___x_4569_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_object* v___x_4571_; 
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 0, v___x_4569_);
v___x_4571_ = v___x_4560_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4569_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
else
{
return v___x_4557_;
}
}
else
{
lean_object* v_packages_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v_baseName_4579_; lean_object* v_depConfigs_4580_; lean_object* v___x_4581_; lean_object* v___f_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v_packages_4576_ = lean_ctor_get(v_ws_4542_, 4);
v___x_4577_ = lean_unsigned_to_nat(0u);
v___x_4578_ = lean_array_fget_borrowed(v_packages_4576_, v___x_4577_);
v_baseName_4579_ = lean_ctor_get(v___x_4578_, 1);
v_depConfigs_4580_ = lean_ctor_get(v___x_4578_, 12);
v___x_4581_ = lean_box(v_updateToolchain_4545_);
lean_inc(v___x_4578_);
lean_inc_ref(v_ws_4542_);
lean_inc(v_baseName_4579_);
v___f_4582_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 8, 4);
lean_closure_set(v___f_4582_, 0, v_baseName_4579_);
lean_closure_set(v___f_4582_, 1, v___x_4581_);
lean_closure_set(v___f_4582_, 2, v_ws_4542_);
lean_closure_set(v___f_4582_, 3, v___x_4578_);
v___x_4583_ = lean_array_get_size(v_depConfigs_4580_);
lean_inc_ref(v_depConfigs_4580_);
v___x_4584_ = l_Array_reverse___redArg(v_depConfigs_4580_);
v___x_4585_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4586_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4583_, v___f_4582_, v___x_4584_, v___x_4577_, v___x_4585_, v_snd_4550_, v_a_4541_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v_fst_4588_; lean_object* v_snd_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4661_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
lean_dec_ref_known(v___x_4586_, 1);
v_fst_4588_ = lean_ctor_get(v_a_4587_, 0);
v_snd_4589_ = lean_ctor_get(v_a_4587_, 1);
v_isSharedCheck_4661_ = !lean_is_exclusive(v_a_4587_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4591_ = v_a_4587_;
v_isShared_4592_ = v_isSharedCheck_4661_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_snd_4589_);
lean_inc(v_fst_4588_);
lean_dec(v_a_4587_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4661_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4593_; 
lean_inc_ref(v_ws_4542_);
v___x_4593_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4541_, v_ws_4542_, v_fst_4588_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v___x_4594_; lean_object* v___x_4595_; 
lean_dec_ref_known(v___x_4593_, 1);
v___x_4594_ = lean_array_get_size(v_packages_4576_);
lean_inc_ref(v_leanOpts_4544_);
v___x_4595_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4583_, v_fst_4588_, v___x_4584_, v_leanOpts_4544_, v___x_4577_, v_ws_4542_, v_snd_4589_, v_a_4541_);
lean_dec_ref(v___x_4584_);
lean_dec(v_fst_4588_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4644_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4598_ = v___x_4595_;
v_isShared_4599_ = v_isSharedCheck_4644_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4595_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4644_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v_fst_4600_; lean_object* v_snd_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4643_; 
v_fst_4600_ = lean_ctor_get(v_a_4596_, 0);
v_snd_4601_ = lean_ctor_get(v_a_4596_, 1);
v_isSharedCheck_4643_ = !lean_is_exclusive(v_a_4596_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4603_ = v_a_4596_;
v_isShared_4604_ = v_isSharedCheck_4643_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_snd_4601_);
lean_inc(v_fst_4600_);
lean_dec(v_a_4596_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4643_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v_packages_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4610_; 
v_packages_4605_ = lean_ctor_get(v_fst_4600_, 4);
v___x_4606_ = lean_array_get_size(v_packages_4605_);
v___x_4607_ = lean_array_fget(v_packages_4605_, v___x_4577_);
v___x_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4594_);
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 1, v___x_4606_);
lean_ctor_set(v___x_4591_, 0, v___x_4608_);
v___x_4610_ = v___x_4591_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4642_, 1, v___x_4606_);
v___x_4610_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; uint8_t v___x_4613_; 
v___x_4611_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4610_, v___x_4585_);
v___x_4612_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4600_, v___x_4607_, v___x_4611_);
v___x_4613_ = lean_nat_dec_eq(v___x_4594_, v___x_4606_);
if (v___x_4613_ == 0)
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
lean_del_object(v___x_4603_);
lean_del_object(v___x_4598_);
v___x_4614_ = lean_unsigned_to_nat(1u);
v___x_4615_ = lean_nat_add(v___x_4594_, v___x_4614_);
v___x_4616_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4544_, v___x_4551_, v___x_4612_, v___x_4594_, v___x_4615_, v_snd_4601_, v_a_4541_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4634_; 
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4619_ = v___x_4616_;
v_isShared_4620_ = v_isSharedCheck_4634_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4616_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4634_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v_fst_4621_; lean_object* v_snd_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4633_; 
v_fst_4621_ = lean_ctor_get(v_a_4617_, 0);
v_snd_4622_ = lean_ctor_get(v_a_4617_, 1);
v_isSharedCheck_4633_ = !lean_is_exclusive(v_a_4617_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4624_ = v_a_4617_;
v_isShared_4625_ = v_isSharedCheck_4633_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_snd_4622_);
lean_inc(v_fst_4621_);
lean_dec(v_a_4617_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4633_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4626_; lean_object* v___x_4628_; 
v___x_4626_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4621_);
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 0, v___x_4626_);
v___x_4628_ = v___x_4624_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4626_);
lean_ctor_set(v_reuseFailAlloc_4632_, 1, v_snd_4622_);
v___x_4628_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
lean_object* v___x_4630_; 
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 0, v___x_4628_);
v___x_4630_ = v___x_4619_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4628_);
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
else
{
return v___x_4616_;
}
}
else
{
lean_object* v___x_4635_; lean_object* v___x_4637_; 
lean_dec_ref(v_leanOpts_4544_);
v___x_4635_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4612_);
if (v_isShared_4604_ == 0)
{
lean_ctor_set(v___x_4603_, 0, v___x_4635_);
v___x_4637_ = v___x_4603_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4635_);
lean_ctor_set(v_reuseFailAlloc_4641_, 1, v_snd_4601_);
v___x_4637_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
lean_object* v___x_4639_; 
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 0, v___x_4637_);
v___x_4639_ = v___x_4598_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4637_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
lean_del_object(v___x_4591_);
lean_dec_ref(v_leanOpts_4544_);
v_a_4645_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4595_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4595_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4660_; 
lean_del_object(v___x_4591_);
lean_dec(v_snd_4589_);
lean_dec(v_fst_4588_);
lean_dec_ref(v___x_4584_);
lean_dec_ref(v_leanOpts_4544_);
lean_dec_ref(v_ws_4542_);
v_a_4653_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4655_ = v___x_4593_;
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4593_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4656_ == 0)
{
v___x_4658_ = v___x_4655_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4653_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_dec_ref(v___x_4584_);
lean_dec_ref(v_leanOpts_4544_);
lean_dec_ref(v_ws_4542_);
v_a_4662_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4586_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4586_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4677_; 
lean_dec_ref(v_leanOpts_4544_);
lean_dec_ref(v_ws_4542_);
v_a_4670_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4672_ = v___x_4548_;
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4548_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4675_; 
if (v_isShared_4673_ == 0)
{
v___x_4675_ = v___x_4672_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4678_, lean_object* v_ws_4679_, lean_object* v_toUpdate_4680_, lean_object* v_leanOpts_4681_, lean_object* v_updateToolchain_4682_, lean_object* v_a_4683_){
_start:
{
uint8_t v_updateToolchain_boxed_4684_; lean_object* v_res_4685_; 
v_updateToolchain_boxed_4684_ = lean_unbox(v_updateToolchain_4682_);
v_res_4685_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4678_, v_ws_4679_, v_toUpdate_4680_, v_leanOpts_4681_, v_updateToolchain_boxed_4684_);
lean_dec_ref(v_a_4678_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4686_, size_t v_i_4687_, size_t v_stop_4688_, lean_object* v_b_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
uint8_t v___x_4693_; 
v___x_4693_ = lean_usize_dec_eq(v_i_4687_, v_stop_4688_);
if (v___x_4693_ == 0)
{
lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4694_ = lean_array_uget_borrowed(v_as_4686_, v_i_4687_);
lean_inc(v___x_4694_);
v___x_4695_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4694_, v___y_4690_, v___y_4691_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; size_t v___x_4697_; size_t v___x_4698_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4695_, 1);
v___x_4697_ = ((size_t)1ULL);
v___x_4698_ = lean_usize_add(v_i_4687_, v___x_4697_);
v_i_4687_ = v___x_4698_;
v_b_4689_ = v_a_4696_;
goto _start;
}
else
{
return v___x_4695_;
}
}
else
{
lean_object* v___x_4700_; 
v___x_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4700_, 0, v_b_4689_);
return v___x_4700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4701_, lean_object* v_i_4702_, lean_object* v_stop_4703_, lean_object* v_b_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
size_t v_i_boxed_4708_; size_t v_stop_boxed_4709_; lean_object* v_res_4710_; 
v_i_boxed_4708_ = lean_unbox_usize(v_i_4702_);
lean_dec(v_i_4702_);
v_stop_boxed_4709_ = lean_unbox_usize(v_stop_4703_);
lean_dec(v_stop_4703_);
v_res_4710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4701_, v_i_boxed_4708_, v_stop_boxed_4709_, v_b_4704_, v___y_4705_, v___y_4706_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v_as_4701_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4711_, lean_object* v_toUpdate_4712_, lean_object* v_leanOpts_4713_, uint8_t v_updateToolchain_4714_, lean_object* v_a_4715_){
_start:
{
lean_object* v___x_4717_; 
v___x_4717_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4715_, v_ws_4711_, v_toUpdate_4712_, v_leanOpts_4713_, v_updateToolchain_4714_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_object* v_a_4718_; lean_object* v_fst_4719_; lean_object* v_snd_4720_; lean_object* v___x_4721_; 
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
lean_inc(v_a_4718_);
lean_dec_ref_known(v___x_4717_, 1);
v_fst_4719_ = lean_ctor_get(v_a_4718_, 0);
lean_inc(v_fst_4719_);
v_snd_4720_ = lean_ctor_get(v_a_4718_, 1);
lean_inc(v_snd_4720_);
lean_dec(v_a_4718_);
v___x_4721_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4719_, v_snd_4720_);
lean_dec(v_snd_4720_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4752_; 
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4752_ == 0)
{
lean_object* v_unused_4753_; 
v_unused_4753_ = lean_ctor_get(v___x_4721_, 0);
lean_dec(v_unused_4753_);
v___x_4723_ = v___x_4721_;
v_isShared_4724_ = v_isSharedCheck_4752_;
goto v_resetjp_4722_;
}
else
{
lean_dec(v___x_4721_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4752_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v_packages_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; 
v_packages_4725_ = lean_ctor_get(v_fst_4719_, 4);
v___x_4726_ = lean_unsigned_to_nat(0u);
v___x_4727_ = lean_array_get_size(v_packages_4725_);
v___x_4728_ = lean_nat_dec_lt(v___x_4726_, v___x_4727_);
if (v___x_4728_ == 0)
{
lean_object* v___x_4730_; 
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 0, v_fst_4719_);
v___x_4730_ = v___x_4723_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_fst_4719_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
else
{
lean_object* v___x_4732_; size_t v___x_4733_; size_t v___x_4734_; lean_object* v___x_4735_; 
lean_del_object(v___x_4723_);
v___x_4732_ = lean_box(0);
v___x_4733_ = ((size_t)0ULL);
v___x_4734_ = lean_usize_of_nat(v___x_4727_);
v___x_4735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4725_, v___x_4733_, v___x_4734_, v___x_4732_, v_fst_4719_, v_a_4715_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4742_ == 0)
{
lean_object* v_unused_4743_; 
v_unused_4743_ = lean_ctor_get(v___x_4735_, 0);
lean_dec(v_unused_4743_);
v___x_4737_ = v___x_4735_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_dec(v___x_4735_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 0, v_fst_4719_);
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_fst_4719_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec(v_fst_4719_);
v_a_4744_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4735_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4735_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4766_; 
lean_dec(v_fst_4719_);
v_a_4754_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4756_ = v___x_4721_;
v_isShared_4757_ = v_isSharedCheck_4766_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4721_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4766_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4758_; uint8_t v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4764_; 
v___x_4758_ = lean_io_error_to_string(v_a_4754_);
v___x_4759_ = 3;
v___x_4760_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4760_, 0, v___x_4758_);
lean_ctor_set_uint8(v___x_4760_, sizeof(void*)*1, v___x_4759_);
lean_inc_ref(v_a_4715_);
v___x_4761_ = lean_apply_2(v_a_4715_, v___x_4760_, lean_box(0));
v___x_4762_ = lean_box(0);
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 0, v___x_4762_);
v___x_4764_ = v___x_4756_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
else
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
v_a_4767_ = lean_ctor_get(v___x_4717_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___x_4717_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4717_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4772_; 
if (v_isShared_4770_ == 0)
{
v___x_4772_ = v___x_4769_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4775_, lean_object* v_toUpdate_4776_, lean_object* v_leanOpts_4777_, lean_object* v_updateToolchain_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
uint8_t v_updateToolchain_boxed_4781_; lean_object* v_res_4782_; 
v_updateToolchain_boxed_4781_ = lean_unbox(v_updateToolchain_4778_);
v_res_4782_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4775_, v_toUpdate_4776_, v_leanOpts_4777_, v_updateToolchain_boxed_4781_, v_a_4779_);
lean_dec_ref(v_a_4779_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v_name_4787_, lean_object* v_what_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; uint8_t v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; uint8_t v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_4792_ = lean_string_append(v___x_4791_, v_what_4788_);
v___x_4793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_4794_ = lean_string_append(v___x_4792_, v___x_4793_);
v___x_4795_ = 1;
v___x_4796_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4787_, v___x_4795_);
v___x_4797_ = lean_string_append(v___x_4794_, v___x_4796_);
v___x_4798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_4799_ = lean_string_append(v___x_4797_, v___x_4798_);
v___x_4800_ = lean_string_append(v___x_4799_, v___x_4796_);
lean_dec_ref(v___x_4796_);
v___x_4801_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_4802_ = lean_string_append(v___x_4800_, v___x_4801_);
v___x_4803_ = 2;
v___x_4804_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4804_, 0, v___x_4802_);
lean_ctor_set_uint8(v___x_4804_, sizeof(void*)*1, v___x_4803_);
lean_inc_ref(v___y_4789_);
v___x_4805_ = lean_apply_2(v___y_4789_, v___x_4804_, lean_box(0));
v___x_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4805_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v_name_4807_, lean_object* v_what_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v_name_4807_, v_what_4808_, v___y_4809_);
lean_dec_ref(v___y_4809_);
lean_dec_ref(v_what_4808_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_4815_, lean_object* v_as_4816_, size_t v_i_4817_, size_t v_stop_4818_, lean_object* v_b_4819_, lean_object* v___y_4820_){
_start:
{
lean_object* v_a_4823_; lean_object* v___y_4828_; uint8_t v___x_4830_; 
v___x_4830_ = lean_usize_dec_eq(v_i_4817_, v_stop_4818_);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; lean_object* v_src_x3f_4832_; 
v___x_4831_ = lean_array_uget_borrowed(v_as_4816_, v_i_4817_);
v_src_x3f_4832_ = lean_ctor_get(v___x_4831_, 3);
if (lean_obj_tag(v_src_x3f_4832_) == 1)
{
lean_object* v_name_4833_; lean_object* v_val_4834_; lean_object* v___x_4835_; 
v_name_4833_ = lean_ctor_get(v___x_4831_, 0);
v_val_4834_ = lean_ctor_get(v_src_x3f_4832_, 0);
v___x_4835_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_4815_, v_name_4833_);
if (lean_obj_tag(v___x_4835_) == 1)
{
lean_object* v_val_4836_; lean_object* v___y_4838_; 
v_val_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_val_4836_);
lean_dec_ref_known(v___x_4835_, 1);
if (lean_obj_tag(v_val_4834_) == 0)
{
lean_object* v_src_4841_; 
v_src_4841_ = lean_ctor_get(v_val_4836_, 4);
lean_inc_ref(v_src_4841_);
lean_dec(v_val_4836_);
if (lean_obj_tag(v_src_4841_) == 0)
{
lean_object* v___x_4842_; 
lean_dec_ref_known(v_src_4841_, 1);
v___x_4842_ = lean_box(0);
v_a_4823_ = v___x_4842_;
goto v___jp_4822_;
}
else
{
lean_dec_ref(v_src_4841_);
v___y_4838_ = v___y_4820_;
goto v___jp_4837_;
}
}
else
{
lean_object* v_src_4843_; 
v_src_4843_ = lean_ctor_get(v_val_4836_, 4);
lean_inc_ref(v_src_4843_);
lean_dec(v_val_4836_);
if (lean_obj_tag(v_src_4843_) == 1)
{
lean_object* v_url_4844_; lean_object* v_rev_4845_; lean_object* v_url_4846_; lean_object* v_inputRev_x3f_4847_; lean_object* v___y_4849_; uint8_t v___x_4855_; 
v_url_4844_ = lean_ctor_get(v_val_4834_, 0);
v_rev_4845_ = lean_ctor_get(v_val_4834_, 1);
v_url_4846_ = lean_ctor_get(v_src_4843_, 0);
lean_inc_ref(v_url_4846_);
v_inputRev_x3f_4847_ = lean_ctor_get(v_src_4843_, 2);
lean_inc(v_inputRev_x3f_4847_);
lean_dec_ref_known(v_src_4843_, 4);
v___x_4855_ = lean_string_dec_eq(v_url_4844_, v_url_4846_);
lean_dec_ref(v_url_4846_);
if (v___x_4855_ == 0)
{
lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v_name_4833_);
v___x_4857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v_name_4833_, v___x_4856_, v___y_4820_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_dec_ref_known(v___x_4857_, 1);
v___y_4849_ = v___y_4820_;
goto v___jp_4848_;
}
else
{
lean_dec(v_inputRev_x3f_4847_);
return v___x_4857_;
}
}
else
{
v___y_4849_ = v___y_4820_;
goto v___jp_4848_;
}
v___jp_4848_:
{
lean_object* v___x_4850_; uint8_t v___x_4851_; 
v___x_4850_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_4845_);
v___x_4851_ = l_Option_instDecidableEq___redArg(v___x_4850_, v_rev_4845_, v_inputRev_x3f_4847_);
if (v___x_4851_ == 0)
{
lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v_name_4833_);
v___x_4853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v_name_4833_, v___x_4852_, v___y_4849_);
v___y_4828_ = v___x_4853_;
goto v___jp_4827_;
}
else
{
lean_object* v___x_4854_; 
v___x_4854_ = lean_box(0);
v_a_4823_ = v___x_4854_;
goto v___jp_4822_;
}
}
}
else
{
lean_dec_ref(v_src_4843_);
v___y_4838_ = v___y_4820_;
goto v___jp_4837_;
}
}
v___jp_4837_:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v_name_4833_);
v___x_4840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v_name_4833_, v___x_4839_, v___y_4838_);
v___y_4828_ = v___x_4840_;
goto v___jp_4827_;
}
}
else
{
lean_object* v___x_4858_; 
lean_dec(v___x_4835_);
v___x_4858_ = lean_box(0);
v_a_4823_ = v___x_4858_;
goto v___jp_4822_;
}
}
else
{
lean_object* v___x_4859_; 
v___x_4859_ = lean_box(0);
v_a_4823_ = v___x_4859_;
goto v___jp_4822_;
}
}
else
{
lean_object* v___x_4860_; 
v___x_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4860_, 0, v_b_4819_);
return v___x_4860_;
}
v___jp_4822_:
{
size_t v___x_4824_; size_t v___x_4825_; 
v___x_4824_ = ((size_t)1ULL);
v___x_4825_ = lean_usize_add(v_i_4817_, v___x_4824_);
v_i_4817_ = v___x_4825_;
v_b_4819_ = v_a_4823_;
goto _start;
}
v___jp_4827_:
{
if (lean_obj_tag(v___y_4828_) == 0)
{
lean_object* v_a_4829_; 
v_a_4829_ = lean_ctor_get(v___y_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref_known(v___y_4828_, 1);
v_a_4823_ = v_a_4829_;
goto v___jp_4822_;
}
else
{
return v___y_4828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_4861_, lean_object* v_as_4862_, lean_object* v_i_4863_, lean_object* v_stop_4864_, lean_object* v_b_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
size_t v_i_boxed_4868_; size_t v_stop_boxed_4869_; lean_object* v_res_4870_; 
v_i_boxed_4868_ = lean_unbox_usize(v_i_4863_);
lean_dec(v_i_4863_);
v_stop_boxed_4869_ = lean_unbox_usize(v_stop_4864_);
lean_dec(v_stop_4864_);
v_res_4870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4861_, v_as_4862_, v_i_boxed_4868_, v_stop_boxed_4869_, v_b_4865_, v___y_4866_);
lean_dec_ref(v___y_4866_);
lean_dec_ref(v_as_4862_);
lean_dec(v_pkgEntries_4861_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_4871_, lean_object* v_deps_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; uint8_t v___x_4878_; 
v___x_4875_ = lean_unsigned_to_nat(0u);
v___x_4876_ = lean_array_get_size(v_deps_4872_);
v___x_4877_ = lean_box(0);
v___x_4878_ = lean_nat_dec_lt(v___x_4875_, v___x_4876_);
if (v___x_4878_ == 0)
{
lean_object* v___x_4879_; 
v___x_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4877_);
return v___x_4879_;
}
else
{
size_t v___x_4880_; size_t v___x_4881_; lean_object* v___x_4882_; 
v___x_4880_ = ((size_t)0ULL);
v___x_4881_ = lean_usize_of_nat(v___x_4876_);
v___x_4882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4871_, v_deps_4872_, v___x_4880_, v___x_4881_, v___x_4877_, v_a_4873_);
return v___x_4882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_4883_, lean_object* v_deps_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_4883_, v_deps_4884_, v_a_4885_);
lean_dec_ref(v_a_4885_);
lean_dec_ref(v_deps_4884_);
lean_dec(v_pkgEntries_4883_);
return v_res_4887_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_4888_, lean_object* v_x_4889_){
_start:
{
if (lean_obj_tag(v_x_4888_) == 0)
{
if (lean_obj_tag(v_x_4889_) == 0)
{
uint8_t v___x_4890_; 
v___x_4890_ = 1;
return v___x_4890_;
}
else
{
uint8_t v___x_4891_; 
v___x_4891_ = 0;
return v___x_4891_;
}
}
else
{
if (lean_obj_tag(v_x_4889_) == 0)
{
uint8_t v___x_4892_; 
v___x_4892_ = 0;
return v___x_4892_;
}
else
{
lean_object* v_val_4893_; lean_object* v_val_4894_; uint8_t v___x_4895_; 
v_val_4893_ = lean_ctor_get(v_x_4888_, 0);
v_val_4894_ = lean_ctor_get(v_x_4889_, 0);
v___x_4895_ = lean_string_dec_eq(v_val_4893_, v_val_4894_);
return v___x_4895_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_4896_, lean_object* v_x_4897_){
_start:
{
uint8_t v_res_4898_; lean_object* v_r_4899_; 
v_res_4898_ = l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_4896_, v_x_4897_);
lean_dec(v_x_4897_);
lean_dec(v_x_4896_);
v_r_4899_ = lean_box(v_res_4898_);
return v_r_4899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_pkg_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v_leanOpts_4908_, uint8_t v_reconfigure_4909_, lean_object* v_as_4910_, size_t v_i_4911_, size_t v_stop_4912_, lean_object* v_b_4913_, lean_object* v___y_4914_){
_start:
{
uint8_t v___x_4916_; 
v___x_4916_ = lean_usize_dec_eq(v_i_4911_, v_stop_4912_);
if (v___x_4916_ == 0)
{
lean_object* v_ws_4917_; lean_object* v_depIdxs_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_5048_; 
v_ws_4917_ = lean_ctor_get(v_b_4913_, 0);
v_depIdxs_4918_ = lean_ctor_get(v_b_4913_, 1);
v_isSharedCheck_5048_ = !lean_is_exclusive(v_b_4913_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_4920_ = v_b_4913_;
v_isShared_4921_ = v_isSharedCheck_5048_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_depIdxs_4918_);
lean_inc(v_ws_4917_);
lean_dec(v_b_4913_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_5048_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v_lakeEnv_4922_; lean_object* v_packages_4923_; size_t v___x_4924_; size_t v___x_4925_; lean_object* v___x_4926_; lean_object* v___f_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v_lakeEnv_4922_ = lean_ctor_get(v_ws_4917_, 0);
v_packages_4923_ = lean_ctor_get(v_ws_4917_, 4);
v___x_4924_ = ((size_t)1ULL);
v___x_4925_ = lean_usize_sub(v_i_4911_, v___x_4924_);
v___x_4926_ = lean_array_uget_borrowed(v_as_4910_, v___x_4925_);
lean_inc(v___x_4926_);
v___f_4927_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4927_, 0, v___x_4926_);
v___x_4928_ = lean_unsigned_to_nat(0u);
v___x_4929_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_4927_, v_packages_4923_, v___x_4928_);
if (lean_obj_tag(v___x_4929_) == 1)
{
lean_object* v_val_4930_; lean_object* v___x_4931_; lean_object* v___x_4933_; 
v_val_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_val_4930_);
lean_dec_ref_known(v___x_4929_, 1);
v___x_4931_ = lean_array_push(v_depIdxs_4918_, v_val_4930_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 1, v___x_4931_);
v___x_4933_ = v___x_4920_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_ws_4917_);
lean_ctor_set(v_reuseFailAlloc_4935_, 1, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
v_i_4911_ = v___x_4925_;
v_b_4913_ = v___x_4933_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_4936_; lean_object* v_baseName_4937_; lean_object* v_name_4938_; lean_object* v_opts_4939_; uint8_t v___x_4940_; 
lean_dec(v___x_4929_);
v_wsIdx_4936_ = lean_ctor_get(v_pkg_4905_, 0);
v_baseName_4937_ = lean_ctor_get(v_pkg_4905_, 1);
v_name_4938_ = lean_ctor_get(v___x_4926_, 0);
v_opts_4939_ = lean_ctor_get(v___x_4926_, 4);
v___x_4940_ = lean_name_eq(v_baseName_4937_, v_name_4938_);
if (v___x_4940_ == 0)
{
lean_object* v___x_4941_; 
v___x_4941_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_4906_, v_name_4938_);
if (lean_obj_tag(v___x_4941_) == 1)
{
lean_object* v_val_4942_; lean_object* v___x_4943_; lean_object* v_dir_4944_; lean_object* v___x_4945_; 
v_val_4942_ = lean_ctor_get(v___x_4941_, 0);
lean_inc(v_val_4942_);
lean_dec_ref_known(v___x_4941_, 1);
v___x_4943_ = lean_array_fget_borrowed(v_packages_4923_, v___x_4928_);
v_dir_4944_ = lean_ctor_get(v___x_4943_, 4);
lean_inc_ref(v___y_4907_);
lean_inc_ref(v_dir_4944_);
v___x_4945_ = l_Lake_PackageEntry_materialize(v_val_4942_, v_lakeEnv_4922_, v_dir_4944_, v___y_4907_, v___y_4914_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_5002_; 
v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4948_ = v___x_4945_;
v_isShared_4949_ = v_isSharedCheck_5002_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4945_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_5002_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4950_; lean_object* v_wsIdx_4951_; lean_object* v___x_4952_; 
v___x_4950_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_4951_ = lean_array_get_size(v_packages_4923_);
lean_inc_ref(v_leanOpts_4908_);
lean_inc(v_opts_4939_);
v___x_4952_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_4917_, v_a_4946_, v_opts_4939_, v_leanOpts_4908_, v_reconfigure_4909_, v___x_4950_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v_a_4953_; lean_object* v_a_4954_; lean_object* v___x_4955_; lean_object* v___x_4957_; 
lean_del_object(v___x_4948_);
v_a_4953_ = lean_ctor_get(v___x_4952_, 0);
lean_inc(v_a_4953_);
v_a_4954_ = lean_ctor_get(v___x_4952_, 1);
lean_inc(v_a_4954_);
lean_dec_ref_known(v___x_4952_, 2);
v___x_4955_ = lean_array_push(v_depIdxs_4918_, v_wsIdx_4951_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 1, v___x_4955_);
lean_ctor_set(v___x_4920_, 0, v_a_4953_);
v___x_4957_ = v___x_4920_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4953_);
lean_ctor_set(v_reuseFailAlloc_4974_, 1, v___x_4955_);
v___x_4957_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
lean_object* v___x_4958_; uint8_t v___x_4959_; 
v___x_4958_ = lean_array_get_size(v_a_4954_);
v___x_4959_ = lean_nat_dec_lt(v___x_4928_, v___x_4958_);
if (v___x_4959_ == 0)
{
lean_dec(v_a_4954_);
v_i_4911_ = v___x_4925_;
v_b_4913_ = v___x_4957_;
goto _start;
}
else
{
lean_object* v___x_4961_; size_t v___x_4962_; size_t v___x_4963_; lean_object* v___x_4964_; 
v___x_4961_ = lean_box(0);
v___x_4962_ = ((size_t)0ULL);
v___x_4963_ = lean_usize_of_nat(v___x_4958_);
v___x_4964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4954_, v___x_4962_, v___x_4963_, v___x_4961_, v___y_4914_);
lean_dec(v_a_4954_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_dec_ref_known(v___x_4964_, 1);
v_i_4911_ = v___x_4925_;
v_b_4913_ = v___x_4957_;
goto _start;
}
else
{
lean_object* v_a_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4973_; 
lean_dec_ref(v___x_4957_);
lean_dec_ref(v_leanOpts_4908_);
lean_dec_ref(v___y_4907_);
lean_dec_ref(v_pkg_4905_);
v_a_4966_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4968_ = v___x_4964_;
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_a_4966_);
lean_dec(v___x_4964_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4971_; 
if (v_isShared_4969_ == 0)
{
v___x_4971_ = v___x_4968_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4966_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
}
}
else
{
lean_object* v_a_4975_; lean_object* v___x_4976_; uint8_t v___x_4977_; 
lean_del_object(v___x_4920_);
lean_dec_ref(v_depIdxs_4918_);
lean_dec_ref(v_leanOpts_4908_);
lean_dec_ref(v___y_4907_);
lean_dec_ref(v_pkg_4905_);
v_a_4975_ = lean_ctor_get(v___x_4952_, 1);
lean_inc(v_a_4975_);
lean_dec_ref_known(v___x_4952_, 2);
v___x_4976_ = lean_array_get_size(v_a_4975_);
v___x_4977_ = lean_nat_dec_lt(v___x_4928_, v___x_4976_);
if (v___x_4977_ == 0)
{
lean_object* v___x_4978_; lean_object* v___x_4980_; 
lean_dec(v_a_4975_);
v___x_4978_ = lean_box(0);
if (v_isShared_4949_ == 0)
{
lean_ctor_set_tag(v___x_4948_, 1);
lean_ctor_set(v___x_4948_, 0, v___x_4978_);
v___x_4980_ = v___x_4948_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v___x_4978_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
else
{
lean_object* v___x_4982_; size_t v___x_4983_; size_t v___x_4984_; lean_object* v___x_4985_; 
lean_del_object(v___x_4948_);
v___x_4982_ = lean_box(0);
v___x_4983_ = ((size_t)0ULL);
v___x_4984_ = lean_usize_of_nat(v___x_4976_);
v___x_4985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_4975_, v___x_4983_, v___x_4984_, v___x_4982_, v___y_4914_);
lean_dec(v_a_4975_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4992_; 
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_4992_ == 0)
{
lean_object* v_unused_4993_; 
v_unused_4993_ = lean_ctor_get(v___x_4985_, 0);
lean_dec(v_unused_4993_);
v___x_4987_ = v___x_4985_;
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
else
{
lean_dec(v___x_4985_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4990_; 
if (v_isShared_4988_ == 0)
{
lean_ctor_set_tag(v___x_4987_, 1);
lean_ctor_set(v___x_4987_, 0, v___x_4982_);
v___x_4990_ = v___x_4987_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v___x_4982_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
else
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5001_; 
v_a_4994_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4996_ = v___x_4985_;
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4985_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4999_; 
if (v_isShared_4997_ == 0)
{
v___x_4999_ = v___x_4996_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_a_4994_);
v___x_4999_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
return v___x_4999_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5010_; 
lean_del_object(v___x_4920_);
lean_dec_ref(v_depIdxs_4918_);
lean_dec_ref(v_ws_4917_);
lean_dec_ref(v_leanOpts_4908_);
lean_dec_ref(v___y_4907_);
lean_dec_ref(v_pkg_4905_);
v_a_5003_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_5005_ = v___x_4945_;
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_4945_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_5006_ == 0)
{
v___x_5008_ = v___x_5005_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
}
}
else
{
uint8_t v___x_5011_; 
lean_inc(v_baseName_4937_);
lean_inc(v_wsIdx_4936_);
lean_dec(v___x_4941_);
lean_del_object(v___x_4920_);
lean_dec_ref(v_depIdxs_4918_);
lean_dec_ref(v_ws_4917_);
lean_dec_ref(v_leanOpts_4908_);
lean_dec_ref(v___y_4907_);
lean_dec_ref(v_pkg_4905_);
v___x_5011_ = lean_nat_dec_eq(v_wsIdx_4936_, v___x_4928_);
lean_dec(v_wsIdx_4936_);
if (v___x_5011_ == 0)
{
lean_object* v___x_5012_; uint8_t v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; uint8_t v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5013_ = 1;
lean_inc(v_name_4938_);
v___x_5014_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4938_, v___x_5013_);
v___x_5015_ = lean_string_append(v___x_5012_, v___x_5014_);
lean_dec_ref(v___x_5014_);
v___x_5016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5017_ = lean_string_append(v___x_5015_, v___x_5016_);
v___x_5018_ = l_Lean_Name_toString(v_baseName_4937_, v___x_5011_);
v___x_5019_ = lean_string_append(v___x_5017_, v___x_5018_);
lean_dec_ref(v___x_5018_);
v___x_5020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5021_ = lean_string_append(v___x_5019_, v___x_5020_);
v___x_5022_ = 3;
v___x_5023_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5023_, 0, v___x_5021_);
lean_ctor_set_uint8(v___x_5023_, sizeof(void*)*1, v___x_5022_);
lean_inc_ref(v___y_4914_);
v___x_5024_ = lean_apply_2(v___y_4914_, v___x_5023_, lean_box(0));
v___x_5025_ = lean_box(0);
v___x_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5025_);
return v___x_5026_;
}
else
{
lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; uint8_t v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
lean_dec(v_baseName_4937_);
v___x_5027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_4938_);
v___x_5028_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4938_, v___x_5011_);
v___x_5029_ = lean_string_append(v___x_5027_, v___x_5028_);
v___x_5030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5031_ = lean_string_append(v___x_5029_, v___x_5030_);
v___x_5032_ = lean_string_append(v___x_5031_, v___x_5028_);
lean_dec_ref(v___x_5028_);
v___x_5033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5034_ = lean_string_append(v___x_5032_, v___x_5033_);
v___x_5035_ = 3;
v___x_5036_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5036_, 0, v___x_5034_);
lean_ctor_set_uint8(v___x_5036_, sizeof(void*)*1, v___x_5035_);
lean_inc_ref(v___y_4914_);
v___x_5037_ = lean_apply_2(v___y_4914_, v___x_5036_, lean_box(0));
v___x_5038_ = lean_box(0);
v___x_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5039_, 0, v___x_5038_);
return v___x_5039_;
}
}
}
else
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; uint8_t v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
lean_inc(v_baseName_4937_);
lean_del_object(v___x_4920_);
lean_dec_ref(v_depIdxs_4918_);
lean_dec_ref(v_ws_4917_);
lean_dec_ref(v_leanOpts_4908_);
lean_dec_ref(v___y_4907_);
lean_dec_ref(v_pkg_4905_);
v___x_5040_ = l_Lean_Name_toString(v_baseName_4937_, v___x_4916_);
v___x_5041_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5042_ = lean_string_append(v___x_5040_, v___x_5041_);
v___x_5043_ = 3;
v___x_5044_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5044_, 0, v___x_5042_);
lean_ctor_set_uint8(v___x_5044_, sizeof(void*)*1, v___x_5043_);
lean_inc_ref(v___y_4914_);
v___x_5045_ = lean_apply_2(v___y_4914_, v___x_5044_, lean_box(0));
v___x_5046_ = lean_box(0);
v___x_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5047_, 0, v___x_5046_);
return v___x_5047_;
}
}
}
}
else
{
lean_object* v___x_5049_; 
lean_dec_ref(v_leanOpts_4908_);
lean_dec_ref(v___y_4907_);
lean_dec_ref(v_pkg_4905_);
v___x_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5049_, 0, v_b_4913_);
return v___x_5049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_pkg_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v_leanOpts_5053_, lean_object* v_reconfigure_5054_, lean_object* v_as_5055_, lean_object* v_i_5056_, lean_object* v_stop_5057_, lean_object* v_b_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_){
_start:
{
uint8_t v_reconfigure_boxed_5061_; size_t v_i_boxed_5062_; size_t v_stop_boxed_5063_; lean_object* v_res_5064_; 
v_reconfigure_boxed_5061_ = lean_unbox(v_reconfigure_5054_);
v_i_boxed_5062_ = lean_unbox_usize(v_i_5056_);
lean_dec(v_i_5056_);
v_stop_boxed_5063_ = lean_unbox_usize(v_stop_5057_);
lean_dec(v_stop_5057_);
v_res_5064_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5050_, v___y_5051_, v___y_5052_, v_leanOpts_5053_, v_reconfigure_boxed_5061_, v_as_5055_, v_i_boxed_5062_, v_stop_boxed_5063_, v_b_5058_, v___y_5059_);
lean_dec_ref(v___y_5059_);
lean_dec_ref(v_as_5055_);
lean_dec(v___y_5051_);
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_start_5065_, lean_object* v_pkg_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v_leanOpts_5069_, uint8_t v_reconfigure_5070_, lean_object* v_as_5071_, size_t v_i_5072_, size_t v_stop_5073_, lean_object* v_b_5074_, lean_object* v___y_5075_){
_start:
{
uint8_t v___x_5077_; 
v___x_5077_ = lean_usize_dec_eq(v_i_5072_, v_stop_5073_);
if (v___x_5077_ == 0)
{
lean_object* v_ws_5078_; lean_object* v_depIdxs_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5209_; 
v_ws_5078_ = lean_ctor_get(v_b_5074_, 0);
v_depIdxs_5079_ = lean_ctor_get(v_b_5074_, 1);
v_isSharedCheck_5209_ = !lean_is_exclusive(v_b_5074_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5081_ = v_b_5074_;
v_isShared_5082_ = v_isSharedCheck_5209_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_depIdxs_5079_);
lean_inc(v_ws_5078_);
lean_dec(v_b_5074_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5209_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v_lakeEnv_5083_; lean_object* v_packages_5084_; size_t v___x_5085_; size_t v___x_5086_; lean_object* v___x_5087_; lean_object* v___f_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
v_lakeEnv_5083_ = lean_ctor_get(v_ws_5078_, 0);
v_packages_5084_ = lean_ctor_get(v_ws_5078_, 4);
v___x_5085_ = ((size_t)1ULL);
v___x_5086_ = lean_usize_sub(v_i_5072_, v___x_5085_);
v___x_5087_ = lean_array_uget_borrowed(v_as_5071_, v___x_5086_);
lean_inc(v___x_5087_);
v___f_5088_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5088_, 0, v___x_5087_);
v___x_5089_ = lean_unsigned_to_nat(0u);
v___x_5090_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5088_, v_packages_5084_, v___x_5089_);
if (lean_obj_tag(v___x_5090_) == 1)
{
lean_object* v_val_5091_; lean_object* v___x_5092_; lean_object* v___x_5094_; 
v_val_5091_ = lean_ctor_get(v___x_5090_, 0);
lean_inc(v_val_5091_);
lean_dec_ref_known(v___x_5090_, 1);
v___x_5092_ = lean_array_push(v_depIdxs_5079_, v_val_5091_);
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 1, v___x_5092_);
v___x_5094_ = v___x_5081_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_ws_5078_);
lean_ctor_set(v_reuseFailAlloc_5096_, 1, v___x_5092_);
v___x_5094_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5095_; 
v___x_5095_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5066_, v___y_5067_, v___y_5068_, v_leanOpts_5069_, v_reconfigure_5070_, v_as_5071_, v___x_5086_, v_stop_5073_, v___x_5094_, v___y_5075_);
return v___x_5095_;
}
}
else
{
lean_object* v_wsIdx_5097_; lean_object* v_baseName_5098_; lean_object* v_name_5099_; lean_object* v_opts_5100_; uint8_t v___x_5101_; 
lean_dec(v___x_5090_);
v_wsIdx_5097_ = lean_ctor_get(v_pkg_5066_, 0);
v_baseName_5098_ = lean_ctor_get(v_pkg_5066_, 1);
v_name_5099_ = lean_ctor_get(v___x_5087_, 0);
v_opts_5100_ = lean_ctor_get(v___x_5087_, 4);
v___x_5101_ = lean_name_eq(v_baseName_5098_, v_name_5099_);
if (v___x_5101_ == 0)
{
lean_object* v___x_5102_; 
v___x_5102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5067_, v_name_5099_);
if (lean_obj_tag(v___x_5102_) == 1)
{
lean_object* v_val_5103_; lean_object* v___x_5104_; lean_object* v_dir_5105_; lean_object* v___x_5106_; 
v_val_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_val_5103_);
lean_dec_ref_known(v___x_5102_, 1);
v___x_5104_ = lean_array_fget_borrowed(v_packages_5084_, v___x_5089_);
v_dir_5105_ = lean_ctor_get(v___x_5104_, 4);
lean_inc_ref(v___y_5068_);
lean_inc_ref(v_dir_5105_);
v___x_5106_ = l_Lake_PackageEntry_materialize(v_val_5103_, v_lakeEnv_5083_, v_dir_5105_, v___y_5068_, v___y_5075_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5163_; 
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5109_ = v___x_5106_;
v_isShared_5110_ = v_isSharedCheck_5163_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_5106_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5163_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5111_; lean_object* v_wsIdx_5112_; lean_object* v___x_5113_; 
v___x_5111_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v_wsIdx_5112_ = lean_array_get_size(v_packages_5084_);
lean_inc_ref(v_leanOpts_5069_);
lean_inc(v_opts_5100_);
v___x_5113_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5078_, v_a_5107_, v_opts_5100_, v_leanOpts_5069_, v_reconfigure_5070_, v___x_5111_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; lean_object* v_a_5115_; lean_object* v___x_5116_; lean_object* v___x_5118_; 
lean_del_object(v___x_5109_);
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc(v_a_5114_);
v_a_5115_ = lean_ctor_get(v___x_5113_, 1);
lean_inc(v_a_5115_);
lean_dec_ref_known(v___x_5113_, 2);
v___x_5116_ = lean_array_push(v_depIdxs_5079_, v_wsIdx_5112_);
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 1, v___x_5116_);
lean_ctor_set(v___x_5081_, 0, v_a_5114_);
v___x_5118_ = v___x_5081_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_a_5114_);
lean_ctor_set(v_reuseFailAlloc_5135_, 1, v___x_5116_);
v___x_5118_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
lean_object* v___x_5119_; uint8_t v___x_5120_; 
v___x_5119_ = lean_array_get_size(v_a_5115_);
v___x_5120_ = lean_nat_dec_lt(v___x_5089_, v___x_5119_);
if (v___x_5120_ == 0)
{
lean_object* v___x_5121_; 
lean_dec(v_a_5115_);
v___x_5121_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5066_, v___y_5067_, v___y_5068_, v_leanOpts_5069_, v_reconfigure_5070_, v_as_5071_, v___x_5086_, v_stop_5073_, v___x_5118_, v___y_5075_);
return v___x_5121_;
}
else
{
lean_object* v___x_5122_; size_t v___x_5123_; size_t v___x_5124_; lean_object* v___x_5125_; 
v___x_5122_ = lean_box(0);
v___x_5123_ = ((size_t)0ULL);
v___x_5124_ = lean_usize_of_nat(v___x_5119_);
v___x_5125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5115_, v___x_5123_, v___x_5124_, v___x_5122_, v___y_5075_);
lean_dec(v_a_5115_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v___x_5126_; 
lean_dec_ref_known(v___x_5125_, 1);
v___x_5126_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5066_, v___y_5067_, v___y_5068_, v_leanOpts_5069_, v_reconfigure_5070_, v_as_5071_, v___x_5086_, v_stop_5073_, v___x_5118_, v___y_5075_);
return v___x_5126_;
}
else
{
lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5134_; 
lean_dec_ref(v___x_5118_);
lean_dec_ref(v_leanOpts_5069_);
lean_dec_ref(v___y_5068_);
lean_dec_ref(v_pkg_5066_);
v_a_5127_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5134_ == 0)
{
v___x_5129_ = v___x_5125_;
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5125_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5132_; 
if (v_isShared_5130_ == 0)
{
v___x_5132_ = v___x_5129_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
}
}
}
}
}
}
else
{
lean_object* v_a_5136_; lean_object* v___x_5137_; uint8_t v___x_5138_; 
lean_del_object(v___x_5081_);
lean_dec_ref(v_depIdxs_5079_);
lean_dec_ref(v_leanOpts_5069_);
lean_dec_ref(v___y_5068_);
lean_dec_ref(v_pkg_5066_);
v_a_5136_ = lean_ctor_get(v___x_5113_, 1);
lean_inc(v_a_5136_);
lean_dec_ref_known(v___x_5113_, 2);
v___x_5137_ = lean_array_get_size(v_a_5136_);
v___x_5138_ = lean_nat_dec_lt(v___x_5089_, v___x_5137_);
if (v___x_5138_ == 0)
{
lean_object* v___x_5139_; lean_object* v___x_5141_; 
lean_dec(v_a_5136_);
v___x_5139_ = lean_box(0);
if (v_isShared_5110_ == 0)
{
lean_ctor_set_tag(v___x_5109_, 1);
lean_ctor_set(v___x_5109_, 0, v___x_5139_);
v___x_5141_ = v___x_5109_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v___x_5139_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
else
{
lean_object* v___x_5143_; size_t v___x_5144_; size_t v___x_5145_; lean_object* v___x_5146_; 
lean_del_object(v___x_5109_);
v___x_5143_ = lean_box(0);
v___x_5144_ = ((size_t)0ULL);
v___x_5145_ = lean_usize_of_nat(v___x_5137_);
v___x_5146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__3(v_a_5136_, v___x_5144_, v___x_5145_, v___x_5143_, v___y_5075_);
lean_dec(v_a_5136_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5153_ == 0)
{
lean_object* v_unused_5154_; 
v_unused_5154_ = lean_ctor_get(v___x_5146_, 0);
lean_dec(v_unused_5154_);
v___x_5148_ = v___x_5146_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_dec(v___x_5146_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
lean_ctor_set_tag(v___x_5148_, 1);
lean_ctor_set(v___x_5148_, 0, v___x_5143_);
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5143_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
else
{
lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5162_; 
v_a_5155_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5157_ = v___x_5146_;
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_dec(v___x_5146_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v___x_5160_; 
if (v_isShared_5158_ == 0)
{
v___x_5160_ = v___x_5157_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_a_5155_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
lean_del_object(v___x_5081_);
lean_dec_ref(v_depIdxs_5079_);
lean_dec_ref(v_ws_5078_);
lean_dec_ref(v_leanOpts_5069_);
lean_dec_ref(v___y_5068_);
lean_dec_ref(v_pkg_5066_);
v_a_5164_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5106_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5106_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
else
{
uint8_t v___x_5172_; 
lean_inc(v_baseName_5098_);
lean_inc(v_wsIdx_5097_);
lean_dec(v___x_5102_);
lean_del_object(v___x_5081_);
lean_dec_ref(v_depIdxs_5079_);
lean_dec_ref(v_ws_5078_);
lean_dec_ref(v_leanOpts_5069_);
lean_dec_ref(v___y_5068_);
lean_dec_ref(v_pkg_5066_);
v___x_5172_ = lean_nat_dec_eq(v_wsIdx_5097_, v___x_5089_);
lean_dec(v_wsIdx_5097_);
if (v___x_5172_ == 0)
{
lean_object* v___x_5173_; uint8_t v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; uint8_t v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v___x_5173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5174_ = 1;
lean_inc(v_name_5099_);
v___x_5175_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5099_, v___x_5174_);
v___x_5176_ = lean_string_append(v___x_5173_, v___x_5175_);
lean_dec_ref(v___x_5175_);
v___x_5177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5178_ = lean_string_append(v___x_5176_, v___x_5177_);
v___x_5179_ = l_Lean_Name_toString(v_baseName_5098_, v___x_5172_);
v___x_5180_ = lean_string_append(v___x_5178_, v___x_5179_);
lean_dec_ref(v___x_5179_);
v___x_5181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5182_ = lean_string_append(v___x_5180_, v___x_5181_);
v___x_5183_ = 3;
v___x_5184_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5184_, 0, v___x_5182_);
lean_ctor_set_uint8(v___x_5184_, sizeof(void*)*1, v___x_5183_);
lean_inc_ref(v___y_5075_);
v___x_5185_ = lean_apply_2(v___y_5075_, v___x_5184_, lean_box(0));
v___x_5186_ = lean_box(0);
v___x_5187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5186_);
return v___x_5187_;
}
else
{
lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; uint8_t v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; 
lean_dec(v_baseName_5098_);
v___x_5188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5099_);
v___x_5189_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5099_, v___x_5172_);
v___x_5190_ = lean_string_append(v___x_5188_, v___x_5189_);
v___x_5191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5192_ = lean_string_append(v___x_5190_, v___x_5191_);
v___x_5193_ = lean_string_append(v___x_5192_, v___x_5189_);
lean_dec_ref(v___x_5189_);
v___x_5194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5195_ = lean_string_append(v___x_5193_, v___x_5194_);
v___x_5196_ = 3;
v___x_5197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5197_, 0, v___x_5195_);
lean_ctor_set_uint8(v___x_5197_, sizeof(void*)*1, v___x_5196_);
lean_inc_ref(v___y_5075_);
v___x_5198_ = lean_apply_2(v___y_5075_, v___x_5197_, lean_box(0));
v___x_5199_ = lean_box(0);
v___x_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5199_);
return v___x_5200_;
}
}
}
else
{
lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; uint8_t v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
lean_inc(v_baseName_5098_);
lean_del_object(v___x_5081_);
lean_dec_ref(v_depIdxs_5079_);
lean_dec_ref(v_ws_5078_);
lean_dec_ref(v_leanOpts_5069_);
lean_dec_ref(v___y_5068_);
lean_dec_ref(v_pkg_5066_);
v___x_5201_ = l_Lean_Name_toString(v_baseName_5098_, v___x_5077_);
v___x_5202_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5203_ = lean_string_append(v___x_5201_, v___x_5202_);
v___x_5204_ = 3;
v___x_5205_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5205_, 0, v___x_5203_);
lean_ctor_set_uint8(v___x_5205_, sizeof(void*)*1, v___x_5204_);
lean_inc_ref(v___y_5075_);
v___x_5206_ = lean_apply_2(v___y_5075_, v___x_5205_, lean_box(0));
v___x_5207_ = lean_box(0);
v___x_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5208_, 0, v___x_5207_);
return v___x_5208_;
}
}
}
}
else
{
lean_object* v___x_5210_; 
lean_dec_ref(v_leanOpts_5069_);
lean_dec_ref(v___y_5068_);
lean_dec_ref(v_pkg_5066_);
v___x_5210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5210_, 0, v_b_5074_);
return v___x_5210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_start_5211_, lean_object* v_pkg_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v_leanOpts_5215_, lean_object* v_reconfigure_5216_, lean_object* v_as_5217_, lean_object* v_i_5218_, lean_object* v_stop_5219_, lean_object* v_b_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
uint8_t v_reconfigure_boxed_5223_; size_t v_i_boxed_5224_; size_t v_stop_boxed_5225_; lean_object* v_res_5226_; 
v_reconfigure_boxed_5223_ = lean_unbox(v_reconfigure_5216_);
v_i_boxed_5224_ = lean_unbox_usize(v_i_5218_);
lean_dec(v_i_5218_);
v_stop_boxed_5225_ = lean_unbox_usize(v_stop_5219_);
lean_dec(v_stop_5219_);
v_res_5226_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5211_, v_pkg_5212_, v___y_5213_, v___y_5214_, v_leanOpts_5215_, v_reconfigure_boxed_5223_, v_as_5217_, v_i_boxed_5224_, v_stop_boxed_5225_, v_b_5220_, v___y_5221_);
lean_dec_ref(v___y_5221_);
lean_dec_ref(v_as_5217_);
lean_dec(v___y_5213_);
lean_dec(v_start_5211_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v_leanOpts_5229_, uint8_t v_reconfigure_5230_, lean_object* v_ws_5231_, lean_object* v_i_5232_, lean_object* v_next_5233_, lean_object* v___y_5234_){
_start:
{
lean_object* v_packages_5236_; lean_object* v_pkg_5237_; lean_object* v_ws_5239_; lean_object* v_depIdxs_5240_; lean_object* v___y_5241_; lean_object* v_____x_5251_; lean_object* v___y_5252_; lean_object* v_depConfigs_5255_; lean_object* v_start_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v_s_5259_; lean_object* v___x_5260_; uint8_t v___x_5261_; 
v_packages_5236_ = lean_ctor_get(v_ws_5231_, 4);
v_pkg_5237_ = lean_array_fget(v_packages_5236_, v_i_5232_);
lean_dec(v_i_5232_);
v_depConfigs_5255_ = lean_ctor_get(v_pkg_5237_, 12);
v_start_5256_ = lean_array_get_size(v_packages_5236_);
v___x_5257_ = lean_array_get_size(v_depConfigs_5255_);
v___x_5258_ = lean_mk_empty_array_with_capacity(v___x_5257_);
lean_inc_ref(v___x_5258_);
lean_inc_ref(v_ws_5231_);
v_s_5259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5259_, 0, v_ws_5231_);
lean_ctor_set(v_s_5259_, 1, v___x_5258_);
v___x_5260_ = lean_unsigned_to_nat(0u);
v___x_5261_ = lean_nat_dec_le(v___x_5257_, v___x_5257_);
if (v___x_5261_ == 0)
{
uint8_t v___x_5262_; 
v___x_5262_ = lean_nat_dec_lt(v___x_5260_, v___x_5257_);
if (v___x_5262_ == 0)
{
lean_object* v_ws_5263_; lean_object* v_packages_5264_; lean_object* v___x_5265_; uint8_t v___x_5266_; 
lean_dec_ref_known(v_s_5259_, 2);
v_ws_5263_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5231_, v_pkg_5237_, v___x_5258_);
v_packages_5264_ = lean_ctor_get(v_ws_5263_, 4);
v___x_5265_ = lean_array_get_size(v_packages_5264_);
v___x_5266_ = lean_nat_dec_lt(v_next_5233_, v___x_5265_);
if (v___x_5266_ == 0)
{
lean_object* v___x_5267_; 
lean_dec(v_next_5233_);
lean_dec_ref(v_leanOpts_5229_);
lean_dec_ref(v___y_5228_);
v___x_5267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5267_, 0, v_ws_5263_);
return v___x_5267_;
}
else
{
lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5268_ = lean_unsigned_to_nat(1u);
v___x_5269_ = lean_nat_add(v_next_5233_, v___x_5268_);
v_ws_5231_ = v_ws_5263_;
v_i_5232_ = v_next_5233_;
v_next_5233_ = v___x_5269_;
goto _start;
}
}
else
{
size_t v___x_5271_; size_t v___x_5272_; lean_object* v___x_5273_; 
lean_dec_ref(v___x_5258_);
lean_dec_ref(v_ws_5231_);
v___x_5271_ = lean_usize_of_nat(v___x_5257_);
v___x_5272_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5229_);
lean_inc_ref(v___y_5228_);
lean_inc(v_pkg_5237_);
v___x_5273_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5256_, v_pkg_5237_, v___y_5227_, v___y_5228_, v_leanOpts_5229_, v_reconfigure_5230_, v_depConfigs_5255_, v___x_5271_, v___x_5272_, v_s_5259_, v___y_5234_);
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v_a_5274_; 
v_a_5274_ = lean_ctor_get(v___x_5273_, 0);
lean_inc(v_a_5274_);
lean_dec_ref_known(v___x_5273_, 1);
v_____x_5251_ = v_a_5274_;
v___y_5252_ = v___y_5234_;
goto v___jp_5250_;
}
else
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5282_; 
lean_dec(v_pkg_5237_);
lean_dec(v_next_5233_);
lean_dec_ref(v_leanOpts_5229_);
lean_dec_ref(v___y_5228_);
v_a_5275_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5277_ = v___x_5273_;
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___x_5273_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5280_; 
if (v_isShared_5278_ == 0)
{
v___x_5280_ = v___x_5277_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_a_5275_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
}
}
}
else
{
uint8_t v___x_5283_; 
v___x_5283_ = lean_nat_dec_lt(v___x_5260_, v___x_5257_);
if (v___x_5283_ == 0)
{
lean_dec_ref_known(v_s_5259_, 2);
v_ws_5239_ = v_ws_5231_;
v_depIdxs_5240_ = v___x_5258_;
v___y_5241_ = v___y_5234_;
goto v___jp_5238_;
}
else
{
size_t v___x_5284_; size_t v___x_5285_; lean_object* v___x_5286_; 
lean_dec_ref(v___x_5258_);
lean_dec_ref(v_ws_5231_);
v___x_5284_ = lean_usize_of_nat(v___x_5257_);
v___x_5285_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5229_);
lean_inc_ref(v___y_5228_);
lean_inc(v_pkg_5237_);
v___x_5286_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5256_, v_pkg_5237_, v___y_5227_, v___y_5228_, v_leanOpts_5229_, v_reconfigure_5230_, v_depConfigs_5255_, v___x_5284_, v___x_5285_, v_s_5259_, v___y_5234_);
if (lean_obj_tag(v___x_5286_) == 0)
{
lean_object* v_a_5287_; 
v_a_5287_ = lean_ctor_get(v___x_5286_, 0);
lean_inc(v_a_5287_);
lean_dec_ref_known(v___x_5286_, 1);
v_____x_5251_ = v_a_5287_;
v___y_5252_ = v___y_5234_;
goto v___jp_5250_;
}
else
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5295_; 
lean_dec(v_pkg_5237_);
lean_dec(v_next_5233_);
lean_dec_ref(v_leanOpts_5229_);
lean_dec_ref(v___y_5228_);
v_a_5288_ = lean_ctor_get(v___x_5286_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___x_5286_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5290_ = v___x_5286_;
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5286_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5293_; 
if (v_isShared_5291_ == 0)
{
v___x_5293_ = v___x_5290_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_a_5288_);
v___x_5293_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
return v___x_5293_;
}
}
}
}
}
v___jp_5238_:
{
lean_object* v_ws_5242_; lean_object* v_packages_5243_; lean_object* v___x_5244_; uint8_t v___x_5245_; 
v_ws_5242_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5239_, v_pkg_5237_, v_depIdxs_5240_);
v_packages_5243_ = lean_ctor_get(v_ws_5242_, 4);
v___x_5244_ = lean_array_get_size(v_packages_5243_);
v___x_5245_ = lean_nat_dec_lt(v_next_5233_, v___x_5244_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; 
lean_dec(v_next_5233_);
lean_dec_ref(v_leanOpts_5229_);
lean_dec_ref(v___y_5228_);
v___x_5246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5246_, 0, v_ws_5242_);
return v___x_5246_;
}
else
{
lean_object* v___x_5247_; lean_object* v___x_5248_; 
v___x_5247_ = lean_unsigned_to_nat(1u);
v___x_5248_ = lean_nat_add(v_next_5233_, v___x_5247_);
v_ws_5231_ = v_ws_5242_;
v_i_5232_ = v_next_5233_;
v_next_5233_ = v___x_5248_;
v___y_5234_ = v___y_5241_;
goto _start;
}
}
v___jp_5250_:
{
lean_object* v_ws_5253_; lean_object* v_depIdxs_5254_; 
v_ws_5253_ = lean_ctor_get(v_____x_5251_, 0);
lean_inc_ref(v_ws_5253_);
v_depIdxs_5254_ = lean_ctor_get(v_____x_5251_, 1);
lean_inc_ref(v_depIdxs_5254_);
lean_dec_ref(v_____x_5251_);
v_ws_5239_ = v_ws_5253_;
v_depIdxs_5240_ = v_depIdxs_5254_;
v___y_5241_ = v___y_5252_;
goto v___jp_5238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v_leanOpts_5298_, lean_object* v_reconfigure_5299_, lean_object* v_ws_5300_, lean_object* v_i_5301_, lean_object* v_next_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_){
_start:
{
uint8_t v_reconfigure_boxed_5305_; lean_object* v_res_5306_; 
v_reconfigure_boxed_5305_ = lean_unbox(v_reconfigure_5299_);
v_res_5306_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5296_, v___y_5297_, v_leanOpts_5298_, v_reconfigure_boxed_5305_, v_ws_5300_, v_i_5301_, v_next_5302_, v___y_5303_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5296_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(lean_object* v_as_5307_, size_t v_i_5308_, size_t v_stop_5309_, lean_object* v_b_5310_){
_start:
{
uint8_t v___x_5311_; 
v___x_5311_ = lean_usize_dec_eq(v_i_5308_, v_stop_5309_);
if (v___x_5311_ == 0)
{
lean_object* v___x_5312_; lean_object* v_name_5313_; lean_object* v___x_5314_; size_t v___x_5315_; size_t v___x_5316_; 
v___x_5312_ = lean_array_uget_borrowed(v_as_5307_, v_i_5308_);
v_name_5313_ = lean_ctor_get(v___x_5312_, 0);
lean_inc(v___x_5312_);
lean_inc(v_name_5313_);
v___x_5314_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5313_, v___x_5312_, v_b_5310_);
v___x_5315_ = ((size_t)1ULL);
v___x_5316_ = lean_usize_add(v_i_5308_, v___x_5315_);
v_i_5308_ = v___x_5316_;
v_b_5310_ = v___x_5314_;
goto _start;
}
else
{
return v_b_5310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2___boxed(lean_object* v_as_5318_, lean_object* v_i_5319_, lean_object* v_stop_5320_, lean_object* v_b_5321_){
_start:
{
size_t v_i_boxed_5322_; size_t v_stop_boxed_5323_; lean_object* v_res_5324_; 
v_i_boxed_5322_ = lean_unbox_usize(v_i_5319_);
lean_dec(v_i_5319_);
v_stop_boxed_5323_ = lean_unbox_usize(v_stop_5320_);
lean_dec(v_stop_5320_);
v_res_5324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5318_, v_i_boxed_5322_, v_stop_boxed_5323_, v_b_5321_);
lean_dec_ref(v_as_5318_);
return v_res_5324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5325_, size_t v_i_5326_, size_t v_stop_5327_, lean_object* v_b_5328_){
_start:
{
uint8_t v___x_5329_; 
v___x_5329_ = lean_usize_dec_eq(v_i_5326_, v_stop_5327_);
if (v___x_5329_ == 0)
{
lean_object* v___x_5330_; lean_object* v_name_5331_; lean_object* v___x_5332_; size_t v___x_5333_; size_t v___x_5334_; lean_object* v___x_5335_; 
v___x_5330_ = lean_array_uget_borrowed(v_as_5325_, v_i_5326_);
v_name_5331_ = lean_ctor_get(v___x_5330_, 0);
lean_inc(v___x_5330_);
lean_inc(v_name_5331_);
v___x_5332_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5331_, v___x_5330_, v_b_5328_);
v___x_5333_ = ((size_t)1ULL);
v___x_5334_ = lean_usize_add(v_i_5326_, v___x_5333_);
v___x_5335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5325_, v___x_5334_, v_stop_5327_, v___x_5332_);
return v___x_5335_;
}
else
{
return v_b_5328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5336_, lean_object* v_i_5337_, lean_object* v_stop_5338_, lean_object* v_b_5339_){
_start:
{
size_t v_i_boxed_5340_; size_t v_stop_boxed_5341_; lean_object* v_res_5342_; 
v_i_boxed_5340_ = lean_unbox_usize(v_i_5337_);
lean_dec(v_i_5337_);
v_stop_boxed_5341_ = lean_unbox_usize(v_stop_5338_);
lean_dec(v_stop_5338_);
v_res_5342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5336_, v_i_boxed_5340_, v_stop_boxed_5341_, v_b_5339_);
lean_dec_ref(v_as_5336_);
return v_res_5342_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5352_, lean_object* v_manifest_5353_, lean_object* v_leanOpts_5354_, uint8_t v_reconfigure_5355_, lean_object* v_overrides_5356_, lean_object* v_a_5357_){
_start:
{
lean_object* v___y_5360_; lean_object* v___y_5361_; lean_object* v___y_5362_; lean_object* v___y_5363_; lean_object* v___y_5364_; lean_object* v___y_5377_; lean_object* v___y_5378_; lean_object* v___y_5379_; lean_object* v___y_5380_; lean_object* v___y_5381_; lean_object* v___y_5382_; lean_object* v___y_5383_; lean_object* v___y_5391_; lean_object* v___y_5392_; lean_object* v___y_5393_; lean_object* v___y_5394_; lean_object* v___y_5395_; lean_object* v___y_5396_; lean_object* v___y_5397_; lean_object* v___y_5404_; lean_object* v___y_5405_; lean_object* v___y_5406_; lean_object* v___y_5407_; lean_object* v_packagesDir_x3f_5446_; lean_object* v_packages_5447_; lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5459_; lean_object* v___x_5467_; lean_object* v___x_5468_; uint8_t v___x_5469_; 
v_packagesDir_x3f_5446_ = lean_ctor_get(v_manifest_5353_, 2);
lean_inc(v_packagesDir_x3f_5446_);
v_packages_5447_ = lean_ctor_get(v_manifest_5353_, 3);
lean_inc_ref(v_packages_5447_);
lean_dec_ref(v_manifest_5353_);
v___x_5467_ = lean_array_get_size(v_packages_5447_);
v___x_5468_ = lean_unsigned_to_nat(0u);
v___x_5469_ = lean_nat_dec_eq(v___x_5467_, v___x_5468_);
if (v___x_5469_ == 0)
{
lean_object* v_packages_5470_; lean_object* v___x_5471_; lean_object* v_config_5472_; lean_object* v_toWorkspaceConfig_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; uint8_t v___x_5477_; 
v_packages_5470_ = lean_ctor_get(v_ws_5352_, 4);
v___x_5471_ = lean_array_fget_borrowed(v_packages_5470_, v___x_5468_);
v_config_5472_ = lean_ctor_get(v___x_5471_, 6);
v_toWorkspaceConfig_5473_ = lean_ctor_get(v_config_5472_, 0);
lean_inc_ref(v_toWorkspaceConfig_5473_);
v___x_5474_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5473_);
v___x_5475_ = l_Lake_mkRelPathString(v___x_5474_);
v___x_5476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5476_, 0, v___x_5475_);
v___x_5477_ = l_instBEqOption_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5446_, v___x_5476_);
lean_dec_ref_known(v___x_5476_, 1);
if (v___x_5477_ == 0)
{
lean_object* v___x_5478_; lean_object* v___x_5479_; 
v___x_5478_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5357_);
v___x_5479_ = lean_apply_2(v_a_5357_, v___x_5478_, lean_box(0));
v___y_5459_ = v_a_5357_;
goto v___jp_5458_;
}
else
{
v___y_5459_ = v_a_5357_;
goto v___jp_5458_;
}
}
else
{
v___y_5459_ = v_a_5357_;
goto v___jp_5458_;
}
v___jp_5359_:
{
lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5365_ = lean_array_get_size(v___y_5360_);
lean_dec_ref(v___y_5360_);
v___x_5366_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5363_, v___y_5364_, v_leanOpts_5354_, v_reconfigure_5355_, v_ws_5352_, v___y_5361_, v___x_5365_, v___y_5362_);
lean_dec(v___y_5363_);
if (lean_obj_tag(v___x_5366_) == 0)
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5375_; 
v_a_5367_ = lean_ctor_get(v___x_5366_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___x_5366_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5369_ = v___x_5366_;
v_isShared_5370_ = v_isSharedCheck_5375_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5366_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5375_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5371_; lean_object* v___x_5373_; 
v___x_5371_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_a_5367_);
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 0, v___x_5371_);
v___x_5373_ = v___x_5369_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v___x_5371_);
v___x_5373_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
return v___x_5373_;
}
}
}
else
{
return v___x_5366_;
}
}
v___jp_5376_:
{
if (lean_obj_tag(v___y_5383_) == 0)
{
lean_dec_ref(v___y_5378_);
v___y_5360_ = v___y_5377_;
v___y_5361_ = v___y_5379_;
v___y_5362_ = v___y_5380_;
v___y_5363_ = v___y_5383_;
v___y_5364_ = v___y_5381_;
goto v___jp_5359_;
}
else
{
lean_object* v___x_5384_; uint8_t v___x_5385_; 
v___x_5384_ = lean_array_get_size(v___y_5378_);
lean_dec_ref(v___y_5378_);
v___x_5385_ = lean_nat_dec_eq(v___x_5384_, v___y_5382_);
if (v___x_5385_ == 0)
{
lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; 
lean_dec_ref(v___y_5381_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5377_);
lean_dec_ref(v_leanOpts_5354_);
lean_dec_ref(v_ws_5352_);
v___x_5386_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5380_);
v___x_5387_ = lean_apply_2(v___y_5380_, v___x_5386_, lean_box(0));
v___x_5388_ = lean_box(0);
v___x_5389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5389_, 0, v___x_5388_);
return v___x_5389_;
}
else
{
v___y_5360_ = v___y_5377_;
v___y_5361_ = v___y_5379_;
v___y_5362_ = v___y_5380_;
v___y_5363_ = v___y_5383_;
v___y_5364_ = v___y_5381_;
goto v___jp_5359_;
}
}
}
v___jp_5390_:
{
lean_object* v___x_5398_; uint8_t v___x_5399_; 
v___x_5398_ = lean_array_get_size(v_overrides_5356_);
v___x_5399_ = lean_nat_dec_lt(v___y_5396_, v___x_5398_);
if (v___x_5399_ == 0)
{
v___y_5377_ = v___y_5391_;
v___y_5378_ = v___y_5392_;
v___y_5379_ = v___y_5393_;
v___y_5380_ = v___y_5394_;
v___y_5381_ = v___y_5395_;
v___y_5382_ = v___y_5396_;
v___y_5383_ = v___y_5397_;
goto v___jp_5376_;
}
else
{
size_t v___x_5400_; size_t v___x_5401_; lean_object* v___x_5402_; 
v___x_5400_ = ((size_t)0ULL);
v___x_5401_ = lean_usize_of_nat(v___x_5398_);
v___x_5402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5356_, v___x_5400_, v___x_5401_, v___y_5397_);
v___y_5377_ = v___y_5391_;
v___y_5378_ = v___y_5392_;
v___y_5379_ = v___y_5393_;
v___y_5380_ = v___y_5394_;
v___y_5381_ = v___y_5395_;
v___y_5382_ = v___y_5396_;
v___y_5383_ = v___x_5402_;
goto v___jp_5376_;
}
}
v___jp_5403_:
{
lean_object* v_packages_5408_; lean_object* v___x_5409_; lean_object* v_wsIdx_5410_; lean_object* v_dir_5411_; lean_object* v_depConfigs_5412_; lean_object* v___x_5413_; 
v_packages_5408_ = lean_ctor_get(v_ws_5352_, 4);
v___x_5409_ = lean_array_fget_borrowed(v_packages_5408_, v___y_5406_);
v_wsIdx_5410_ = lean_ctor_get(v___x_5409_, 0);
v_dir_5411_ = lean_ctor_get(v___x_5409_, 4);
v_depConfigs_5412_ = lean_ctor_get(v___x_5409_, 12);
v___x_5413_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5407_, v_depConfigs_5412_, v___y_5404_);
if (lean_obj_tag(v___x_5413_) == 0)
{
lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; 
lean_dec_ref_known(v___x_5413_, 1);
v___x_5414_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5411_);
v___x_5415_ = l_Lake_joinRelative(v_dir_5411_, v___x_5414_);
v___x_5416_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5417_ = l_Lake_joinRelative(v___x_5415_, v___x_5416_);
v___x_5418_ = l_Lake_Manifest_tryLoadEntries(v___x_5417_);
if (lean_obj_tag(v___x_5418_) == 0)
{
lean_object* v_a_5419_; lean_object* v___x_5420_; uint8_t v___x_5421_; 
v_a_5419_ = lean_ctor_get(v___x_5418_, 0);
lean_inc(v_a_5419_);
lean_dec_ref_known(v___x_5418_, 1);
v___x_5420_ = lean_array_get_size(v_a_5419_);
v___x_5421_ = lean_nat_dec_lt(v___y_5406_, v___x_5420_);
if (v___x_5421_ == 0)
{
lean_dec(v_a_5419_);
lean_inc(v_wsIdx_5410_);
lean_inc_ref(v_depConfigs_5412_);
lean_inc_ref(v_packages_5408_);
v___y_5391_ = v_packages_5408_;
v___y_5392_ = v_depConfigs_5412_;
v___y_5393_ = v_wsIdx_5410_;
v___y_5394_ = v___y_5404_;
v___y_5395_ = v___y_5405_;
v___y_5396_ = v___y_5406_;
v___y_5397_ = v___y_5407_;
goto v___jp_5390_;
}
else
{
size_t v___x_5422_; size_t v___x_5423_; lean_object* v___x_5424_; 
v___x_5422_ = ((size_t)0ULL);
v___x_5423_ = lean_usize_of_nat(v___x_5420_);
v___x_5424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5419_, v___x_5422_, v___x_5423_, v___y_5407_);
lean_dec(v_a_5419_);
lean_inc(v_wsIdx_5410_);
lean_inc_ref(v_depConfigs_5412_);
lean_inc_ref(v_packages_5408_);
v___y_5391_ = v_packages_5408_;
v___y_5392_ = v_depConfigs_5412_;
v___y_5393_ = v_wsIdx_5410_;
v___y_5394_ = v___y_5404_;
v___y_5395_ = v___y_5405_;
v___y_5396_ = v___y_5406_;
v___y_5397_ = v___x_5424_;
goto v___jp_5390_;
}
}
else
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5437_; 
lean_dec(v___y_5407_);
lean_dec_ref(v___y_5405_);
lean_dec_ref(v_leanOpts_5354_);
lean_dec_ref(v_ws_5352_);
v_a_5425_ = lean_ctor_get(v___x_5418_, 0);
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5418_);
if (v_isSharedCheck_5437_ == 0)
{
v___x_5427_ = v___x_5418_;
v_isShared_5428_ = v_isSharedCheck_5437_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v___x_5418_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5437_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v___x_5429_; uint8_t v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5435_; 
v___x_5429_ = lean_io_error_to_string(v_a_5425_);
v___x_5430_ = 3;
v___x_5431_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5431_, 0, v___x_5429_);
lean_ctor_set_uint8(v___x_5431_, sizeof(void*)*1, v___x_5430_);
lean_inc_ref(v___y_5404_);
v___x_5432_ = lean_apply_2(v___y_5404_, v___x_5431_, lean_box(0));
v___x_5433_ = lean_box(0);
if (v_isShared_5428_ == 0)
{
lean_ctor_set(v___x_5427_, 0, v___x_5433_);
v___x_5435_ = v___x_5427_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v___x_5433_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
return v___x_5435_;
}
}
}
}
else
{
lean_object* v_a_5438_; lean_object* v___x_5440_; uint8_t v_isShared_5441_; uint8_t v_isSharedCheck_5445_; 
lean_dec(v___y_5407_);
lean_dec_ref(v___y_5405_);
lean_dec_ref(v_leanOpts_5354_);
lean_dec_ref(v_ws_5352_);
v_a_5438_ = lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5445_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5445_ == 0)
{
v___x_5440_ = v___x_5413_;
v_isShared_5441_ = v_isSharedCheck_5445_;
goto v_resetjp_5439_;
}
else
{
lean_inc(v_a_5438_);
lean_dec(v___x_5413_);
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
v___jp_5448_:
{
lean_object* v_pkgEntries_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; uint8_t v___x_5454_; 
v_pkgEntries_5451_ = lean_box(1);
v___x_5452_ = lean_unsigned_to_nat(0u);
v___x_5453_ = lean_array_get_size(v_packages_5447_);
v___x_5454_ = lean_nat_dec_lt(v___x_5452_, v___x_5453_);
if (v___x_5454_ == 0)
{
lean_dec_ref(v_packages_5447_);
v___y_5404_ = v___y_5449_;
v___y_5405_ = v___y_5450_;
v___y_5406_ = v___x_5452_;
v___y_5407_ = v_pkgEntries_5451_;
goto v___jp_5403_;
}
else
{
size_t v___x_5455_; size_t v___x_5456_; lean_object* v___x_5457_; 
v___x_5455_ = ((size_t)0ULL);
v___x_5456_ = lean_usize_of_nat(v___x_5453_);
v___x_5457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5447_, v___x_5455_, v___x_5456_, v_pkgEntries_5451_);
lean_dec_ref(v_packages_5447_);
v___y_5404_ = v___y_5449_;
v___y_5405_ = v___y_5450_;
v___y_5406_ = v___x_5452_;
v___y_5407_ = v___x_5457_;
goto v___jp_5403_;
}
}
v___jp_5458_:
{
if (lean_obj_tag(v_packagesDir_x3f_5446_) == 0)
{
lean_object* v_packages_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v_config_5463_; lean_object* v_toWorkspaceConfig_5464_; lean_object* v___x_5465_; 
v_packages_5460_ = lean_ctor_get(v_ws_5352_, 4);
v___x_5461_ = lean_unsigned_to_nat(0u);
v___x_5462_ = lean_array_fget_borrowed(v_packages_5460_, v___x_5461_);
v_config_5463_ = lean_ctor_get(v___x_5462_, 6);
v_toWorkspaceConfig_5464_ = lean_ctor_get(v_config_5463_, 0);
lean_inc_ref(v_toWorkspaceConfig_5464_);
v___x_5465_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5464_);
v___y_5449_ = v___y_5459_;
v___y_5450_ = v___x_5465_;
goto v___jp_5448_;
}
else
{
lean_object* v_val_5466_; 
v_val_5466_ = lean_ctor_get(v_packagesDir_x3f_5446_, 0);
lean_inc(v_val_5466_);
lean_dec_ref_known(v_packagesDir_x3f_5446_, 1);
v___y_5449_ = v___y_5459_;
v___y_5450_ = v_val_5466_;
goto v___jp_5448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5480_, lean_object* v_manifest_5481_, lean_object* v_leanOpts_5482_, lean_object* v_reconfigure_5483_, lean_object* v_overrides_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_){
_start:
{
uint8_t v_reconfigure_boxed_5487_; lean_object* v_res_5488_; 
v_reconfigure_boxed_5487_ = lean_unbox(v_reconfigure_5483_);
v_res_5488_ = l_Lake_Workspace_materializeDeps(v_ws_5480_, v_manifest_5481_, v_leanOpts_5482_, v_reconfigure_boxed_5487_, v_overrides_5484_, v_a_5485_);
lean_dec_ref(v_a_5485_);
lean_dec_ref(v_overrides_5484_);
return v_res_5488_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v_leanOpts_5491_, uint8_t v_reconfigure_5492_, lean_object* v_ws_5493_, lean_object* v_i_5494_, lean_object* v_i__lt_5495_, lean_object* v_next_5496_, lean_object* v_lt__next_5497_, lean_object* v___y_5498_){
_start:
{
lean_object* v___x_5500_; 
v___x_5500_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5489_, v___y_5490_, v_leanOpts_5491_, v_reconfigure_5492_, v_ws_5493_, v_i_5494_, v_next_5496_, v___y_5498_);
return v___x_5500_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v_leanOpts_5503_, lean_object* v_reconfigure_5504_, lean_object* v_ws_5505_, lean_object* v_i_5506_, lean_object* v_i__lt_5507_, lean_object* v_next_5508_, lean_object* v_lt__next_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_){
_start:
{
uint8_t v_reconfigure_boxed_5512_; lean_object* v_res_5513_; 
v_reconfigure_boxed_5512_ = lean_unbox(v_reconfigure_5504_);
v_res_5513_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5501_, v___y_5502_, v_leanOpts_5503_, v_reconfigure_boxed_5512_, v_ws_5505_, v_i_5506_, v_i__lt_5507_, v_next_5508_, v_lt__next_5509_, v___y_5510_);
lean_dec_ref(v___y_5510_);
lean_dec(v___y_5501_);
return v_res_5513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(lean_object* v_start_5514_, lean_object* v_pkg_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v_leanOpts_5518_, uint8_t v_reconfigure_5519_, lean_object* v_as_5520_, size_t v_i_5521_, size_t v_stop_5522_, lean_object* v_b_5523_, lean_object* v___y_5524_){
_start:
{
lean_object* v___x_5526_; 
v___x_5526_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5515_, v___y_5516_, v___y_5517_, v_leanOpts_5518_, v_reconfigure_5519_, v_as_5520_, v_i_5521_, v_stop_5522_, v_b_5523_, v___y_5524_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_start_5527_, lean_object* v_pkg_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v_leanOpts_5531_, lean_object* v_reconfigure_5532_, lean_object* v_as_5533_, lean_object* v_i_5534_, lean_object* v_stop_5535_, lean_object* v_b_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_){
_start:
{
uint8_t v_reconfigure_boxed_5539_; size_t v_i_boxed_5540_; size_t v_stop_boxed_5541_; lean_object* v_res_5542_; 
v_reconfigure_boxed_5539_ = lean_unbox(v_reconfigure_5532_);
v_i_boxed_5540_ = lean_unbox_usize(v_i_5534_);
lean_dec(v_i_5534_);
v_stop_boxed_5541_ = lean_unbox_usize(v_stop_5535_);
lean_dec(v_stop_5535_);
v_res_5542_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(v_start_5527_, v_pkg_5528_, v___y_5529_, v___y_5530_, v_leanOpts_5531_, v_reconfigure_boxed_5539_, v_as_5533_, v_i_boxed_5540_, v_stop_boxed_5541_, v_b_5536_, v___y_5537_);
lean_dec_ref(v___y_5537_);
lean_dec_ref(v_as_5533_);
lean_dec(v___y_5529_);
lean_dec(v_start_5527_);
return v_res_5542_;
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
